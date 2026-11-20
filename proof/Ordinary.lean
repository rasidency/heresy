import Runtime
import Execution

set_option warningAsError true

namespace Heresy.Ordinary

inductive TypeCode where
  | pointer | byte | signedByte | integer | unsignedInt | size
  | bitField (shift widthMinusOne : Nat) (isSigned : Bool)
  deriving DecidableEq, Repr

def TypeCode.haskell : TypeCode → String
  | .pointer => "PointerType"
  | .byte => "(IntegerType 8 False)"
  | .signedByte => "(IntegerType 8 True)"
  | .integer => "(IntegerType 32 True)"
  | .unsignedInt => "(IntegerType 32 False)"
  | .size => "(IntegerType 64 False)"
  | .bitField shift width signed =>
    "(BitField " ++ toString shift ++ " " ++ toString (width + 1) ++ (if signed then " True)" else " False)")

def TypeCode.width : TypeCode → Nat
  | .pointer | .size => 8
  | .byte | .signedByte => 1
  | .integer | .unsignedInt => 4
  | .bitField shift width _ => bitfield_bytes shift (width + 1)

def TypeCode.signed : TypeCode → Bool
  | .integer | .signedByte => true
  | .bitField _ _ signed => signed
  | _ => false

private theorem TypeCode.width_positive (ty : TypeCode) : 0 < ty.width := by
  cases ty <;> first | decide | simp only [TypeCode.width, bitfield_bytes]; omega

def TypeCode.bit_width : TypeCode → Nat
  | .bitField _ width _ => width + 1
  | ty => 8 * ty.width

def TypeCode.bit_shift : TypeCode → Nat
  | .bitField shift _ _ => shift
  | _ => 0

structure FieldSpec where
  identity : String
  name : String
  spelling : String
  ty : TypeCode
  bits : Option Nat := none
  deriving Repr

structure Field where
  spec : FieldSpec
  offset : Nat
  shift : Nat := 0
  deriving Repr

def Field.access (field : Field) : TypeCode :=
  match field.spec.bits with
  | none => field.spec.ty
  | some width => .bitField field.shift width field.spec.ty.signed

private def FieldSpec.span (field : FieldSpec) : Nat :=
  (field.bits.map (· + 1)).getD (8 * field.ty.width)

private def Field.start_bit (field : Field) : Nat := 8 * field.offset + field.shift

private def place_fields (cursor : Nat) : List FieldSpec → List Field × Nat
  | [] => ([], cursor)
  | field :: fields =>
    let offset := (aligned_slot cursor 0 field.ty.width).1
    let (placed, extent) := place_fields (offset + field.ty.width) fields
    (⟨field, offset, 0⟩ :: placed, extent)

private theorem placed_fields_valid (cursor : Nat) (fields : List FieldSpec) :
    let (placed, extent) := place_fields cursor fields
    cursor ≤ extent ∧ ∀ member ∈ placed, cursor ≤ member.offset ∧
      member.offset % member.spec.ty.width = 0 ∧ member.offset + member.spec.ty.width ≤ extent := by
  induction fields generalizing cursor with
  | nil => simp [place_fields]
  | cons field rest later =>
    let offset := (aligned_slot cursor 0 field.ty.width).1
    obtain ⟨after, _, aligned, _⟩ := aligned_slot_valid cursor 0 field.ty.width field.ty.width_positive
    obtain ⟨extent, members⟩ := later (offset + field.ty.width)
    refine ⟨Nat.le_trans after (Nat.le_trans (Nat.le_add_right _ _) extent), ?_⟩
    intro member present
    cases List.mem_cons.mp present with
    | inl same => subst member; exact ⟨after, aligned, extent⟩
    | inr tail =>
      obtain ⟨ordered, boundary, contained⟩ := members member tail
      exact ⟨Nat.le_trans after (Nat.le_trans (Nat.le_add_right _ _) ordered), boundary, contained⟩

structure RecordLayout where
  spelling : String
  fields : List Field
  width : Nat
  alignment : Nat
  isUnion : Bool := false
  deriving Repr

private def record_alignment (fields : List FieldSpec) : Nat :=
  max 1 ((fields.map fun field => field.ty.width).foldr max 0)

def record_layout (spelling : String) (fields : List FieldSpec) : RecordLayout :=
  let (placed, extent) := place_fields 0 fields
  let alignment := record_alignment fields
  ⟨spelling, placed, (aligned_slot extent 0 alignment).1, alignment, false⟩

def union_layout (spelling : String) (fields : List FieldSpec) : RecordLayout :=
  let alignment := record_alignment fields
  ⟨spelling, fields.map (fun field => ⟨field, 0, 0⟩), alignment, alignment, true⟩

private theorem field_width_le_max (field : FieldSpec) (fields : List FieldSpec) (present : field ∈ fields) :
    field.ty.width ≤ (fields.map fun field => field.ty.width).foldr max 0 := by
  induction fields with
  | nil => simp at present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | later
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

theorem union_member_in_bounds (spelling : String) (fields : List FieldSpec) (field : Field)
    (present : field ∈ (union_layout spelling fields).fields) :
    field.offset = 0 ∧ field.spec.ty.width ≤ (union_layout spelling fields).width := by
  obtain ⟨spec, included, rfl⟩ := List.mem_map.mp present
  exact ⟨rfl, Nat.le_trans (field_width_le_max spec fields included) (Nat.le_max_right _ _)⟩

theorem record_field_in_bounds (spelling : String) (fields : List FieldSpec) (field : Field)
    (present : field ∈ (record_layout spelling fields).fields) :
    field.offset % field.spec.ty.width = 0 ∧ field.offset + field.spec.ty.width ≤ (record_layout spelling fields).width := by
  obtain ⟨_, members⟩ := placed_fields_valid 0 fields
  obtain ⟨_, aligned, extent⟩ := members field present
  have positive : 0 < record_alignment fields := Nat.lt_of_lt_of_le (by decide) (Nat.le_max_left _ _)
  have rounded := (aligned_slot_valid (place_fields 0 fields).2 0 (record_alignment fields) positive).1
  exact ⟨aligned, Nat.le_trans extent rounded⟩

private theorem placed_fields_ordered (cursor : Nat) (fields : List FieldSpec) :
    (place_fields cursor fields).1.Pairwise (fun first later => first.offset + first.spec.ty.width ≤ later.offset) := by
  induction fields generalizing cursor with
  | nil => exact .nil
  | cons field rest ih =>
    let offset := (aligned_slot cursor 0 field.ty.width).1
    let next := offset + field.ty.width
    have tail := (placed_fields_valid next rest).2
    exact .cons (fun member present => (tail member present).1) (ih next)

theorem record_fields_ordered (spelling : String) (fields : List FieldSpec) :
    (record_layout spelling fields).fields.Pairwise (fun first later => first.offset + first.spec.ty.width ≤ later.offset) :=
  placed_fields_ordered 0 fields

private def member_position (cursor : Nat) (member : FieldSpec) : Nat :=
  let unit := 8 * member.ty.width
  if member.bits.isSome && cursor % unit + member.span ≤ unit then cursor
  else (aligned_slot cursor 0 unit).1

private theorem member_position_monotone (cursor : Nat) (member : FieldSpec) : cursor ≤ member_position cursor member := by
  simp only [member_position]
  split
  · exact Nat.le_refl _
  · exact (aligned_slot_valid cursor 0 _ (Nat.mul_pos (by decide) member.ty.width_positive)).1

private def place_bit_fields (cursor : Nat) : List FieldSpec → List Field × Nat
  | [] => ([], cursor)
  | spec :: rest =>
    let position := member_position cursor spec
    let (fields, extent) := place_bit_fields (position + spec.span) rest
    (⟨spec, position / 8, position % 8⟩ :: fields, extent)

private theorem place_bit_fields_valid (cursor : Nat) (fields : List FieldSpec) :
    let (placed, extent) := place_bit_fields cursor fields
    cursor ≤ extent ∧ ∀ field ∈ placed, cursor ≤ field.start_bit ∧ field.start_bit + field.spec.span ≤ extent := by
  induction fields generalizing cursor with
  | nil => simp [place_bit_fields]
  | cons spec rest ih =>
    let start := member_position cursor spec
    have lower := member_position_monotone cursor spec
    obtain ⟨remaining, valid⟩ := ih (start + spec.span)
    refine ⟨Nat.le_trans lower (Nat.le_trans (Nat.le_add_right _ _) remaining), ?_⟩
    intro field present
    rcases List.mem_cons.mp present with same | later
    · subst field
      have equivalent : (⟨spec, start / 8, start % 8⟩ : Field).start_bit = start := by
        simpa [Field.start_bit, Nat.add_comm] using (Nat.mod_add_div start 8)
      exact ⟨equivalent.symm ▸ lower, equivalent.symm ▸ remaining⟩
    · obtain ⟨after, within⟩ := valid field later
      exact ⟨Nat.le_trans lower (Nat.le_trans (Nat.le_add_right _ _) after), within⟩

def bit_record_layout (spelling : String) (fields : List FieldSpec) : RecordLayout :=
  let (placed, extent) := place_bit_fields 0 fields
  let alignment := record_alignment fields
  ⟨spelling, placed, (aligned_slot ((extent + 7) / 8) 0 alignment).1, alignment, false⟩

theorem bit_record_member_in_bounds (spelling : String) (fields : List FieldSpec) (field : Field)
    (present : field ∈ (bit_record_layout spelling fields).fields) :
    field.offset + field.access.width ≤ (bit_record_layout spelling fields).width := by
  let extent := (place_bit_fields 0 fields).2
  let alignment := record_alignment fields
  have fits : field.start_bit + field.spec.span ≤ extent := ((place_bit_fields_valid 0 fields).2 field present).2
  have positive : 0 < alignment := Nat.lt_of_lt_of_le (by decide) (Nat.le_max_left _ _)
  have rounded := (aligned_slot_valid ((extent + 7) / 8) 0 alignment positive).1
  apply Nat.le_trans _ rounded
  cases bits : field.spec.bits with
  | none =>
    simp only [Field.access, Field.start_bit, FieldSpec.span, bits, Option.map_none, Option.getD_none] at fits ⊢
    omega
  | some width =>
    simp only [Field.access, TypeCode.width, Field.start_bit, FieldSpec.span, bits, Option.map_some, Option.getD_some,
      bitfield_bytes] at fits ⊢
    omega

inductive ScalarOp where
  | add | sub | mul | eq | ne | lt | le | gt | ge
  deriving Repr

def ScalarOp.symbol : ScalarOp → String
  | .add => "+" | .sub => "-" | .mul => "*"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

inductive Expression where
  | literal (value : Int)
  | nullPointer
  | slotAddress (slot : Nat)
  | globalAddress (name : String)
  | load (ty : TypeCode) (address : Expression)
  | cast (ty : TypeCode) (operand : Expression)
  | offset (base index : Expression) (stride : Nat := 1)
  | field (base : Expression) (offset : Nat)
  | logicalNot (operand : Expression)
  | logic (conjunction : Bool) (left right : Expression)
  | pointerCompare (equality : Bool) (left right : Expression)
  | allocate (size : Expression)
  | move (destination source size : Expression)
  | copyRecord (destination source : Expression) (width alignment : Nat)
  | put (value : Expression)
  | release (address : Expression)
  | exit (status : Expression)
  | assign (ty : TypeCode) (address value : Expression)
  | scalar (op : ScalarOp) (ty : TypeCode) (left right : Expression)
  | call (name : String) (ty : TypeCode) (arguments : Expression)
  | emptyArguments
  | argument (ty : TypeCode) (value rest : Expression)
  deriving Repr

structure Initialiser where
  offset : Option Nat
  ty : TypeCode
  value : Expression
  deriving Repr

private def Initialiser.start_bit (init : Initialiser) : Nat := 8 * init.offset.getD 0 + init.ty.bit_shift

inductive LabelChoice where
  | address (identity : String)
  | conditional (test : Expression) (yes no : LabelChoice)
  deriving Repr

def LabelChoice.symbols : LabelChoice → List String
  | .address name => [name]
  | .conditional _ yes no => yes.symbols ++ no.symbols

def Initialiser.fits (width : Nat) (stores : List Initialiser) : Bool :=
  stores.all (fun init => decide (init.offset.getD 0 + init.ty.width ≤ width)) &&
    decide (stores.Pairwise (fun first later => first.start_bit + first.ty.bit_width ≤ later.start_bit))

inductive Statement where
  | empty
  | sequence (first rest : Statement)
  | block (body : Statement)
  | skip
  | initialise (slot : Nat) (ty : TypeCode) (value : Expression)
  | initialiseAggregate (slot width : Nat) (stores : List Initialiser)
  | initialiseCopy (slot : Nat) (source : Expression) (width alignment : Nat)
  | discard (value : Expression)
  | branch (condition : Expression) (yes no : Statement)
  | whileDo (condition : Expression) (body : Statement)
  | doWhile (body : Statement) (condition : Expression)
  | forDo (initial : Statement) (condition : Option Expression) (body : Statement) (advance : Option Expression)
  | stop
  | restart
  | result (value : Expression)
  | gotoLabel (identity : String)
  | indirect (choice : LabelChoice)
  | label (identity : String) (body : Statement)
  | select (selector : Expression) (body : Statement)
  | caseOf (bounds : Option (Int × Int)) (body : Statement)
  deriving Repr

inductive BlockAction where
  | finish
  | escape (stop : Bool)
  | jump (target : Nat)
  | branch (condition : Expression) (yes no : Nat)
  | select (selector : Expression) (entries : List SwitchEntry)
  | indirect (choice : LabelChoice) (destinations : List (String × Nat))
  | run (statement : Statement) (next : Nat)
  deriving Repr

structure Block where
  action : BlockAction
  redirect : Option (Nat × Nat) := none
  deriving Repr

private def BlockAction.targets : BlockAction → List Nat
  | .finish | .escape _ => []
  | .jump target | .run _ target => [target]
  | .branch _ yes no => [yes, no]
  | .select _ entries => entries.map (·.target)
  | .indirect _ destinations => destinations.map Prod.snd

def Block.targets (block : Block) : List Nat :=
  match block.redirect with
  | none => block.action.targets
  | some (stop, restart) => (stop :: restart :: block.action.targets).mergeSort.eraseDups

structure Dispatch where
  name : String
  entry : Nat
  blocks : List Block
  deriving Repr

def Dispatch.graph (dispatch : Dispatch) : DispatchGraph :=
  ⟨dispatch.entry, dispatch.blocks.map (·.targets)⟩

structure Exits where
  next : Bool := false
  stop : Bool := false
  restart : Bool := false

private def Exits.join (left right : Exits) : Exits :=
  ⟨left.next || right.next, left.stop || right.stop, left.restart || right.restart⟩

private def Exits.sequence (first rest : Exits) : Exits :=
  ⟨first.next && rest.next, first.stop || (first.next && rest.stop), first.restart || (first.next && rest.restart)⟩

def Statement.exits : Statement → Exits
  | .discard (.exit _) => {}
  | .empty | .skip | .initialise .. | .initialiseAggregate .. | .initialiseCopy ..
  | .discard _ | .whileDo .. | .doWhile .. => { next := true }
  | .sequence first rest => first.exits.sequence rest.exits
  | .block body => body.exits
  | .branch _ yes no => yes.exits.join no.exits
  | .forDo initial .. => initial.exits.sequence { next := true }
  | .stop => { stop := true }
  | .restart => { restart := true }
  | .result _ => {}
  | .gotoLabel _ | .indirect _ | .label .. | .select .. | .caseOf .. => {}

private def Block.outgoing (block : Block) : List Nat :=
  match block.action with
  | .run statement next =>
    let exits := statement.exits
    (if exits.next then [next] else []) ++
      (match block.redirect with
        | some (stop, restart) => (if exits.stop then [stop] else []) ++ (if exits.restart then [restart] else [])
        | none => [])
  | action => action.targets

private def Block.exits (block : Block) : Exits :=
  match block.action with
  | .finish => { next := true }
  | .escape true => { stop := true }
  | .escape false => { restart := true }
  | .select _ entries => { next := !(entries.any (·.bounds.isNone)) }
  | .run statement _ =>
    let exits := statement.exits
    { stop := block.redirect.isNone && exits.stop, restart := block.redirect.isNone && exits.restart }
  | _ => {}

private def Dispatch.region (dispatch : Dispatch) : List Nat :=
  let rec visit : Nat → List Nat → Array Bool → List Nat → List Nat
    | 0, _, _, known | _, [], _, known => known
    | fuel + 1, index :: work, seen, known =>
      let targets := (dispatch.blocks[index]?.map Block.outgoing).getD []
      let (work, seen) := targets.foldl (fun (work, seen) target =>
        if seen[target]?.getD true then (work, seen) else (target :: work, seen.set! target true)) (work, seen)
      visit fuel work seen (index :: known)
  let seen := (Array.replicate dispatch.blocks.length false).set! dispatch.entry true
  visit dispatch.blocks.length [dispatch.entry] seen []

private def Exits.allowed (exits : Exits) (allowNext : Bool) : Bool :=
  !exits.stop && !exits.restart && (allowNext || !exits.next)

private def Dispatch.control_checked (dispatch : Dispatch) (allowNext : Bool) : Bool :=
  valid_dispatch dispatch.graph &&
    (let region := dispatch.region
     region.contains dispatch.entry && region.all (fun index => match dispatch.blocks[index]? with
       | none => false
       | some block => block.exits.allowed allowNext && block.outgoing.all region.contains))

def Statement.labels : Statement → List String
  | .sequence first rest | .branch _ first rest | .forDo first _ rest _ => first.labels ++ rest.labels
  | .block body | .whileDo _ body | .doWhile body _ | .select _ body | .caseOf _ body => body.labels
  | .label identity body => identity :: body.labels
  | _ => []

def Statement.needs_dispatch : Statement → Bool
  | .sequence first rest | .branch _ first rest | .forDo first _ rest _ => first.needs_dispatch || rest.needs_dispatch
  | .block body | .whileDo _ body | .doWhile body _ => body.needs_dispatch
  | .label .. | .gotoLabel _ | .indirect _ | .select .. | .caseOf .. => true
  | _ => false

private structure GraphBuilder where
  next : Nat
  blocks : List (Nat × Block) := []
  cases : List (List SwitchEntry) := []

private abbrev BuildGraph := StateT GraphBuilder (Except String)

private def reserve_block : BuildGraph Nat := do
  let state ← get
  set { state with next := state.next + 1 }
  return state.next

private def define_block (index : Nat) (action : BlockAction) (redirect : Option (Nat × Nat)) : BuildGraph Unit :=
  modify fun state => { state with blocks := (index, ⟨action, redirect⟩) :: state.blocks }

private def add_block (action : BlockAction) (redirect : Option (Nat × Nat) := none) : BuildGraph Nat := do
  let index ← reserve_block
  define_block index action redirect
  return index

private def disjoint_cases (left right : SwitchEntry) : Bool :=
  match left.bounds, right.bounds with
  | none, none => false
  | some (lo, hi), some (first, last) => decide (hi < first ∨ last < lo)
  | _, _ => true

private def LabelChoice.resolve (labels : List (String × String)) : LabelChoice → Except String LabelChoice
  | .address identity =>
    match labels.lookup identity with
    | none => .error "ordinary computed goto target is outside its function"
    | some name => .ok (.address name)
  | .conditional test yes no => do
    return .conditional test (← yes.resolve labels) (← no.resolve labels)

private def build_graph (labels : List String) (named : List (String × String)) : Statement → Nat → Nat → Nat → BuildGraph Nat
  | .empty, _, _, next | .skip, _, _, next => pure next
  | .sequence first rest, stop, restart, next => do
    let tail ← build_graph labels named rest stop restart next
    build_graph labels named first stop restart tail
  | .block body, stop, restart, next => build_graph labels named body stop restart next
  | .branch condition yes no, stop, restart, next => do
    let chosen ← build_graph labels named yes stop restart next
    let other ← build_graph labels named no stop restart next
    add_block (.branch condition chosen other) (some (stop, restart))
  | .whileDo condition body, stop, restart, next => do
    let test ← reserve_block
    let first ← build_graph labels named body next test test
    define_block test (.branch condition first next) (some (stop, restart))
    return test
  | .doWhile body condition, stop, restart, next => do
    let test ← reserve_block
    let first ← build_graph labels named body next test test
    define_block test (.branch condition first next) (some (stop, restart))
    return first
  | .forDo initial condition body advance, stop, restart, next => do
    let test ← reserve_block
    let step ← match advance with
      | none => pure test
      | some value => add_block (.run (.discard value) test) (some (stop, restart))
    let first ← build_graph labels named body next step step
    let branch := match condition with
      | none => .jump first
      | some value => BlockAction.branch value first next
    define_block test branch (some (stop, restart))
    build_graph labels named initial stop restart test
  | .stop, stop, _, _ => pure stop
  | .restart, _, restart, _ => pure restart
  | .gotoLabel identity, _, _, _ => do
    let some index := labels.findIdx? (· == identity) | throw "ordinary goto target is outside its function"
    return index
  | .indirect choice, stop, restart, _ => do
    let visible := named.filter (fun label => labels.contains label.1)
    let destinations := labels.zipIdx.filterMap fun (identity, target) =>
      (visible.lookup identity).map (fun name => (name, target))
    let resolved ← choice.resolve visible
    add_block (.indirect resolved destinations) (some (stop, restart))
  | .label identity body, stop, restart, next => do
    let some index := labels.findIdx? (· == identity) | throw "missing ordinary label declaration"
    let first ← build_graph labels named body stop restart next
    define_block index (.jump first) none
    return index
  | .select selector body, stop, restart, next => do
    modify fun state => { state with cases := [] :: state.cases }
    let _ ← build_graph labels named body next restart next
    let state ← get
    let entries :: enclosing := state.cases | throw "missing ordinary switch entries"
    set { state with cases := enclosing }
    unless decide (entries.Pairwise (fun left right => disjoint_cases left right = true)) do
      throw "overlapping ordinary switch entries"
    let entries := if entries.any (·.bounds.isNone) then entries else entries ++ [⟨none, next⟩]
    add_block (.select selector entries) (some (stop, restart))
  | .caseOf bounds body, stop, restart, next => do
    let first ← build_graph labels named body stop restart next
    let state ← get
    let entries :: enclosing := state.cases | throw "ordinary case is outside a switch"
    set { state with cases := (⟨bounds, first⟩ :: entries) :: enclosing }
    return first
  | statement, stop, restart, next => add_block (.run statement next) (some (stop, restart))

def compile_dispatch (name : String) (statement : Statement) (named : List (String × String) := []) : Except String Dispatch := do
  let labels := statement.labels
  unless decide labels.Nodup do throw "duplicate ordinary label identity"
  let compile := do
    let finish ← add_block .finish
    let restart ← add_block (.escape false)
    let stop ← add_block (.escape true)
    build_graph labels named statement stop restart finish
  let (entry, state) ← compile.run { next := labels.length }
  let rows := state.blocks.mergeSort (fun left right => left.1 ≤ right.1)
  unless rows.map Prod.fst == List.range state.next do throw "incomplete ordinary dispatch graph"
  return ⟨name, entry, rows.map Prod.snd⟩

structure Procedure where
  name : String
  resultType : TypeCode
  parameters : List TypeCode
  locals : List Nat
  slots : List String
  statements : Statement
  dispatch : Option Dispatch := none
  deriving Repr

def Procedure.control_checked (procedure : Procedure) : Bool :=
  match procedure.dispatch with
  | none => procedure.statements.exits.allowed (procedure.name == "main")
  | some dispatch => dispatch.control_checked (procedure.name == "main")

theorem Procedure.valid_graph (procedure : Procedure) (checked : procedure.control_checked = true)
    (dispatch : Dispatch) (found : procedure.dispatch = some dispatch) : valid_dispatch dispatch.graph = true := by
  simp only [Procedure.control_checked, found, Dispatch.control_checked, Bool.and_eq_true] at checked
  exact checked.1

structure Global where
  name : String
  width : Nat
  initialisers : List Initialiser
  deriving Repr

def Global.initialisers_fit (object : Global) : Bool :=
  Initialiser.fits object.width object.initialisers

theorem Global.initialiser_in_bounds (object : Global) (checked : object.initialisers_fit = true)
    (init : Initialiser) (present : init ∈ object.initialisers) :
    init.offset.getD 0 + init.ty.width ≤ object.width := by
  simp only [Global.initialisers_fit, Initialiser.fits, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  exact checked.1 init present

theorem Global.initialisers_ordered (object : Global) (checked : object.initialisers_fit = true) :
    object.initialisers.Pairwise (fun first later => first.start_bit + first.ty.bit_width ≤ later.start_bit) := by
  simp only [Global.initialisers_fit, Initialiser.fits, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.2

structure UnitBody where
  namespaceName : String
  procedures : List Procedure
  globals : List Global
  labels : List String := []
  deriving Repr

structure Program where
  units : List UnitBody
  deriving Repr

structure Invocation where
  program : List UInt8 := []
  arguments : List (List UInt8) := []
  deriving Repr

private def decode_strings (current : List UInt8) : List UInt8 → Option (List (List UInt8))
  | [] => if current.isEmpty then some [] else none
  | byte :: rest =>
    if byte == 0 then (current.reverse :: ·) <$> decode_strings [] rest
    else decode_strings (byte :: current) rest

def Invocation.decode (bytes : List UInt8) : Option Invocation := do
  let program :: arguments ← decode_strings [] bytes | none
  return ⟨program, arguments⟩

def Invocation.encoding (invocation : Invocation) : List UInt8 :=
  (invocation.program :: invocation.arguments).flatMap (· ++ [0])

private theorem decode_strings_exact (data current : List UInt8) (parts : List (List UInt8))
    (decoded : decode_strings current data = some parts) :
    parts.flatMap (· ++ [0]) = current.reverse ++ data := by
  induction data generalizing current parts with
  | nil =>
    cases current <;> simp_all [decode_strings]
  | cons head rest ih =>
    by_cases zero : head = 0
    · subst head
      cases tail : decode_strings [] rest with
      | none => simp [decode_strings, tail] at decoded
      | some strings =>
        simp [decode_strings, tail] at decoded
        subst parts
        simpa [List.append_assoc] using congrArg (fun bytes => current.reverse ++ (0 :: bytes)) (ih [] strings tail)
    · have decoded := ih (head :: current) parts (by simpa [decode_strings, zero] using decoded)
      simpa [List.reverse_cons, List.append_assoc] using decoded

theorem Invocation.decode_exact (bytes : List UInt8) (invocation : Invocation)
    (decoded : Invocation.decode bytes = some invocation) : invocation.encoding = bytes := by
  unfold Invocation.decode at decoded
  cases result : decode_strings [] bytes with
  | none => simp [result] at decoded
  | some strings =>
    cases strings with
    | nil => simp [result] at decoded
    | cons program arguments =>
      simp [result] at decoded
      subst invocation
      simpa [Invocation.encoding] using decode_strings_exact bytes [] (program :: arguments) result

private theorem decode_strings_entry (entry current suffix : List UInt8) (nonzero : 0 ∉ entry) :
    decode_strings current (entry ++ 0 :: suffix) =
      (fun strings => (current.reverse ++ entry) :: strings) <$> decode_strings [] suffix := by
  induction entry generalizing current with
  | nil => simp [decode_strings]
  | cons byte remaining ih =>
    have separate : byte ≠ 0 := by
      intro zero
      exact nonzero (by simp [zero])
    have tail : 0 ∉ remaining := fun found => nonzero (List.mem_cons_of_mem _ found)
    simpa [decode_strings, separate, List.reverse_cons, List.append_assoc] using ih (byte :: current) tail

private theorem decode_strings_encoding (strings : List (List UInt8))
    (nonzero : ∀ entry ∈ strings, 0 ∉ entry) :
    decode_strings [] (strings.flatMap (· ++ [0])) = some strings := by
  induction strings with
  | nil => rfl
  | cons entry remaining ih =>
    have tail := ih (fun string inside => nonzero string (List.mem_cons_of_mem _ inside))
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append]
    rw [decode_strings_entry _ _ _ (nonzero entry (List.mem_cons_self ..)), tail]
    rfl

theorem Invocation.decode_encoding (invocation : Invocation)
    (nonzero : ∀ entry ∈ invocation.program :: invocation.arguments, 0 ∉ entry) :
    Invocation.decode invocation.encoding = some invocation := by
  cases invocation with
  | mk program arguments =>
    unfold Invocation.decode Invocation.encoding
    rw [decode_strings_encoding _ nonzero]
    rfl

def Program.procedures (program : Program) : List Procedure :=
  program.units.flatMap (·.procedures)

def Program.globals (program : Program) : List Global :=
  program.units.flatMap (·.globals)

def Program.labels (program : Program) : List String :=
  (program.units.flatMap (·.labels)).mergeSort

def Program.label_codes (program : Program) : List (String × Int) :=
  program.labels.zipIdx.map fun (name, index) =>
    (name, 9223372036854775808 + Int.ofNat program.procedures.length + Int.ofNat index)

private def Block.labels_checked (block : Block) (labels : List String) : Bool :=
  match block.action with
  | .indirect choice destinations =>
    choice.symbols.all (fun name => labels.contains name && (destinations.lookup name).isSome)
  | _ => true

def Program.labels_checked (program : Program) : Bool :=
  let labels := program.labels
  decide ((program.procedures.map (·.name) ++ labels).Nodup) &&
    program.procedures.all (fun procedure =>
      procedure.dispatch.all (fun dispatch => dispatch.blocks.all (fun block => block.labels_checked labels)))

theorem checked_computed_jump (program : Program) (checked : program.labels_checked = true)
    (procedure : Procedure) (registered : procedure ∈ program.procedures)
    (dispatch : Dispatch) (found : procedure.dispatch = some dispatch)
    (block : Block) (installed : block ∈ dispatch.blocks)
    (choice : LabelChoice) (destinations : List (String × Nat))
    (indirect : block.action = .indirect choice destinations) (symbol : String) (chosen : symbol ∈ choice.symbols) :
    ∃ raw target, computed_jump (fun name => program.label_codes.lookup name)
      (fun name => destinations.lookup name) (some (raw, symbol)) = some target := by
  simp only [Program.labels_checked, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  have procedureOk := checked.2 procedure registered
  simp only [found, Option.all_some, List.all_eq_true] at procedureOk
  have blockOk := procedureOk block installed
  simp only [Block.labels_checked, indirect, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at blockOk
  obtain ⟨registeredLabel, destination⟩ := blockOk symbol chosen
  have names : program.label_codes.map Prod.fst = program.labels := by
    simp [Program.label_codes, List.map_map, Function.comp_def]
  have present : (program.label_codes.lookup symbol).isSome = true := by
    obtain ⟨entry, present, equal⟩ := List.mem_map.mp (names.symm ▸ registeredLabel)
    exact List.lookup_isSome_iff.mpr ⟨entry, present, beq_iff_eq.mpr equal.symm⟩
  obtain ⟨raw, code⟩ := Option.isSome_iff_exists.mp present
  obtain ⟨target, next⟩ := Option.isSome_iff_exists.mp destination
  exact ⟨raw, target, (computed_jump_matches_symbol _ _ _ _ _).mpr ⟨code, next⟩⟩

def Program.lookup (program : Program) (name : String) : Option Procedure :=
  program.procedures.find? (fun procedure => procedure.name == name)

theorem lookup_registered (program : Program) (procedure : Procedure)
    (unique : (program.procedures.map (·.name)).Nodup)
    (registered : procedure ∈ program.procedures) :
    program.lookup procedure.name = some procedure := by
  unfold Program.lookup
  generalize eq : program.procedures = procedures at unique registered ⊢
  clear eq
  induction procedures with
  | nil => simp at registered
  | cons first rest ih =>
    obtain ⟨fresh, distinct⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp registered with rfl | member
    · simp
    · have away : first.name ≠ procedure.name := by
        intro equal
        apply fresh
        change first.name ∈ rest.map Procedure.name
        rw [equal]
        exact List.mem_map.mpr ⟨procedure, member, rfl⟩
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr away]
      exact ih distinct member

inductive Value where
  | integer (word : Int)
  | pointer (address : Pointer)
  | arguments (values : List Value)

inductive Computation (α : Type) where
  | pure (value : α)
  | tick (next : Computation α)
  | output (byte : UInt8) (next : Computation α)
  | heap (operation : HeapEffect) (next : HeapReply → Computation α)
  | invalid
  | fault (reason : HeapFault)
  | terminate (status : Int)
  | suspend

def Computation.bind (next : α → Computation β) : Computation α → Computation β
  | .pure value => next value
  | .tick rest => .tick (bind next rest)
  | .output byte rest => .output byte (bind next rest)
  | .heap operation rest => .heap operation fun reply => bind next (rest reply)
  | .invalid => .invalid
  | .fault reason => .fault reason
  | .terminate status => .terminate status
  | .suspend => .suspend

def Computation.emit (next : α → TraceProgram) : Computation α → TraceProgram
  | .pure value => next value
  | .tick rest => .tick (rest.emit next)
  | .output byte rest => .output [byte] (rest.emit next)
  | .heap operation rest => .effect operation fun reply => (rest reply).emit next
  | .invalid => .jump 0
  | .fault reason => .fail reason
  | .terminate status => .finish status
  | .suspend => .jump 1

theorem emit_bind (action : Computation α) (next : α → Computation β) (finish : β → TraceProgram) :
    (action.bind next).emit finish = action.emit (fun value => (next value).emit finish) := by
  induction action with
  | pure => rfl
  | invalid | fault _ | terminate _ => rfl
  | suspend => rfl
  | tick _ ih | output _ _ ih => simp only [Computation.bind, Computation.emit, ih]
  | heap op _ ih => exact congrArg (TraceProgram.effect op) (funext ih)

instance : Monad Computation where
  pure := .pure
  bind action next := action.bind next

@[simp] theorem emit_monad_bind (action : Computation α) (next : α → Computation β) (finish : β → TraceProgram) :
    (action >>= next).emit finish = action.emit (fun value => (next value).emit finish) :=
  emit_bind action next finish

@[simp] theorem emit_pure (value : α) (finish : α → TraceProgram) :
    ((pure value : Computation α)).emit finish = finish value := rfl

private def integer (value : Value) : Computation Int :=
  match value with
  | .integer word => pure word
  | _ => .invalid

private def pointer (value : Value) : Computation Pointer :=
  match value with
  | .pointer address => pure address
  | _ => .invalid

private def terminate (value : Value) : Computation Value := do
  .terminate (← integer value)

private def byte (value : Int) : UInt8 := UInt8.ofNat (unsigned 8 value).toNat

private def truth : Value → Bool
  | .integer word => word != 0
  | .pointer address => address.address != 0
  | .arguments _ => false

private def logical (test : Bool) : Value := .integer (if test then 1 else 0)

private def pointer_compare (equality : Bool) (first second : Value) : Computation Value := do
  let left ← pointer first
  let right ← pointer second
  pure (logical ((left.address == right.address) == equality))

private def convert : TypeCode → Value → Computation Value
  | .pointer, value@(.pointer _) => pure value
  | .byte, .integer value => pure (.integer (unsigned 8 value))
  | .signedByte, .integer value => pure (.integer (signed 8 value))
  | .integer, .integer value => pure (.integer (signed 32 value))
  | .unsignedInt, .integer value => pure (.integer (unsigned 32 value))
  | .size, .integer value => pure (.integer (unsigned 64 value))
  | .bitField _ width isSigned, .integer value =>
    pure (.integer (if isSigned then signed (width + 1) value else unsigned (width + 1) value))
  | _, _ => .invalid

private def perform (operation : HeapEffect) : Computation HeapReply := .heap operation .pure

private def alloc (size : Int) (heap : Bool := true) : Computation Value := do
  if size < 0 ∨ 9223372036854775807 < size then return ← .fault .hostSize
  match ← perform (.allocate size.toNat heap) with
  | .pointer address => pure (.pointer address)
  | _ => .invalid

private def read (ty : TypeCode) (address : Value) : Computation Value := do
  let address ← pointer address
  match ty with
  | .pointer =>
    match ← perform (.loadPointer address) with
    | .pointer value => pure (.pointer value)
    | _ => .invalid
  | .byte | .signedByte =>
    match ← perform (.loadByte address) with
    | .byte value => convert ty (.integer value.toNat)
    | _ => .invalid
  | .integer | .unsignedInt | .size =>
    match ← perform (.loadWord address ty.width) with
    | .word value => convert ty (.integer value)
    | _ => .invalid
  | .bitField shift _ _ =>
    match ← perform (.loadWord address ty.width) with
    | .word value => convert ty (.integer (value / 2 ^ shift))
    | _ => .invalid

private def store (ty : TypeCode) (address value : Value) : Computation Value := do
  let p ← pointer address
  let converted ← convert ty value
  match ty, converted with
  | .pointer, .pointer target =>
    let _ ← perform (.storePointer p target)
    pure converted
  | .byte, .integer scalar | .signedByte, .integer scalar =>
    let _ ← perform (.storeByte p (byte scalar))
    pure converted
  | .integer, .integer scalar | .unsignedInt, .integer scalar | .size, .integer scalar =>
    let _ ← perform (.storeWord p ty.width scalar)
    pure converted
  | .bitField shift width _, .integer scalar =>
    let _ ← perform (.storeBits p shift (width + 1) scalar)
    pure converted
  | _, _ => .invalid

private def move_bytes (destination source size : Value) : Computation Value := do
  let d ← pointer destination
  let s ← pointer source
  let count ← integer size
  if count < 0 ∨ 9223372036854775807 < count then return ← .fault .hostSize
  let _ ← perform (.copy s d count.toNat)
  pure destination

private def copy_record (destination source : Value) (width : Nat) : Computation Value := do
  let dst ← pointer destination
  let src ← pointer source
  let _ ← perform (.copyAggregate src dst width)
  pure (.integer 0)

private def emit_byte (value : Value) : Computation Value := do
  let n ← integer value
  let b := byte n
  .output b (.pure (.integer b.toNat))

private def release_heap (value : Value) : Computation Value := do
  let address ← pointer value
  let _ ← perform (.release address)
  pure (.integer 0)

private def add_offset (stride : Nat) (base index : Value) : Computation Value := do
  let address ← pointer base
  let delta ← integer index
  pure (.pointer (offset_pointer address (stride * delta)))

private def scalar_apply (op : ScalarOp) (ty : TypeCode) (left right : Value) : Computation Value := do
  let x ← integer left
  let y ← integer right
  let arithmetic := fun result : Int =>
    if ty.signed && (result < -2147483648 || 2147483648 ≤ result) then .fault .signedOverflow
    else convert ty (.integer result)
  match op with
  | .add => arithmetic (x + y)
  | .sub => arithmetic (x - y)
  | .mul => arithmetic (x * y)
  | .eq => pure (logical (x == y))
  | .ne => pure (logical (x != y))
  | .lt => pure (logical (x < y))
  | .le => pure (logical (x ≤ y))
  | .gt => pure (logical (x > y))
  | .ge => pure (logical (x ≥ y))

private def argument_values (value : Value) : Computation (List Value) :=
  match value with
  | .arguments values => pure values
  | _ => .invalid

abbrev Calls := String → List Value → Computation Value

abbrev Globals := List (String × Value)

structure Locals where
  slots : List Value
  globals : Globals

private def locate (locals : Locals) (index : Nat) : Computation Value :=
  match locals.slots[index]? with
  | none => .invalid
  | some value => pure value

private def locate_global (globals : Globals) (name : String) : Computation Value :=
  match globals.lookup name with
  | none => .invalid
  | some address => pure address

def Expression.evaluate (calls : Calls) (locals : Locals) : Expression → Computation Value
  | .literal n => pure (.integer n)
  | .nullPointer => pure (.pointer ⟨0, 0⟩)
  | .slotAddress slot => locate locals slot
  | .globalAddress name => locate_global locals.globals name
  | .load ty address => do read ty (← address.evaluate calls locals)
  | .cast ty operand => do convert ty (← operand.evaluate calls locals)
  | .offset base index stride => do add_offset stride (← base.evaluate calls locals) (← index.evaluate calls locals)
  | .field base displacement => do add_offset 1 (← base.evaluate calls locals) (.integer displacement)
  | .logicalNot operand => do pure (logical (! truth (← operand.evaluate calls locals)))
  | .logic conjunction lhs rhs => do
    if truth (← lhs.evaluate calls locals) == conjunction then pure (logical (truth (← rhs.evaluate calls locals)))
    else pure (logical (!conjunction))
  | .pointerCompare equality lhs rhs =>
    do pointer_compare equality (← lhs.evaluate calls locals) (← rhs.evaluate calls locals)
  | .allocate size => do alloc (← integer (← size.evaluate calls locals))
  | .move dst src size => do move_bytes (← dst.evaluate calls locals) (← src.evaluate calls locals) (← size.evaluate calls locals)
  | .copyRecord dst src width _ => do copy_record (← dst.evaluate calls locals) (← src.evaluate calls locals) width
  | .put value => do emit_byte (← value.evaluate calls locals)
  | .release address => do release_heap (← address.evaluate calls locals)
  | .exit status => do terminate (← status.evaluate calls locals)
  | .assign ty address value => do store ty (← address.evaluate calls locals) (← value.evaluate calls locals)

  | .scalar op ty left right => do scalar_apply op ty (← left.evaluate calls locals) (← right.evaluate calls locals)
  | .call name ty arguments => do
    let values ← argument_values (← arguments.evaluate calls locals)
    convert ty (← calls name values)
  | .emptyArguments => pure (.arguments [])
  | .argument ty value rest => do
    let packed ← convert ty (← value.evaluate calls locals)
    pure (.arguments (packed :: (← argument_values (← rest.evaluate calls locals))))

private def initialiser_address (base : Value) : Option Nat → Computation Value
  | none => pure base
  | some displacement => add_offset 1 base (.integer displacement)

private def initialise_stores (calls : Calls) (locals : Locals) (base : Value) : List Initialiser → Computation Unit
  | [] => pure ()
  | init :: rest => do
    let value ← init.value.evaluate calls locals
    let address ← initialiser_address base init.offset
    let _ ← store init.ty address value
    initialise_stores calls locals base rest

private def clear (address : Value) (width : Nat) : Computation Unit := do
  let _ ← perform (.clear (← pointer address) width)
  pure ()

private inductive Flow where
  | next
  | stop
  | restart
  | returned (value : Value)

private def Flow.result : Flow → Computation Value
  | .next => pure (.integer 0)
  | .returned value => pure value
  | _ => .invalid

private def Exits.permits (exits : Exits) : Flow → Prop
  | .next => exits.next = true
  | .stop => exits.stop = true
  | .restart => exits.restart = true
  | .returned _ => True

private def Computation.all (property : α → Prop) : Computation α → Prop
  | .pure value => property value
  | .tick rest | .output _ rest => rest.all property
  | .heap _ next => ∀ reply, (next reply).all property
  | .invalid | .fault _ | .terminate _ | .suspend => True

private theorem Computation.all_bind (input : Computation α) (next : α → Computation β)
    (inputOk : input.all property) (nextOk : ∀ x, property x → (next x).all result) :
    (input >>= next).all result := by
  induction input with
  | pure value => exact nextOk value inputOk
  | tick _ ih | output _ _ ih => exact ih inputOk
  | heap _ _ ih => exact fun reply => ih reply (inputOk reply)
  | invalid | fault | terminate | suspend => trivial

private theorem Computation.all_mono (input : Computation α) (inputOk : input.all property)
    (implies : ∀ x, property x → result x) : input.all result := by
  induction input with
  | pure value => exact implies value inputOk
  | tick _ ih | output _ _ ih => exact ih inputOk
  | heap _ _ ih => exact fun reply => ih reply (inputOk reply)
  | invalid | fault | terminate | suspend => trivial

private theorem Computation.all_values (input : Computation α) : input.all (fun _ => True) := by
  induction input with
  | pure | invalid | fault | terminate | suspend => trivial
  | tick _ ih | output _ _ ih => exact ih
  | heap _ _ ih => exact ih

private theorem Computation.emit_congr (input : Computation α) (first second : α → TraceProgram)
    (allowed : input.all property) (same : ∀ value, property value → first value = second value) :
    input.emit first = input.emit second := by
  induction input with
  | pure value => exact same value allowed
  | tick _ ih | output _ _ ih => simp only [Computation.emit, ih allowed]
  | heap operation _ ih => exact congrArg (TraceProgram.effect operation) (funext fun reply => ih reply (allowed reply))
  | invalid | fault | terminate | suspend => rfl

private def sequence (first rest : Computation Flow) : Computation Flow := do
  match ← first with
  | .next => rest
  | flow => pure flow

private def execute_loop (post : Bool) (condition : Computation Value) (body : Computation Flow)
    (advance : Computation Value) : Nat → Computation Flow
  | 0 => .suspend
  | iterations + 1 => .tick <|
    let restartLoop := fun () => execute_loop post condition body advance iterations
    let if_true := fun (tested : Value) (yes : Unit → Computation Flow) => if truth tested then yes () else pure .next
    let iterate := fun (again : Unit → Computation Flow) => do
      match ← body with
      | .returned value => pure (.returned value)
      | .stop => pure .next
      | .next | .restart => again ()
    if post then iterate fun () => condition >>= fun value => if_true value restartLoop
    else condition >>= fun value => if_true value fun () => iterate fun () => advance >>= fun _ => restartLoop ()

private def execute (calls : Calls) (locals : Locals) (iterations : Nat) : Statement → Computation Flow
  | .empty | .skip => pure .next
  | .sequence first rest => sequence (execute calls locals iterations first) (execute calls locals iterations rest)
  | .block body => execute calls locals iterations body
  | .initialise slot ty value => do
    let _ ← store ty (← locate locals slot) (← value.evaluate calls locals)
    pure .next
  | .initialiseAggregate slot width stores => do
    let base ← locate locals slot
    clear base width
    initialise_stores calls locals base stores
    pure .next
  | .initialiseCopy slot source width _ => do
    let base ← locate locals slot
    let _ ← copy_record base (← source.evaluate calls locals) width
    pure .next
  | .discard expression => do
    let _ ← expression.evaluate calls locals
    pure .next
  | .branch condition yes no => do
    if truth (← condition.evaluate calls locals) then execute calls locals iterations yes
    else execute calls locals iterations no
  | .whileDo condition body =>
    execute_loop false (condition.evaluate calls locals) (execute calls locals iterations body) (pure (.integer 0)) iterations
  | .doWhile body condition =>
    execute_loop true (condition.evaluate calls locals) (execute calls locals iterations body) (pure (.integer 0)) iterations
  | .forDo initial condition body advance =>
    sequence (execute calls locals iterations initial)
      (execute_loop false ((condition.getD (.literal 1)).evaluate calls locals) (execute calls locals iterations body)
        ((advance.getD (.literal 0)).evaluate calls locals) iterations)
  | .stop => pure .stop
  | .restart => pure .restart
  | .result value => do pure (.returned (← value.evaluate calls locals))
  | .gotoLabel _ | .indirect _ | .label .. | .select .. | .caseOf .. => .invalid

private theorem sequence_exits {first rest : Computation Flow} {left right : Exits}
    (head : first.all left.permits) (tail : rest.all right.permits) :
    (sequence first rest).all (left.sequence right).permits := by
  apply Computation.all_bind first _ head
  intro flow allowed
  cases flow with
  | next =>
    apply rest.all_mono tail
    intro flow permitted
    cases flow <;> simp_all [Exits.permits, Exits.sequence]
  | stop | restart | returned => simp_all [Exits.permits, Exits.sequence, Computation.all]

private theorem loop_exits (post : Bool) (test advance : Computation Value) (body : Computation Flow)
    (iterations : Nat) : (execute_loop post test body advance iterations).all (Exits.permits { next := true }) := by
  induction iterations with
  | zero => trivial
  | succ iterations ih =>
    let exits : Exits := { next := true }
    have testOk (value : Value) (yes : Computation Flow) (allowed : yes.all exits.permits) :
        (if truth value then yes else pure .next).all exits.permits := by
      split
      · exact allowed
      · rfl
    have bodyOk (again : Computation Flow) (allowed : again.all exits.permits) :
        (body >>= fun flow => match flow with
          | .returned value => pure (.returned value)
          | .stop => pure .next
          | .next | .restart => again).all exits.permits := by
      apply body.all_bind _ body.all_values
      intro flow _
      cases flow
      · exact allowed
      · rfl
      · exact allowed
      · trivial
    cases post
    · exact test.all_bind _ test.all_values (fun value _ =>
        testOk value _ (bodyOk _ (advance.all_bind _ advance.all_values (fun _ _ => ih))))
    · exact bodyOk _ (test.all_bind _ test.all_values (fun value _ => testOk value _ ih))

private theorem execute_exits (calls : Calls) (locals : Locals) (iterations : Nat) (statement : Statement) :
    (execute calls locals iterations statement).all statement.exits.permits := by
  induction statement with
  | empty | skip | stop | restart => rfl
  | sequence first rest head tail => exact sequence_exits head tail
  | block body allowed => exact allowed
  | initialise slot ty value =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro address _
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro initial _
    exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => rfl)
  | initialiseAggregate slot width stores =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro base _
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro _ _
    exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => rfl)
  | initialiseCopy slot source width alignment =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro base _
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro incoming _
    exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => rfl)
  | discard value =>
    cases value with
    | exit status =>
      have never : ((Expression.exit status).evaluate calls locals).all (fun _ => False) := by
        apply Computation.all_bind _ _ (Computation.all_values _)
        intro value _
        cases value <;> trivial
      exact Computation.all_bind _ _ never (fun _ impossible => impossible.elim)
    | _ => exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => rfl)
  | result value => exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => trivial)
  | branch condition yes no left right =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro tested _
    split
    · apply Computation.all_mono _ left
      intro flow allowed
      cases flow <;> simp_all [Exits.permits, Exits.join, Statement.exits]
    · apply Computation.all_mono _ right
      intro flow allowed
      cases flow <;> simp_all [Exits.permits, Exits.join, Statement.exits]
  | whileDo | doWhile => exact loop_exits _ _ _ _ _
  | forDo initial condition body advance head _ => exact sequence_exits head (loop_exits _ _ _ _ _)
  | gotoLabel | indirect | label | select | caseOf => trivial

private theorem structured_control_correct (statement : Statement) (name : String)
    (calls : Calls) (locals : Locals) (iterations : Nat) (checked : statement.exits.allowed (name == "main") = true) :
    (execute calls locals iterations statement).all (fun flow => match flow with
      | .returned _ => True
      | .next => name = "main"
      | .stop | .restart => False) := by
  apply Computation.all_mono _ (execute_exits calls locals iterations statement)
  intro flow allowed
  cases flow <;> simp_all [Exits.allowed, Exits.permits]

private inductive Route where
  | jump (target : Nat)
  | exit (flow : Flow)

private def step_flow (next : Nat) (redirect : Option (Nat × Nat)) : Flow → Route
  | .next => .jump next
  | .stop => (redirect.map (fun (stop, _) => .jump stop)).getD (.exit .stop)
  | .restart => (redirect.map (fun (_, restart) => .jump restart)).getD (.exit .restart)
  | .returned value => .exit (.returned value)

private def select_route (entries : List SwitchEntry) (selector : Int) : Route :=
  match switch_search selector none entries with
  | none => .exit .next
  | some target => .jump target

private def LabelChoice.evaluate (calls : Calls) (locals : Locals) : LabelChoice → Computation String
  | .address symbol => pure symbol
  | .conditional condition yes no => do
    if truth (← condition.evaluate calls locals) then yes.evaluate calls locals else no.evaluate calls locals

private def indirect_route (destinations : List (String × Nat)) (symbol : String) : Computation Route :=
  match destinations.lookup symbol with
  | none => .invalid
  | some target => pure (.jump target)

private def Block.evaluate (block : Block) (calls : Calls) (locals : Locals) (fuel : Nat) : Computation Route :=
  match block.action with
  | .finish => pure (.exit .next)
  | .escape stop => pure (.exit (if stop then .stop else .restart))
  | .jump target => pure (.jump target)
  | .branch condition yes no => do pure (.jump (if truth (← condition.evaluate calls locals) then yes else no))
  | .select selector entries => do pure (select_route entries (← integer (← selector.evaluate calls locals)))
  | .indirect choice destinations => do indirect_route destinations (← choice.evaluate calls locals)
  | .run statement next => do pure (step_flow next block.redirect (← execute calls locals fuel statement))

private def Block.permits (block : Block) : Route → Prop
  | .jump target => target ∈ block.outgoing
  | .exit flow => block.exits.permits flow

private theorem member_erase_dups (target : Nat) (items : List Nat) (present : target ∈ items) :
    target ∈ items.eraseDups := by
  match items with
  | [] => simp at present
  | first :: rest =>
    rw [List.eraseDups_cons]
    by_cases equal : target = first
    · simp [equal]
    · have tail : target ∈ rest := (List.mem_cons.mp present).resolve_left equal
      have filtered : target ∈ rest.filter (fun value => !value == first) := by simp [tail, equal]
      exact List.mem_cons_of_mem _ (member_erase_dups target _ filtered)
termination_by items.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem Block.outgoing_listed (block : Block) (target : Nat) (outgoing : target ∈ block.outgoing) :
    target ∈ block.targets := by
  obtain ⟨operation, redirect⟩ := block
  rcases redirect with _ | ⟨stop, restart⟩
  · cases operation <;> simp_all [Block.outgoing, Block.targets, BlockAction.targets]
  · change target ∈ (stop :: restart :: operation.targets).mergeSort.eraseDups
    apply member_erase_dups
    rw [List.mem_mergeSort]
    cases operation <;> simp_all [Block.outgoing, BlockAction.targets]
    case run statement next =>
      rcases outgoing with a | a | a <;> simp_all

private theorem Block.evaluate_permitted (block : Block) (calls : Calls) (locals : Locals) (fuel : Nat) :
    (block.evaluate calls locals fuel).all block.permits := by
  obtain ⟨action, redirect⟩ := block
  cases action with
  | finish | jump => simp [Block.evaluate, Block.permits, Block.outgoing, Block.exits, BlockAction.targets,
      Exits.permits, Computation.all]
  | escape stop => cases stop <;> rfl
  | branch condition yes no =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro value _
    split <;> simp [Block.permits, Block.outgoing, BlockAction.targets, Computation.all]
  | select selector entries =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro value _
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro number _
    cases found : switch_search number none entries with
    | none =>
      have absent : entries.any (·.bounds.isNone) = false := by
        by_cases existsDefault : entries.any (·.bounds.isNone) = true
        · have result := switch_search_has_target number entries none (by simp [existsDefault])
          simp [found] at result
        · simpa using existsDefault
      simp [select_route, found, Block.permits, Block.exits, Exits.permits, Computation.all, absent]
    | some target =>
      obtain absent | ⟨entry, present, rfl⟩ := switch_search_lists_target number none entries target found
      · contradiction
      · simp [select_route, found, Block.permits, Block.outgoing, BlockAction.targets, Computation.all,
          List.mem_map_of_mem present]
  | indirect choice destinations =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro symbol _
    cases found : destinations.lookup symbol with
    | none => simp [indirect_route, found, Computation.all]
    | some target =>
      obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp found
      have present : (symbol, target) ∈ destinations := by simp [table]
      simp [indirect_route, found, Block.permits, Block.outgoing, BlockAction.targets, Computation.all,
        List.mem_map_of_mem present]
  | run statement next =>
    apply Computation.all_bind _ _ (execute_exits calls locals fuel statement)
    intro flow allowed
    cases flow <;> cases redirect <;> simp_all [step_flow, Block.permits, Block.outgoing, Block.exits,
      Exits.permits, Computation.all]

private def execute_dispatch (dispatch : Dispatch) (calls : Calls) (locals : Locals) (depth : Nat) :
    Nat → Nat → Computation Flow
  | 0, _ => .suspend
  | steps + 1, index => .tick <|
    match dispatch.blocks[index]? with
    | none => .invalid
    | some block => do
      match ← block.evaluate calls locals depth with
      | .exit flow => pure flow
      | .jump next => execute_dispatch dispatch calls locals depth steps next

private def Procedure.execute (procedure : Procedure) (calls : Calls) (locals : Locals) (depth : Nat) :
    Computation Flow :=
  match procedure.dispatch with
  | none => Ordinary.execute calls locals depth procedure.statements
  | some dispatch => execute_dispatch dispatch calls locals depth depth dispatch.entry

private theorem dispatch_control_correct (dispatch : Dispatch) (name : String) (calls : Calls) (locals : Locals)
    (depth steps index : Nat) (checked : dispatch.control_checked (name == "main") = true)
    (reachable : index ∈ dispatch.region) :
    (execute_dispatch dispatch calls locals depth steps index).all (fun flow => match flow with
      | .returned _ => True
      | .next => name = "main"
      | .stop | .restart => False) := by
  induction steps generalizing index with
  | zero => trivial
  | succ steps ih =>
    simp only [Dispatch.control_checked, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at checked
    have localCheck := checked.2.2 index reachable
    cases found : dispatch.blocks[index]? with
    | none => simp [found] at localCheck
    | some block =>
      simp only [found, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at localCheck
      simp only [execute_dispatch, found, Computation.all]
      apply Computation.all_bind _ _ (block.evaluate_permitted calls locals depth)
      intro route permitted
      cases route with
      | jump target => exact ih target (localCheck.2 target permitted)
      | exit flow =>
        have allowed := localCheck.1
        cases flow <;> simp_all [Block.permits, Exits.allowed, Exits.permits, Computation.all]

theorem Procedure.control_correct (procedure : Procedure) (calls : Calls) (locals : Locals) (depth : Nat)
    (checked : procedure.control_checked = true) :
    (procedure.execute calls locals depth).all (fun flow => match flow with
      | .returned _ => True
      | .next => procedure.name = "main"
      | .stop | .restart => False) := by
  cases graph : procedure.dispatch with
  | none =>
    simp only [Procedure.control_checked, graph] at checked
    simpa only [Procedure.execute, graph] using
      structured_control_correct procedure.statements procedure.name calls locals depth checked
  | some dispatch =>
    simp only [Procedure.control_checked, graph] at checked
    have entry : dispatch.entry ∈ dispatch.region := by
      simp only [Dispatch.control_checked, Bool.and_eq_true, List.contains_iff_mem] at checked
      exact checked.2.1
    simpa only [Procedure.execute, graph] using
      dispatch_control_correct dispatch procedure.name calls locals depth depth dispatch.entry checked entry

private def allocate_locals : List Nat → Computation (List Value)
  | [] => pure []
  | width :: rest => do pure ((← alloc width false) :: (← allocate_locals rest))

private def allocate_parameters : List TypeCode → List Value → Computation (List Value)
  | [], [] => pure []
  | ty :: types, value :: values => do
    let address ← alloc ty.width false
    let _ ← store ty address value
    return address :: (← allocate_parameters types values)
  | _, _ => .invalid

private def Procedure.frame (procedure : Procedure) (globals : Globals) (values : List Value) : Computation Locals := do
  let arguments ← allocate_parameters procedure.parameters values
  return ⟨arguments ++ (← allocate_locals procedure.locals), globals⟩

private def allocate_globals : List Global → Computation Globals
  | [] => pure []
  | object :: rest => do
    match ← perform (.allocateGlobal object.width) with
    | .pointer address => return (object.name, .pointer address) :: (← allocate_globals rest)
    | _ => .invalid

private def initialise_globals (globals : Globals) : List Global → Computation Unit
  | [] => pure ()
  | object :: rest => do
    if !object.initialisers.isEmpty then
      let address ← locate_global globals object.name
      initialise_stores (fun _ _ => .invalid) ⟨[], globals⟩ address object.initialisers
    initialise_globals globals rest

private def Program.startup (program : Program) : Computation Globals := do
  let globals ← allocate_globals program.globals
  initialise_globals globals program.globals
  pure globals

private def store_argument (ty : TypeCode) (base : Value) : Nat → List Value → Computation Unit
  | _, [] => pure ()
  | index, value :: rest => do
    let address ← add_offset ty.width base (.integer index)
    let _ ← store ty address value
    store_argument ty base (index + 1) rest

private def allocate_argument (payload : List UInt8) : Computation Value := do
  let address ← alloc (payload.length + 1 : Nat) false
  store_argument .byte address 0 ((payload ++ [0]).map (fun (value : UInt8) => .integer value.toNat))
  pure address

private def argument_vector (invocation : Invocation) : Computation (List Value) := do
  let strings ← (invocation.program :: invocation.arguments).mapM allocate_argument
  let address ← alloc (8 * (strings.length + 1) : Nat) false
  store_argument .pointer address 0 (strings ++ [.pointer ⟨0, 0⟩])
  return [.integer strings.length, address]

private def Program.entry_arguments (program : Program) (arguments : List Value) : List Value :=
  match program.lookup "main" with
  | some procedure => arguments.take procedure.parameters.length
  | none => []

private def source_calls (program : Program) (globals : Globals) : Nat → Calls
  | 0, _, _ => .suspend
  | depth + 1, name, values => .tick <| do
    match program.lookup name with
    | none => .invalid
    | some procedure =>
      let locals ← procedure.frame globals values
      let flow ← procedure.execute (source_calls program globals depth) locals depth
      convert procedure.resultType (← flow.result)

def Program.source (program : Program) (depth : Nat) (invocation : Invocation := {}) : Computation Int := do
  let globals ← program.startup
  let arguments ← argument_vector invocation
  integer (← source_calls program globals depth "main" (program.entry_arguments arguments))

private abbrev Action (α : Type) := (α → TraceProgram) → TraceProgram

private def action (source : Computation α) : Action α := source.emit

private abbrev LoweredCalls := String → List Value → Action Value

private def lower (linked : LoweredCalls) (locals : Locals) : Expression → Action Value
  | .literal n, next => next (.integer n)
  | .nullPointer, next => next (.pointer ⟨0, 0⟩)
  | .slotAddress slot, next => action (locate locals slot) next
  | .globalAddress name, next => action (locate_global locals.globals name) next
  | .load ty address, next => lower linked locals address fun value => action (read ty value) next
  | .cast ty operand, next => lower linked locals operand fun value => action (convert ty value) next
  | .offset base index stride, next =>
    lower linked locals base fun b => lower linked locals index fun i => action (add_offset stride b i) next
  | .field base displacement, next => lower linked locals base fun b => action (add_offset 1 b (.integer displacement)) next
  | .logicalNot operand, next => lower linked locals operand fun value => next (logical (! truth value))
  | .logic conjunction lhs rhs, next => lower linked locals lhs fun result =>
    if truth result == conjunction then lower linked locals rhs fun value => next (logical (truth value))
    else next (logical (!conjunction))
  | .pointerCompare equality lhs rhs, next => lower linked locals lhs fun first =>
    lower linked locals rhs fun second => action (pointer_compare equality first second) next
  | .allocate size, next => lower linked locals size fun n =>
    action (integer n) fun size => action (alloc size) next
  | .move dst src size, next => lower linked locals dst fun d => lower linked locals src fun s =>
    lower linked locals size fun count => action (move_bytes d s count) next
  | .copyRecord dst src width _, next =>
    lower linked locals dst fun d => lower linked locals src fun s => action (copy_record d s width) next
  | .put value, next => lower linked locals value fun n => action (emit_byte n) next
  | .release address, next => lower linked locals address fun p => action (release_heap p) next
  | .exit status, next => lower linked locals status fun code => action (terminate code) next
  | .assign ty address value, next => lower linked locals address fun p =>
    lower linked locals value fun v => action (store ty p v) next

  | .scalar op ty left right, next => lower linked locals left fun l =>
    lower linked locals right fun r => action (scalar_apply op ty l r) next
  | .call name ty arguments, next => lower linked locals arguments fun args =>
    action (argument_values args) fun values => linked name values fun result => action (convert ty result) next
  | .emptyArguments, next => next (.arguments [])
  | .argument ty value rest, next => lower linked locals value fun v =>
    action (convert ty v) fun packed => lower linked locals rest fun args =>
    action (argument_values args) fun values => next (.arguments (packed :: values))

private theorem lower_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (locals : Locals) (expression : Expression) (next : Value → TraceProgram) :
    lower linked locals expression next = (expression.evaluate calls locals).emit next := by
  induction expression generalizing next <;>
    simp only [lower, Expression.evaluate, action, emit_monad_bind, emit_pure, *]
  case logic conjunction lhs rhs _ _ =>
    apply congrArg (fun continuation => (lhs.evaluate calls locals).emit continuation)
    funext value
    split <;> simp [*]

private def lower_sequence (first rest : Action Flow) : Action Flow :=
  fun next => first fun flow => match flow with
    | .next => rest next
    | _ => next flow

private theorem lower_sequence_correct (first rest : Computation Flow) (next : Flow → TraceProgram) :
    lower_sequence first.emit rest.emit next = (sequence first rest).emit next := by
  simp only [sequence, lower_sequence, emit_monad_bind]
  congr 1
  funext flow
  cases flow <;> rfl

private def lower_loop (post : Bool) (condition : Action Value) (body : Action Flow) (advance : Action Value) :
    Nat → Action Flow
  | 0, _ => .jump 1
  | iterations + 1, next => .tick <|
    let restartLoop := fun () => lower_loop post condition body advance iterations next
    let if_true := fun (tested : Value) (yes : Unit → TraceProgram) => if truth tested then yes () else next .next
    let iterate := fun (again : Unit → TraceProgram) => body fun flow =>
      match flow with
      | .returned value => next (.returned value)
      | .stop => next .next
      | .next | .restart => again ()
    if post then iterate fun () => condition fun value => if_true value restartLoop
    else condition fun value => if_true value fun () => iterate fun () => advance fun _ => restartLoop ()

private theorem lower_loop_correct (post : Bool) (condition : Computation Value)
    (body : Computation Flow) (advance : Computation Value) (iterations : Nat) (next : Flow → TraceProgram) :
    lower_loop post condition.emit body.emit advance.emit iterations next =
      (execute_loop post condition body advance iterations).emit next := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    have test (value : Value) (yes : Computation Flow) :
        (if truth value then yes else pure .next).emit next =
          if truth value then yes.emit next else next .next := by
      split <;> rfl
    have iterate (again : Computation Flow) :
        (body >>= fun flow => match flow with
          | .returned value => pure (.returned value)
          | .stop => pure .next
          | .next | .restart => again).emit next =
        body.emit (fun flow => match flow with
          | .returned value => next (.returned value)
          | .stop => next .next
          | .next | .restart => again.emit next) := by
      rw [emit_monad_bind]
      congr 1
      funext flow
      cases flow <;> rfl
    cases post <;> simp only [lower_loop, execute_loop, Computation.emit, Bool.false_eq_true,
      ↓reduceIte, emit_monad_bind, test, iterate, ih]

private def lower_stores (linked : LoweredCalls) (locals : Locals) (base : Value) : List Initialiser → Action Unit
  | [], next => next ()
  | init :: rest, next =>
    lower linked locals init.value fun value =>
      action (initialiser_address base init.offset) fun address =>
        action (store init.ty address value) fun _ => lower_stores linked locals base rest next

private theorem lower_stores_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (locals : Locals) (base : Value) (stores : List Initialiser) (next : Unit → TraceProgram) :
    lower_stores linked locals base stores next = (initialise_stores calls locals base stores).emit next := by
  induction stores with
  | nil => rfl
  | cons init rest later =>
    simp only [lower_stores, initialise_stores, action, emit_monad_bind, later, lower_correct calls linked related]

private def lower_statements (linked : LoweredCalls) (locals : Locals) (iterations : Nat) : Statement → Action Flow
  | .empty, next | .skip, next => next .next
  | .sequence first rest, next =>
    lower_sequence (lower_statements linked locals iterations first) (lower_statements linked locals iterations rest) next
  | .block body, next => lower_statements linked locals iterations body next
  | .initialise slot ty value, next => action (locate locals slot) fun address =>
    lower linked locals value fun v => action (store ty address v) fun _ => next .next
  | .initialiseAggregate slot width stores, next => action (locate locals slot) fun base =>
    action (clear base width) fun _ => lower_stores linked locals base stores fun _ => next .next
  | .initialiseCopy slot source width _, next => action (locate locals slot) fun base =>
    lower linked locals source fun value => action (copy_record base value width) fun _ => next .next
  | .discard value, next => lower linked locals value fun _ => next .next
  | .branch condition yes no, next => lower linked locals condition fun tested =>
    if truth tested then lower_statements linked locals iterations yes next
    else lower_statements linked locals iterations no next
  | .whileDo condition body, next =>
    lower_loop false (lower linked locals condition) (lower_statements linked locals iterations body)
      (fun continuation => continuation (.integer 0)) iterations next
  | .doWhile body condition, next =>
    lower_loop true (lower linked locals condition) (lower_statements linked locals iterations body)
      (fun continuation => continuation (.integer 0)) iterations next
  | .forDo initial condition body advance, next =>
    lower_sequence (lower_statements linked locals iterations initial)
      (lower_loop false (lower linked locals (condition.getD (.literal 1)))
        (lower_statements linked locals iterations body) (lower linked locals (advance.getD (.literal 0))) iterations) next
  | .stop, next => next .stop
  | .restart, next => next .restart
  | .result value, next => lower linked locals value fun v => next (.returned v)
  | .gotoLabel _, _ | .indirect _, _ | .label .., _ | .select .., _ | .caseOf .., _ => .jump 0

private theorem lower_statements_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (locals : Locals) (iterations : Nat) (statements : Statement) (next : Flow → TraceProgram) :
    lower_statements linked locals iterations statements next = (execute calls locals iterations statements).emit next := by
  have expression (expr : Expression) : lower linked locals expr = (expr.evaluate calls locals).emit :=
    funext (lower_correct calls linked related locals expr)
  have zero : (fun continuation : Value → TraceProgram => continuation (.integer 0)) =
      (pure (.integer 0) : Computation Value).emit := rfl
  induction statements generalizing next with
  | sequence first rest firstCorrect restCorrect =>
    simp only [lower_statements, execute, funext firstCorrect, funext restCorrect, lower_sequence_correct]
  | whileDo condition body correct | doWhile body condition correct =>
    simp only [lower_statements, execute, expression, funext correct, zero, lower_loop_correct]
  | forDo initial condition body advance initialCorrect bodyCorrect =>
    have loop := funext (lower_loop_correct false ((condition.getD (.literal 1)).evaluate calls locals)
      (execute calls locals iterations body) ((advance.getD (.literal 0)).evaluate calls locals) iterations)
    simp only [lower_statements, execute, expression, funext initialCorrect, funext bodyCorrect,
      loop, lower_sequence_correct]
  | branch condition yes no yesCorrect noCorrect =>
    simp only [lower_statements, execute, expression, emit_monad_bind]
    congr 1
    funext tested
    split <;> simp only [yesCorrect, noCorrect]
  | initialise | initialiseCopy | discard | result =>
    simp only [lower_statements, execute, expression, action, emit_monad_bind, emit_pure]
  | initialiseAggregate =>
    simp only [lower_statements, execute, action, lower_stores_correct calls linked related, emit_monad_bind, emit_pure]
  | block body correct => exact correct next
  | empty | skip | stop | restart | gotoLabel | indirect | label | select | caseOf => rfl

private def lower_label (linked : LoweredCalls) (locals : Locals) : LabelChoice → Action String
  | .address symbol, next => next symbol
  | .conditional condition yes no, next => lower linked locals condition fun value =>
    if truth value then lower_label linked locals yes next else lower_label linked locals no next

private theorem lower_label_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (locals : Locals) (choice : LabelChoice) (next : String → TraceProgram) :
    lower_label linked locals choice next = (choice.evaluate calls locals).emit next := by
  induction choice with
  | address => rfl
  | conditional condition yes no chosen other =>
    simp only [lower_label, LabelChoice.evaluate, lower_correct calls linked related, emit_monad_bind]
    congr 1
    funext value
    split <;> simp only [chosen, other]

private def lower_block (linked : LoweredCalls) (locals : Locals) (depth : Nat) (block : Block) : Action Route :=
  match block.action with
  | .finish => fun next => next (.exit .next)
  | .escape stop => fun next => next (.exit (if stop then .stop else .restart))
  | .jump target => fun next => next (.jump target)
  | .branch condition yes no => fun next =>
    lower linked locals condition fun value => next (.jump (if truth value then yes else no))
  | .select selector entries => fun next =>
    lower linked locals selector fun value => action (integer value) fun number => next (select_route entries number)
  | .indirect choice destinations => fun next =>
    lower_label linked locals choice fun symbol => action (indirect_route destinations symbol) next
  | .run statement target => fun next =>
    lower_statements linked locals depth statement fun flow => next (step_flow target block.redirect flow)

private theorem lower_block_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (locals : Locals) (depth : Nat) (block : Block) (next : Route → TraceProgram) :
    lower_block linked locals depth block next = (block.evaluate calls locals depth).emit next := by
  obtain ⟨operation, redirect⟩ := block
  cases operation with
  | finish | escape | jump => rfl
  | branch | select | run =>
    simp only [lower_block, Block.evaluate, lower_correct calls linked related,
      lower_statements_correct calls linked related, action, emit_monad_bind, emit_pure]
  | indirect =>
    simp only [lower_block, Block.evaluate, lower_label_correct calls linked related, action, emit_monad_bind]

private def lower_dispatch (dispatch : Dispatch) (linked : LoweredCalls) (locals : Locals) (depth : Nat) :
    Nat → Nat → Action Flow
  | 0, _, _ => .jump 1
  | steps + 1, index, next => .tick <|
    match dispatch.blocks[index]? with
    | none => .jump 0
    | some block => lower_block linked locals depth block fun route =>
      match route with
      | .exit flow => next flow
      | .jump target =>
        if target ∈ block.targets then lower_dispatch dispatch linked locals depth steps target next
        else .jump 0

private theorem lower_dispatch_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (dispatch : Dispatch) (locals : Locals) (depth steps index : Nat) (next : Flow → TraceProgram) :
    lower_dispatch dispatch linked locals depth steps index next =
      (execute_dispatch dispatch calls locals depth steps index).emit next := by
  induction steps generalizing index with
  | zero => rfl
  | succ steps ih =>
    cases found : dispatch.blocks[index]? with
    | none => simp [lower_dispatch, execute_dispatch, found, Computation.emit]
    | some block =>
      simp only [lower_dispatch, execute_dispatch, found, Computation.emit, lower_block_correct calls linked related, emit_monad_bind]
      congr 1
      apply Computation.emit_congr _ _ _ (block.evaluate_permitted calls locals depth)
      intro route permitted
      cases route with
      | exit flow => rfl
      | jump target =>
        have listed := block.outgoing_listed target permitted
        exact (if_pos listed).trans (ih target)

private def Procedure.lower (procedure : Procedure) (linked : LoweredCalls) (locals : Locals) (depth : Nat) :
    Action Flow :=
  match procedure.dispatch with
  | none => lower_statements linked locals depth procedure.statements
  | some dispatch => lower_dispatch dispatch linked locals depth depth dispatch.entry

private theorem lower_procedure_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (procedure : Procedure) (locals : Locals) (depth : Nat) (next : Flow → TraceProgram) :
    procedure.lower linked locals depth next = (procedure.execute calls locals depth).emit next := by
  cases found : procedure.dispatch with
  | none => simpa only [Procedure.lower, Procedure.execute, found] using
      lower_statements_correct calls linked related locals depth procedure.statements next
  | some dispatch => simpa only [Procedure.lower, Procedure.execute, found] using
      lower_dispatch_correct calls linked related dispatch locals depth depth dispatch.entry next

private def target_calls (program : Program) (globals : Globals) : Nat → LoweredCalls
  | 0, _, _, _ => .jump 1
  | depth + 1, name, arguments, next => .tick <|
    match program.lookup name with
    | none => .jump 0
    | some procedure => action (procedure.frame globals arguments) fun locals =>
        procedure.lower (target_calls program globals depth) locals depth fun flow =>
          action flow.result fun value => action (convert procedure.resultType value) next

theorem calls_correct (program : Program) (globals : Globals) (depth : Nat) (name : String) (arguments : List Value)
    (next : Value → TraceProgram) :
    target_calls program globals depth name arguments next = (source_calls program globals depth name arguments).emit next := by
  induction depth generalizing name arguments next with
  | zero => rfl
  | succ depth ih =>
    cases found : program.lookup name with
    | none => simp [target_calls, source_calls, found, Computation.emit]
    | some procedure =>
      simp only [target_calls, source_calls, found, action, Computation.emit, emit_monad_bind,
        lower_procedure_correct (source_calls program globals depth) (target_calls program globals depth) ih]

private def lower_allocations : List Global → Action Globals
  | [], next => next []
  | object :: rest, next =>
    .effect (.allocateGlobal object.width) fun reply =>
      match reply with
      | .pointer address =>
        lower_allocations rest fun globals => next ((object.name, .pointer address) :: globals)
      | _ => .jump 0

private theorem lower_allocations_correct (objects : List Global) (next : Globals → TraceProgram) :
    lower_allocations objects next = (allocate_globals objects).emit next := by
  induction objects generalizing next with
  | nil => rfl
  | cons object rest ih =>
    simp only [lower_allocations, allocate_globals, perform, emit_monad_bind, Computation.emit, ih]
    congr 1
    funext reply
    cases reply <;> first | rfl | simp only [emit_monad_bind, emit_pure]

private def no_calls : Calls := fun _ _ => .invalid

private def no_linked_calls : LoweredCalls := fun _ _ _ => .jump 0

private def lower_initialisers (globals : Globals) : List Global → Action Unit
  | [], next => next ()
  | object :: rest, next =>
    if object.initialisers.isEmpty then lower_initialisers globals rest next
    else
      action (locate_global globals object.name) fun address =>
        lower_stores no_linked_calls ⟨[], globals⟩ address object.initialisers fun _ => lower_initialisers globals rest next

private theorem lower_initialisers_correct (globals : Globals) (objects : List Global)
    (next : Unit → TraceProgram) :
    lower_initialisers globals objects next = (initialise_globals globals objects).emit next := by
  induction objects generalizing next with
  | nil => rfl
  | cons object rest ih =>
    cases empty : object.initialisers.isEmpty <;>
      simp [lower_initialisers, initialise_globals, empty, action,
        lower_stores_correct no_calls no_linked_calls (fun _ _ _ => rfl), ih]
    rfl

def Program.target (program : Program) (depth : Nat) (invocation : Invocation := {}) : TraceProgram :=
  lower_allocations program.globals fun globals =>
    lower_initialisers globals program.globals fun _ =>
      action (argument_vector invocation) fun arguments =>
        target_calls program globals depth "main" (program.entry_arguments arguments) fun value => action (integer value) .finish

theorem lower_program_correct (program : Program) (depth : Nat) (invocation : Invocation) :
    program.target depth invocation = (program.source depth invocation).emit .finish := by
  simp only [Program.target, Program.source, Program.startup, lower_allocations_correct,
    lower_initialisers_correct, calls_correct, action, emit_monad_bind, emit_pure]

def blocks : Nat → Option TraceProgram
  | 1 => some (.jump 1)
  | _ => none

def Program.observation (program : Program) (fuel : Nat) (terminal : Bool) (invocation : Invocation := {}) :=
  (run_trace sparse_machine terminal blocks fuel (program.target fuel invocation) ⟨[], ⟨1, 4096⟩⟩
    ⟨[], [], 0, true⟩).snapshot.observation

def Program.source_observation (program : Program) (fuel : Nat) (terminal : Bool) (invocation : Invocation := {}) :=
  (run_trace abstract_machine terminal blocks fuel ((program.source fuel invocation).emit .finish)
    ⟨fun _ => none, ⟨1, 4096⟩⟩ ⟨[], [], true⟩).observation

def Observes (observe : Nat → TraceOutcome × List UInt8) (result : TraceOutcome × List UInt8) : Prop :=
  result.1 ≠ .paused ∧ ∃ fuel, observe fuel = result

theorem explicit_exit_observation (status : Int) (fuel : Nat) (terminal : Bool) (heap : HeapState)
    (stdout : StdoutState) (continuation : Value → TraceProgram) :
    (run_trace abstract_machine terminal blocks (fuel + 1)
      ((Computation.terminate status : Computation Value).emit continuation) heap stdout).observation =
      (.returned (unsigned 8 status), stdout.visible ++ stdout.pending) := rfl

theorem prefix_refines (program : Program) (terminal : Bool) (fuel : Nat) (invocation : Invocation)
    (memory : HeapImage) (stdout : StdoutBuffer)
    (valid : stdout.size = stdout.snapshot.pending.length) (reference : Nat → Nat)
    (distinct : Function.Injective reference) :
    ((run_trace (sparse_machine reference) terminal blocks fuel (program.target fuel invocation) memory stdout).snapshot
      reference).observation =
      (run_trace abstract_machine terminal blocks fuel ((program.source fuel invocation).emit .finish)
        (memory.snapshot reference) stdout.snapshot).observation := by
  rw [lower_program_correct]
  exact trace_observations_refine terminal _ fuel _ memory stdout valid reference distinct


inductive Agrees : Nat → Computation α → Computation α → Prop where
  | zero : Agrees 0 left right
  | pure : Agrees fuel (.pure value) (.pure value)
  | invalid : Agrees fuel .invalid .invalid
  | fault : Agrees fuel (.fault reason) (.fault reason)
  | terminate : Agrees fuel (.terminate status) (.terminate status)
  | suspend : Agrees fuel .suspend .suspend
  | tick : Agrees fuel left right → Agrees (fuel + 1) (.tick left) (.tick right)
  | output {outByte : UInt8} : Agrees fuel left right → Agrees (fuel + 1) (.output outByte left) (.output outByte right)
  | heap : (∀ reply, Agrees fuel (left reply) (right reply)) →
      Agrees (fuel + 1) (.heap op left) (.heap op right)

theorem Agrees.weaken {n : Nat} {left right : Computation α} (agreement : Agrees n left right)
    (fuel : Nat) (bound : fuel ≤ n) : Agrees fuel left right := by
  induction agreement generalizing fuel with
  | zero =>
    have : fuel = 0 := by omega
    subst fuel
    exact .zero
  | pure => exact .pure
  | invalid => exact .invalid
  | fault => exact .fault
  | terminate => exact .terminate
  | suspend => exact .suspend
  | tick _ ih => cases fuel with
    | zero => exact .zero
    | succ fuel => exact .tick (ih fuel (by omega))
  | output _ ih => cases fuel with
    | zero => exact .zero
    | succ fuel => exact .output (ih fuel (by omega))
  | heap _ ih => cases fuel with
    | zero => exact .zero
    | succ fuel => exact .heap (fun reply => ih reply fuel (by omega))

theorem Agrees.refl (fuel : Nat) (value : Computation α) : Agrees fuel value value := by
  induction fuel generalizing value with
  | zero => exact .zero
  | succ fuel ih =>
    cases value with
    | pure => exact .pure
    | invalid => exact .invalid
    | fault => exact .fault
    | terminate => exact .terminate
    | suspend => exact .suspend
    | tick => exact .tick (ih _)
    | output => exact .output (ih _)
    | heap => exact .heap (fun _ => ih _)

theorem Agrees.bind {n : Nat} {left right : Computation α}
    (agreement : Agrees n left right) {thenLeft thenRight : α → Computation β}
    (next : ∀ value, Agrees n (thenLeft value) (thenRight value)) :
    Agrees n (left >>= thenLeft) (right >>= thenRight) := by
  induction agreement with
  | zero => exact .zero
  | pure => exact next _
  | invalid => exact .invalid
  | fault => exact .fault
  | terminate => exact .terminate
  | suspend => exact .suspend
  | tick _ ih => exact .tick (ih (fun value => (next value).weaken _ (by omega)))
  | output _ ih => exact .output (ih (fun value => (next value).weaken _ (by omega)))
  | heap _ ih => exact .heap (fun reply => ih reply (fun value => (next value).weaken _ (by omega)))

theorem Agrees.trace {heaps buffers : Type} {fuel : Nat} {left right : Computation α} (agreement : Agrees fuel left right)
    (next : α → TraceProgram) (machine : TraceMachine heaps buffers) (terminal : Bool)
    (blocks : Nat → Option TraceProgram) (memory : heaps) (stdout : buffers) :
    run_trace machine terminal blocks fuel (left.emit next) memory stdout =
      run_trace machine terminal blocks fuel (right.emit next) memory stdout := by
  induction agreement generalizing memory stdout with
  | zero | pure | invalid | fault | terminate | suspend => rfl
  | tick _ ih => exact ih _ _
  | output _ ih => exact ih _ _
  | heap _ ih =>
    simp only [Computation.emit, run_trace]
    split
    · rfl
    · exact ih _ _ _

private theorem evaluate_agrees (first second : Calls) (fuel : Nat)
    (calls : ∀ name values, Agrees fuel (first name values) (second name values))
    (locals : Locals) (expression : Expression) :
    Agrees fuel (expression.evaluate first locals) (expression.evaluate second locals) := by
  induction expression with
  | literal | nullPointer | slotAddress | globalAddress | emptyArguments => exact .refl _ _
  | load _ _ ih | cast _ _ ih | field _ _ ih | logicalNot _ ih | put _ ih | release _ ih | exit _ ih =>
    exact ih.bind (fun _ => .refl _ _)
  | offset _ _ _ il ir | assign _ _ _ il ir | scalar _ _ _ _ il ir | copyRecord _ _ _ _ il ir =>
    exact il.bind (fun _ => ir.bind (fun _ => .refl _ _))
  | pointerCompare _ _ _ il ir =>
    exact il.bind (fun _ => ir.bind (fun _ => .refl _ _))
  | logic _ _ _ il ir =>
    apply il.bind
    intro value
    split
    · exact ir.bind (fun _ => .refl _ _)
    · exact .refl _ _
  | allocate _ ih => exact ih.bind (fun _ => (Agrees.refl _ _).bind (fun _ => .refl _ _))
  | move _ _ _ idst isrc isize =>
    exact idst.bind (fun _ => isrc.bind (fun _ => isize.bind (fun _ => .refl _ _)))
  | call name _ _ ih =>
    exact ih.bind (fun _ => (Agrees.refl _ _).bind (fun actuals =>
      (calls name actuals).bind (fun _ => .refl _ _)))
  | argument _ _ _ iv ir =>
    exact iv.bind (fun _ => (Agrees.refl _ _).bind (fun _ =>
      ir.bind (fun _ => (Agrees.refl _ _).bind (fun _ => .refl _ _))))

private theorem init_stores_agree (first second : Calls) (fuel : Nat)
    (calls : ∀ name values, Agrees fuel (first name values) (second name values))
    (locals : Locals) (base : Value) (stores : List Initialiser) :
    Agrees fuel (initialise_stores first locals base stores) (initialise_stores second locals base stores) := by
  induction stores with
  | nil => exact .pure
  | cons init rest later =>
    exact (evaluate_agrees first second fuel calls locals init.value).bind (fun _ =>
      (Agrees.refl _ _).bind (fun _ => (Agrees.refl _ _).bind (fun _ => later)))

private theorem sequence_agrees {fuel : Nat} {first other rest tail : Computation Flow}
    (head : Agrees fuel first other) (later : Agrees fuel rest tail) :
    Agrees fuel (sequence first rest) (sequence other tail) := by
  apply head.bind
  intro flow
  cases flow
  · exact later
  all_goals exact .pure

private theorem loop_agrees (post : Bool) (fuel left right : Nat)
    (enough : fuel ≤ left) (alsoEnough : fuel ≤ right)
    {testFirst testSecond : Computation Value} {bodyFirst bodySecond : Computation Flow}
    {advanceFirst advanceSecond : Computation Value}
    (condition : Agrees fuel testFirst testSecond) (body : Agrees fuel bodyFirst bodySecond)
    (advance : Agrees fuel advanceFirst advanceSecond) :
    Agrees fuel (execute_loop post testFirst bodyFirst advanceFirst left)
      (execute_loop post testSecond bodySecond advanceSecond right) := by
  induction fuel generalizing left right with
  | zero => exact .zero
  | succ fuel ih =>
    cases left with
    | zero => omega
    | succ left =>
      cases right with
      | zero => omega
      | succ right =>
        have condition := condition.weaken fuel (Nat.le_succ _)
        have body := body.weaken fuel (Nat.le_succ _)
        have advance := advance.weaken fuel (Nat.le_succ _)
        have restartLoop := ih left right (by omega) (by omega) condition body advance
        have test (tested : Value) {yes no : Computation Flow} (proceed : Agrees fuel yes no) :
            Agrees fuel (if truth tested then yes else pure .next) (if truth tested then no else pure .next) := by
          split
          · exact proceed
          · exact .pure
        have iterate {first second : Computation Flow} (again : Agrees fuel first second) :
            Agrees fuel
              (bodyFirst >>= fun flow => match flow with
                | .returned value => pure (.returned value)
                | .stop => pure .next
                | .next | .restart => first)
              (bodySecond >>= fun flow => match flow with
                | .returned value => pure (.returned value)
                | .stop => pure .next
                | .next | .restart => second) := by
          apply body.bind
          intro flow
          cases flow
          · exact again
          · exact .pure
          · exact again
          · exact .pure
        apply Agrees.tick
        cases post
        · exact condition.bind (fun value => test value (iterate (advance.bind (fun _ => restartLoop))))
        · exact iterate (condition.bind (fun value => test value restartLoop))

private theorem execute_agrees (first second : Calls) (fuel : Nat)
    (calls : ∀ name values, Agrees fuel (first name values) (second name values))
    (locals : Locals) (statements : Statement) (left right : Nat)
    (enough : fuel ≤ left) (alsoEnough : fuel ≤ right) :
    Agrees fuel (execute first locals left statements) (execute second locals right statements) := by
  have expression := evaluate_agrees first second fuel calls locals
  induction statements with
  | empty | skip | stop | restart => exact .pure
  | gotoLabel | indirect | label | select | caseOf => exact .invalid
  | sequence first rest firstAgrees restAgrees => exact sequence_agrees firstAgrees restAgrees
  | block body agrees => exact agrees
  | initialise slot ty value | initialiseCopy slot value ty _ =>
    exact (Agrees.refl _ _).bind (fun _ => (expression value).bind (fun _ =>
      (Agrees.refl _ _).bind (fun _ => .pure)))
  | initialiseAggregate slot width stores =>
    exact (Agrees.refl _ _).bind (fun base => (Agrees.refl _ _).bind (fun _ =>
      (init_stores_agree first second fuel calls locals base stores).bind (fun _ => .pure)))
  | discard expr | result expr => exact (expression expr).bind (fun _ => .pure)
  | branch condition yes no yesAgrees noAgrees =>
    apply (expression condition).bind
    intro tested
    split
    · exact yesAgrees
    · exact noAgrees
  | whileDo condition body agrees =>
    exact loop_agrees false fuel left right enough alsoEnough (expression condition) agrees .pure
  | doWhile body condition agrees =>
    exact loop_agrees true fuel left right enough alsoEnough (expression condition) agrees .pure
  | forDo initial condition body advance initialAgrees bodyAgrees =>
    exact sequence_agrees initialAgrees (loop_agrees false fuel left right enough alsoEnough
      (expression _) bodyAgrees (expression _))

private theorem label_agrees (first second : Calls) (fuel : Nat)
    (calls : ∀ name values, Agrees fuel (first name values) (second name values))
    (locals : Locals) (choice : LabelChoice) :
    Agrees fuel (choice.evaluate first locals) (choice.evaluate second locals) := by
  induction choice with
  | address => exact .pure
  | conditional condition yes no chosen other =>
    apply (evaluate_agrees first second fuel calls locals condition).bind
    intro value
    split
    · exact chosen
    · exact other

private theorem block_agrees (first second : Calls) (fuel : Nat)
    (calls : ∀ name values, Agrees fuel (first name values) (second name values))
    (locals : Locals) (block : Block) (left right : Nat) (enough : fuel ≤ left) (alsoEnough : fuel ≤ right) :
    Agrees fuel (block.evaluate first locals left) (block.evaluate second locals right) := by
  obtain ⟨operation, redirect⟩ := block
  cases operation with
  | finish | escape | jump => exact .pure
  | branch condition yes no =>
    exact (evaluate_agrees first second fuel calls locals condition).bind (fun _ => .pure)
  | select selector entries =>
    exact (evaluate_agrees first second fuel calls locals selector).bind (fun value =>
      (Agrees.refl _ (integer value)).bind (fun _ => .pure))
  | indirect choice destinations =>
    exact (label_agrees first second fuel calls locals choice).bind (fun _ => .refl _ _)
  | run statement next =>
    exact (execute_agrees first second fuel calls locals statement left right enough alsoEnough).bind (fun _ => .pure)

private theorem dispatch_agrees (dispatch : Dispatch) (first second : Calls) (locals : Locals)
    (fuel left right leftSteps rightSteps index : Nat) (leftDepth : fuel ≤ left) (rightDepth : fuel ≤ right)
    (enough : fuel ≤ leftSteps) (alsoEnough : fuel ≤ rightSteps)
    (calls : ∀ name values, Agrees fuel (first name values) (second name values)) :
    Agrees fuel (execute_dispatch dispatch first locals left leftSteps index)
      (execute_dispatch dispatch second locals right rightSteps index) := by
  induction fuel generalizing leftSteps rightSteps index with
  | zero => exact .zero
  | succ fuel ih =>
    cases leftSteps with
    | zero => omega
    | succ leftSteps =>
      cases rightSteps with
      | zero => omega
      | succ rightSteps =>
        have calls' name values := (calls name values).weaken fuel (Nat.le_succ _)
        simp only [execute_dispatch]
        apply Agrees.tick
        cases found : dispatch.blocks[index]? with
        | none => exact .invalid
        | some block =>
          apply (block_agrees first second fuel calls' locals block left right (by omega) (by omega)).bind
          intro route
          cases route with
          | exit flow => exact .pure
          | jump target => exact ih leftSteps rightSteps target (by omega) (by omega) (by omega) (by omega) calls'

private theorem procedure_agrees (first second : Calls) (fuel : Nat)
    (calls : ∀ name values, Agrees fuel (first name values) (second name values))
    (locals : Locals) (procedure : Procedure) (left right : Nat) (enough : fuel ≤ left) (alsoEnough : fuel ≤ right) :
    Agrees fuel (procedure.execute first locals left) (procedure.execute second locals right) := by
  unfold Procedure.execute
  cases procedure.dispatch with
  | none => exact execute_agrees first second fuel calls locals procedure.statements left right enough alsoEnough
  | some dispatch =>
    exact dispatch_agrees dispatch first second locals fuel left right left right dispatch.entry
      enough alsoEnough enough alsoEnough calls

theorem calls_stabilise (program : Program) (globals : Globals) (fuel depth larger : Nat) (name : String) (values : List Value)
    (enough : fuel ≤ depth) (alsoEnough : fuel ≤ larger) :
    Agrees fuel (source_calls program globals depth name values) (source_calls program globals larger name values) := by
  induction fuel generalizing depth larger name values with
  | zero => exact .zero
  | succ fuel ih =>
    cases depth with
    | zero => omega
    | succ depth =>
      cases larger with
      | zero => omega
      | succ larger =>
        apply Agrees.tick
        cases found : program.lookup name with
        | none => exact .invalid
        | some procedure =>
          apply (Agrees.refl fuel (procedure.frame globals values)).bind
          intro locals
          exact (procedure_agrees _ _ fuel (fun f args => ih depth larger f args (by omega) (by omega))
            locals procedure depth larger (by omega) (by omega)).bind (fun _ => .refl _ _)

theorem trace_depth_stable (program : Program) (fuel depth larger : Nat) (invocation : Invocation)
    (enough : fuel ≤ depth) (alsoEnough : fuel ≤ larger) (machine : TraceMachine heap buffer)
    (terminal : Bool) (memory : heap) (stdout : buffer) :
    run_trace machine terminal blocks fuel (program.target depth invocation) memory stdout =
    run_trace machine terminal blocks fuel (program.target larger invocation) memory stdout := by
  rw [lower_program_correct, lower_program_correct]
  apply Agrees.trace _ .finish machine terminal blocks memory stdout
  exact (Agrees.refl fuel program.startup).bind (fun globals => (Agrees.refl fuel (argument_vector invocation)).bind fun arguments =>
    (calls_stabilise program globals fuel depth larger "main" (program.entry_arguments arguments) enough alsoEnough).bind
      (fun _ => .refl _ _))

theorem observation_completed (program : Program) (terminal : Bool) (invocation : Invocation) (fuel larger : Nat)
    (enough : fuel ≤ larger) (completed : (program.observation fuel terminal invocation).1 ≠ .paused) :
    program.observation larger terminal invocation = program.observation fuel terminal invocation := by
  unfold Program.observation at completed ⊢
  let memory : HeapImage := ⟨[], ⟨1, 4096⟩⟩
  let stdout : StdoutBuffer := ⟨[], [], 0, true⟩
  have same := trace_depth_stable program fuel fuel larger invocation (Nat.le_refl _) enough
    sparse_machine terminal memory stdout
  change (run_trace sparse_machine terminal blocks fuel (program.target fuel invocation) memory stdout).outcome ≠ .paused at completed
  rw [same] at completed ⊢
  rw [run_trace_completed sparse_machine terminal blocks fuel larger (program.target larger invocation) memory stdout enough completed]

theorem observation_output_prefix (program : Program) (terminal : Bool) (invocation : Invocation) (fuel larger : Nat)
    (enough : fuel ≤ larger) :
    (program.observation fuel terminal invocation).2 <+: (program.observation larger terminal invocation).2 := by
  by_cases complete : (program.observation fuel terminal invocation).1 ≠ .paused
  · rw [observation_completed program terminal invocation fuel larger enough complete]
    exact ⟨[], List.append_nil _⟩
  have paused : (program.observation fuel terminal invocation).1 = .paused := by simpa using complete
  let heap : HeapImage := ⟨[], ⟨1, 4096⟩⟩
  let stdout : StdoutBuffer := ⟨[], [], 0, true⟩
  have source (steps : Nat) : program.observation steps terminal invocation = program.source_observation steps terminal invocation :=
    prefix_refines program terminal steps invocation heap stdout rfl id (fun _ _ same => same)
  rw [source fuel, source larger]
  rw [source fuel] at paused
  unfold Program.source_observation at paused ⊢
  let memory : HeapState := ⟨fun _ => none, ⟨1, 4096⟩⟩
  let output : StdoutState := ⟨[], [], true⟩
  let first := run_trace abstract_machine terminal blocks fuel (program.target fuel invocation) memory output
  let last := run_trace abstract_machine terminal blocks larger (program.target larger invocation) memory output
  rw [← lower_program_correct, ← lower_program_correct]
  rw [← lower_program_correct] at paused
  change first.outcome = .paused at paused
  change first.observation.2 <+: last.observation.2
  have smaller := trace_depth_stable program fuel fuel larger invocation (Nat.le_refl _) enough
    abstract_machine terminal memory output
  have monotone := trace_visible_monotone terminal blocks fuel (larger - fuel) (program.target larger invocation) memory output
  rw [Nat.add_sub_cancel' enough, ← smaller] at monotone
  change first.stdout.visible <+: last.stdout.visible at monotone
  simp only [TraceResult.observation, paused]
  cases last.outcome with
  | paused | fault => exact monotone
  | returned => exact monotone.trans ⟨last.stdout.pending, rfl⟩

theorem completed_observations_unique (program : Program) (terminal : Bool) (invocation : Invocation)
    (first second : TraceOutcome × List UInt8)
    (left : Observes (fun steps => program.observation steps terminal invocation) first)
    (right : Observes (fun steps => program.observation steps terminal invocation) second) : first = second := by
  obtain ⟨firstDone, firstFuel, firstRun⟩ := left
  obtain ⟨secondDone, secondFuel, secondRun⟩ := right
  change program.observation firstFuel terminal invocation = first at firstRun
  change program.observation secondFuel terminal invocation = second at secondRun
  have firstCompleted : (program.observation firstFuel terminal invocation).1 ≠ .paused := by
    rw [firstRun]
    exact firstDone
  have secondCompleted : (program.observation secondFuel terminal invocation).1 ≠ .paused := by
    rw [secondRun]
    exact secondDone
  have firstStable := observation_completed program terminal invocation firstFuel (max firstFuel secondFuel)
    (Nat.le_max_left _ _) firstCompleted
  have secondStable := observation_completed program terminal invocation secondFuel (max firstFuel secondFuel)
    (Nat.le_max_right _ _) secondCompleted
  exact firstRun.symm.trans (firstStable.symm.trans (secondStable.trans secondRun))

private def par (s : String) : String := "(" ++ s ++ ")"

private def quoted (s : String) : String := "\"" ++ s ++ "\""

private def slot_name (names : List String) (slot : Nat) : String :=
  quoted (names[slot]?.getD "")

private def invoke (name result : String) (arguments : List (TypeCode × String)) : String :=
  "invoke " ++ result ++ " (function " ++ quoted name ++ ") [" ++
  String.intercalate ", " (arguments.map fun (ty, expr) => par ("marshal " ++ ty.haskell ++ " <$> " ++ par expr)) ++ "]"

private def aggregate_type (width alignment : Nat) : String :=
  par ("AggregateType " ++ toString width ++ " " ++ toString alignment)

private def aggregate_load (address : String) (width alignment : Nat) : String :=
  par (address ++ " >>= load " ++ aggregate_type width alignment)

def Expression.haskell (names : List String) : Expression → String
  | .literal n => "pure (Number " ++ par (toString n) ++ ")"
  | .nullPointer => "pure nullPointer"
  | .slotAddress slot => "variable " ++ slot_name names slot
  | .globalAddress name => "variable " ++ quoted name
  | .load ty address => par (address.haskell names ++ " >>= load " ++ ty.haskell)
  | .cast ty operand => par ("cast " ++ ty.haskell ++ " <$> " ++ par (operand.haskell names))
  | .offset base index stride => "binary \"+\" 64 False " ++ toString stride ++ " " ++
    par (base.haskell names) ++ " " ++ par (index.haskell names)
  | .field base displacement => par ("offset " ++ toString displacement ++ " <$> " ++ par (base.haskell names))
  | .logicalNot operand => "unary \"!\" (IntegerType 32 True) " ++ par (operand.haskell names)
  | .logic conjunction lhs rhs => "logic " ++ (if conjunction then "True " else "False ") ++
    par (lhs.haskell names) ++ " " ++ par (rhs.haskell names)
  | .pointerCompare equality lhs rhs => "binary " ++ quoted (if equality then "==" else "!=") ++
    " 64 False 1 " ++ par (lhs.haskell names) ++ " " ++ par (rhs.haskell names)
  | .allocate size => invoke "malloc" "(Just PointerType)" [(.size, size.haskell names)]
  | .move dst src size => invoke "memmove" "(Just PointerType)"
    [(.pointer, dst.haskell names), (.pointer, src.haskell names), (.size, size.haskell names)]
  | .copyRecord dst src width alignment =>
    "assign " ++ aggregate_type width alignment ++ " " ++ par (dst.haskell names) ++ " " ++
      par (aggregate_load (src.haskell names) width alignment)
  | .put value => invoke "putchar" "(Just (IntegerType 32 True))" [(.integer, value.haskell names)]
  | .release address => invoke "free" "Nothing" [(.pointer, address.haskell names)]
  | .exit status => invoke "exit" "Nothing" [(.integer, status.haskell names)]
  | .assign ty address value =>
    "assign " ++ ty.haskell ++ " " ++ par (address.haskell names) ++ " " ++ par (value.haskell names)

  | .scalar op ty left right =>
    "binary " ++ quoted op.symbol ++ " " ++ toString (8 * ty.width) ++ (if ty.signed then " True 1 " else " False 1 ") ++
      par (left.haskell names) ++ " " ++ par (right.haskell names)
  | .call name ty arguments =>
    "invoke " ++ par ("Just " ++ ty.haskell) ++ " (function " ++ quoted name ++ ") [" ++ arguments.haskell names ++ "]"
  | .emptyArguments => ""
  | .argument ty value rest =>
    let tail := rest.haskell names
    par ("marshal " ++ ty.haskell ++ " <$> " ++ par (value.haskell names)) ++
      (if tail.isEmpty then "" else ", " ++ tail)

private def flow (body : String) : String := "atFlow \"@\" " ++ par body

private def return_code (expr : String) : String := "Return <$> " ++ par expr

private def Initialiser.haskell (names : List String) (init : Initialiser) : String :=
  let address := (init.offset.map fun displacement => par ("offset " ++ toString displacement ++ " p")).getD "p"
  par (init.value.haskell names ++ " >>= store " ++ init.ty.haskell ++ " " ++ address ++ " >> pure ()")

def Statement.haskell (names : List String) : Statement → String
  | .empty => ""
  | .sequence first rest =>
    let tail := rest.haskell names
    par (first.haskell names) ++ (if tail.isEmpty then "" else ", " ++ tail)
  | .block body => flow ("chain [" ++ body.haskell names ++ "]")
  | .skip => flow "pure Next"
  | .initialise slot ty expr =>
    flow ("chain [(do { p <- variable " ++ slot_name names slot ++ "; " ++
      par (expr.haskell names ++ " >>= store " ++ ty.haskell ++ " p >> pure ()") ++ "; pure Next })]")
  | .initialiseAggregate slot width stores =>
    let setup := ["p <- variable " ++ slot_name names slot, "clear " ++ toString width ++ " p"]
    flow ("chain [(do { " ++ String.intercalate "; " (setup ++ (stores.map (Initialiser.haskell names)) ++ ["pure Next"]) ++ " })]")
  | .initialiseCopy slot source width alignment =>
    flow ("chain [(do { p <- variable " ++ slot_name names slot ++ "; " ++
      par (aggregate_load (source.haskell names) width alignment ++ " >>= store " ++
        aggregate_type width alignment ++ " p >> pure ()") ++ "; pure Next })]")
  | .discard expr => flow ("discard " ++ par (expr.haskell names))
  | .branch condition yes no =>
    let fallback := match no with
      | .empty => "pure Next"
      | _ => no.haskell names
    flow ("branch " ++ par (condition.haskell names) ++ " " ++ par (yes.haskell names) ++ " " ++ par fallback)
  | .whileDo condition body =>
    flow ("loop " ++ par (condition.haskell names) ++ " " ++ par (body.haskell names) ++ " (pure (Number 0))")
  | .doWhile body condition =>
    flow ("postloop " ++ par (body.haskell names) ++ " " ++ par (condition.haskell names))
  | .forDo initial condition body advance =>
    let test := (condition.map (·.haskell names)).getD "pure (Number 1)"
    let step := (advance.map (·.haskell names)).getD "pure (Number 0)"
    flow ("chain [" ++ par (initial.haskell names) ++ ", loop " ++ par test ++ " " ++ par (body.haskell names) ++
      " " ++ par step ++ "]")
  | .stop => flow "pure Break"
  | .restart => flow "pure Continue"
  | .result expr => flow (return_code (expr.haskell names))
  | .gotoLabel _ | .indirect _ | .label .. | .select .. | .caseOf .. => ""

private def jump_code (target : Nat) : String := par ("pure " ++ par ("Jump " ++ toString target))

private def LabelChoice.haskell (names : List String) : LabelChoice → String
  | .address symbol => "function " ++ quoted symbol
  | .conditional condition yes no =>
    par (condition.haskell names ++ " >>= \\v -> if truth v then " ++ par (yes.haskell names) ++
      " else " ++ par (no.haskell names))

private def BlockAction.haskell (names : List String) : BlockAction → String
  | .finish => "pure Next"
  | .escape stop => if stop then "pure Break" else "pure Continue"
  | .jump target => jump_code target
  | .branch condition yes no =>
    "branch " ++ par (condition.haskell names) ++ " " ++ jump_code yes ++ " " ++ jump_code no
  | .select selector entries =>
    let arm (entry : SwitchEntry) :=
      let label := match entry.bounds with
        | none => "Nothing"
        | some (lower, upper) =>
          "Just " ++ par (par ((Expression.literal lower).haskell names) ++ ", " ++ par ((Expression.literal upper).haskell names))
      par (label ++ ", " ++ jump_code entry.target)
    "selection " ++ par (selector.haskell names) ++ " [" ++ String.intercalate ", " (entries.map arm) ++ "]"
  | .indirect choice destinations =>
    let entries := destinations.map fun (name, target) => par (quoted name ++ ", " ++ toString target)
    "indirectJump [" ++ String.intercalate ", " entries ++ "] " ++ par (choice.haskell names)
  | .run statement next => "chain [" ++ par (statement.haskell names) ++ ", " ++ jump_code next ++ "]"

private def Block.haskell (names : List String) (block : Block) : String :=
  let action := block.action.haskell names
  match block.redirect with
  | none => action
  | some (stop, restart) => "redirectFlow " ++ toString stop ++ " " ++ toString restart ++ " " ++ par (flow action)

private def Dispatch.haskell (names : List String) (dispatch : Dispatch) : String :=
  "dispatch " ++ dispatch.name ++ " [" ++ String.intercalate ", " (dispatch.blocks.map (par ∘ Block.haskell names)) ++ "]"

private def Dispatch.declaration (dispatch : Dispatch) : String :=
  let row (targets : List Nat) := "[" ++ String.intercalate ", " (targets.map toString) ++ "]"
  dispatch.name ++ " :: (Int, [[Int]])\n" ++ dispatch.name ++ " = " ++
    par (toString dispatch.entry ++ ", [" ++ String.intercalate ", " (dispatch.graph.successors.map row) ++ "]") ++ "\n"

private def binding (stem name : String) : String :=
  let digits := "0123456789abcdef".toList.toArray
  name.toUTF8.toList.foldl (fun text byte =>
    (text.push digits[byte.toNat / 16]!).push digits[byte.toNat % 16]!) (stem ++ "_")

def Procedure.haskell (procedure : Procedure) : String :=
  let symbol := binding "f" procedure.name
  let count := procedure.parameters.length
  let arguments := (List.range count).map fun slot => "a" ++ toString slot
  let pattern := if count = 0 then "_" else par (String.intercalate " : " (arguments ++ ["_"]))
  let parameters := procedure.parameters.zipIdx |>.map fun (ty, slot) =>
    "parameter " ++ slot_name procedure.slots slot ++ " " ++ ty.haskell ++ " a" ++ toString slot
  let locals := procedure.locals.zipIdx |>.map fun (width, slot) =>
    "at \"@\" (void (declare " ++ slot_name procedure.slots (count + slot) ++ " " ++ toString width ++ "))"
  let body := match procedure.dispatch with
    | none => procedure.statements.haskell procedure.slots
    | some dispatch => dispatch.haskell procedure.slots
  let mismatch := if count = 0 then "" else
    symbol ++ " _ = panic " ++ quoted ("wrong argument count for " ++ procedure.name) ++ "\n"
  symbol ++ " :: [Value] -> R Value\n" ++ symbol ++ " " ++ pattern ++ " = at \"@\" (marshal " ++
    procedure.resultType.haskell ++ " <$> (frame (do { " ++
    String.intercalate "; " (parameters ++ locals ++ [body]) ++ " })))\n" ++ mismatch ++ "\n"

private def UnitBody.initialiser (unit : UnitBody) (phase : String) : String :=
  if unit.namespaceName.isEmpty then phase else phase ++ "_" ++ binding "unit" unit.namespaceName

private def UnitBody.haskell (unit : UnitBody) : String :=
  let alloc := unit.globals.map fun object =>
    "  void (global " ++ quoted object.name ++ " " ++ toString object.width ++ ")\n"
  let stores := unit.globals.filterMap fun object =>
    let actions := object.initialisers.map (Initialiser.haskell [])
    if actions.isEmpty then none else some <|
      "  do { p <- variable " ++ quoted object.name ++ "; " ++ String.intercalate "; " actions ++ " }\n"
  let actions := [("allocateGlobals", alloc), ("initialiseGlobals", stores),
    ("allocateThread", []), ("initialiseThread", [])]
  let initialisers := actions.map fun (phase, body) =>
    let name := unit.initialiser phase
    name ++ " :: R ()\n" ++ name ++ " = do\n" ++ String.join body ++ "  pure ()\n\n"
  String.join (unit.procedures.map Procedure.haskell) ++ String.join initialisers ++
    String.join ((unit.procedures.filterMap (·.dispatch)).map Dispatch.declaration)

private def Program.phase (program : Program) (name : String) : String :=
  let allocate := program.units.map fun unit => unit.initialiser ("allocate" ++ name)
  let initialise := program.units.map fun unit => unit.initialiser ("initialise" ++ name)
  "(do { " ++ String.intercalate "; " (allocate ++ initialise) ++ " })"

def Program.moduleBody (program : Program) : String :=
  let entries := program.procedures.map fun procedure => par (quoted procedure.name ++ ", " ++ binding "f" procedure.name)
  let labels := program.labels
  String.join (program.units.map UnitBody.haskell) ++
    "main :: IO ()\nmain = execute [" ++ String.intercalate ", " entries ++
    "] [" ++ String.intercalate ", " (labels.map quoted) ++ "] False " ++ program.phase "Globals" ++
    " " ++ program.phase "Thread" ++ "\n"

end Heresy.Ordinary

#print axioms Heresy.Ordinary.calls_correct
#print axioms Heresy.Ordinary.Procedure.control_correct
#print axioms Heresy.Ordinary.checked_computed_jump
#print axioms Heresy.Ordinary.lower_program_correct
#print axioms Heresy.Ordinary.prefix_refines
#print axioms Heresy.Ordinary.trace_depth_stable
#print axioms Heresy.Ordinary.observation_output_prefix
#print axioms Heresy.Ordinary.Invocation.decode_encoding
