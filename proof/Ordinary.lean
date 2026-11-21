import Runtime
import Execution

set_option warningAsError true

namespace Heresy

def operator_text : Operator → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .band => ".&."
  | .bor => ".|."
  | .bxor => "`xor`"

def render_expression (render_slot : Nat → String) (strict : Bool) : Target → String
  | .constant value => toString value
  | .parameter index => render_slot index
  | .binary operator left right =>
    let left := "(" ++ render_expression render_slot strict left ++ ")"
    let right := "(" ++ render_expression render_slot strict right ++ ")"
    let operator := operator_text operator
    if strict then "strictOperands (\\left right -> left " ++ operator ++ " right) " ++ left ++ " " ++ right
    else left ++ " " ++ operator ++ " " ++ right
  | .wrap width expression =>
    "normalise " ++ toString width ++ " False (" ++ render_expression render_slot strict expression ++ ")"
  | .conditional condition yes no =>
    "if (" ++ render_expression render_slot strict condition ++ ") == 0 then (" ++ render_expression render_slot strict no ++
      ") else (" ++ render_expression render_slot strict yes ++ ")"
  | .invoke slot arguments =>
    "(" ++ String.intercalate " " (("h_" ++ toString slot) ::
      arguments.map (fun value => "(" ++ render_expression render_slot strict value ++ ")")) ++ ")"

def render_target := render_expression (fun index => "x" ++ toString index) false

end Heresy

namespace Heresy.Ordinary

inductive AtomicMode where
  | bytes | capability | copy
  deriving DecidableEq, Repr

def AtomicMode.haskell : AtomicMode → String
  | .bytes => "AtomicBytes" | .capability => "AtomicCapability" | .copy => "AtomicCopy"

inductive TypeCode where
  | pointer | byte | signedByte | integer | unsignedInt | size
  | short | unsignedShort | long | wide | unsignedWide | extended | binary32 | binary64
  | complex32 | complex64 | complex80
  | bitField (shift widthMinusOne : Nat) (isSigned : Bool)
  | aggregate (lastByte alignment : Nat)
  | atomicRecord (lastByte alignment lastStorage : Nat) (mode : AtomicMode)
  deriving DecidableEq, Repr

private def TypeCode.aggregate_assignment : TypeCode → Bool
  | .aggregate .. | .atomicRecord .. => true
  | _ => false

def TypeCode.component : TypeCode → Option TypeCode
  | .complex32 => some .binary32
  | .complex64 => some .binary64
  | .complex80 => some .extended
  | _ => none

def TypeCode.haskell : TypeCode → String
  | .pointer => "PointerType"
  | .byte => "(IntegerType 8 False)"
  | .signedByte => "(IntegerType 8 True)"
  | .integer => "(IntegerType 32 True)"
  | .unsignedInt => "(IntegerType 32 False)"
  | .size => "(IntegerType 64 False)"
  | .short => "(IntegerType 16 True)"
  | .unsignedShort => "(IntegerType 16 False)"
  | .long => "(IntegerType 64 True)"
  | .binary32 => "(FloatingType 32)"
  | .binary64 => "(FloatingType 64)"
  | .extended => "(FloatingType 80)"
  | .complex32 => "(ComplexType 32)"
  | .complex64 => "(ComplexType 64)"
  | .complex80 => "(ComplexType 80)"
  | .wide => "(IntegerType 128 True)"
  | .unsignedWide => "(IntegerType 128 False)"
  | .bitField shift width signed =>
    "(BitField " ++ toString shift ++ " " ++ toString (width + 1) ++ (if signed then " True)" else " False)")
  | .aggregate lastByte alignment =>
    "(AggregateType " ++ toString (lastByte + 1) ++ " " ++ toString alignment ++ ")"

  | .atomicRecord last alignment storage mode =>
    "(AtomicAggregate " ++ toString (storage + 1) ++ " (AggregateType " ++ toString (last + 1) ++ " " ++
      toString alignment ++ ") " ++ mode.haskell ++ ")"

private def TypeCode.atomic_haskell (ty : TypeCode) := match ty with
  | .atomicRecord .. => ty.haskell
  | _ => "(AtomicType " ++ ty.haskell ++ ")"

def TypeCode.width : TypeCode → Nat
  | .complex80 => 32
  | .complex64 => 16
  | .complex32 | .pointer | .size | .long | .binary64 => 8
  | .byte | .signedByte => 1
  | .short | .unsignedShort => 2
  | .integer | .unsignedInt | .binary32 => 4
  | .wide | .unsignedWide | .extended => 16
  | .bitField shift width _ => bitfield_bytes shift (width + 1)
  | .aggregate lastByte _ | .atomicRecord _ _ lastByte _ => lastByte + 1

def TypeCode.signed : TypeCode → Bool
  | .integer | .signedByte | .short | .long | .wide => true
  | .bitField _ _ signed => signed
  | _ => false

private theorem TypeCode.width_positive (ty : TypeCode) : 0 < ty.width := by
  cases ty <;> first | decide | simp only [TypeCode.width, bitfield_bytes]; omega

def TypeCode.alignment (ty : TypeCode) : Nat :=
  match ty with
  | .aggregate _ alignment => max 1 alignment
  | .atomicRecord _ alignment storage _ => max 1 (if storage < 16 then max alignment (storage + 1) else alignment)
  | .complex32 => 4 | .complex64 => 8 | .complex80 => 16
  | _ => ty.width

private theorem TypeCode.alignment_positive (ty : TypeCode) : 0 < ty.alignment := by
  unfold alignment
  split <;> first | decide | exact Nat.lt_of_lt_of_le (by decide) (Nat.le_max_left _ _) | exact ty.width_positive

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
    let offset := (aligned_slot cursor 0 field.ty.alignment).1
    let (placed, extent) := place_fields (offset + field.ty.width) fields
    (⟨field, offset, 0⟩ :: placed, extent)

private theorem placed_fields_valid (cursor : Nat) (fields : List FieldSpec) :
    let (placed, extent) := place_fields cursor fields
    cursor ≤ extent ∧ ∀ member ∈ placed, cursor ≤ member.offset ∧
      member.offset % member.spec.ty.alignment = 0 ∧ member.offset + member.spec.ty.width ≤ extent := by
  induction fields generalizing cursor with
  | nil => simp [place_fields]
  | cons field rest later =>
    let offset := (aligned_slot cursor 0 field.ty.alignment).1
    obtain ⟨after, _, aligned, _⟩ := aligned_slot_valid cursor 0 field.ty.alignment field.ty.alignment_positive
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
  original : String := ""
  deriving Repr

private def record_alignment (fields : List FieldSpec) : Nat :=
  max 1 ((fields.map fun field => field.ty.alignment).foldr max 0)

def record_layout (spelling : String) (fields : List FieldSpec) : RecordLayout :=
  let (placed, extent) := place_fields 0 fields
  let alignment := record_alignment fields
  ⟨spelling, placed, (aligned_slot extent 0 alignment).1, alignment, false, ""⟩

def union_layout (spelling : String) (fields : List FieldSpec) : RecordLayout :=
  let alignment := record_alignment fields
  let extent := (fields.map fun field => field.ty.width).foldr max 0
  ⟨spelling, fields.map (fun field => ⟨field, 0, 0⟩), (aligned_slot extent 0 alignment).1, alignment, true, ""⟩

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
  have positive : 0 < record_alignment fields := Nat.lt_of_lt_of_le (by decide) (Nat.le_max_left _ _)
  exact ⟨rfl, Nat.le_trans (field_width_le_max spec fields included) (aligned_slot_valid _ 0 _ positive).1⟩

theorem record_field_in_bounds (spelling : String) (fields : List FieldSpec) (field : Field)
    (present : field ∈ (record_layout spelling fields).fields) :
    field.offset % field.spec.ty.alignment = 0 ∧ field.offset + field.spec.ty.width ≤ (record_layout spelling fields).width := by
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
    let offset := (aligned_slot cursor 0 field.ty.alignment).1
    let next := offset + field.ty.width
    have tail := (placed_fields_valid next rest).2
    exact .cons (fun member present => (tail member present).1) (ih next)

theorem record_fields_ordered (spelling : String) (fields : List FieldSpec) :
    (record_layout spelling fields).fields.Pairwise (fun first later => first.offset + first.spec.ty.width ≤ later.offset) :=
  placed_fields_ordered 0 fields

private def member_position (cursor : Nat) (member : FieldSpec) : Nat :=
  let unit := 8 * member.ty.alignment
  if member.bits.isSome && cursor % unit + member.span ≤ unit then cursor
  else (aligned_slot cursor 0 unit).1

private theorem member_position_monotone (cursor : Nat) (member : FieldSpec) : cursor ≤ member_position cursor member := by
  simp only [member_position]
  split
  · exact Nat.le_refl _
  · exact (aligned_slot_valid cursor 0 _ (Nat.mul_pos (by decide) member.ty.alignment_positive)).1

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
  ⟨spelling, placed, (aligned_slot ((extent + 7) / 8) 0 alignment).1, alignment, false, ""⟩

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

def checked_packed_layout (spelling : String) (fields : List Field) (width : Nat) : Option RecordLayout :=
  if fields.all (fun field => decide (field.offset + field.access.width ≤ width)) &&
      decide (fields.Pairwise (fun first later => first.start_bit + first.spec.span ≤ later.start_bit)) then
    some ⟨spelling, fields, width, 1, false, ""⟩
  else none

theorem packed_layout_valid (spelling : String) (fields : List Field) (width : Nat) (layout : RecordLayout)
    (accepted : checked_packed_layout spelling fields width = some layout) :
    (∀ field ∈ layout.fields, field.offset + field.access.width ≤ layout.width) ∧
      layout.fields.Pairwise (fun first later => first.start_bit + first.spec.span ≤ later.start_bit) := by
  unfold checked_packed_layout at accepted
  split at accepted
  · rename_i valid
    cases accepted
    simpa only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using valid
  · contradiction

inductive ScalarOp where
  | add | sub | mul | eq | ne | lt | le | gt | ge
  | div | rem | band | bor | bxor | shl | shr
  deriving Repr

def ScalarOp.symbol : ScalarOp → String
  | .add => "+" | .sub => "-" | .mul => "*"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .div => "/" | .rem => "%" | .band => "&" | .bor => "|" | .bxor => "^" | .shl => "<<" | .shr => ">>"

inductive UnaryOp where
  | plus | minus | complement
  deriving Repr

def UnaryOp.symbol : UnaryOp → String
  | .plus => "+" | .minus => "-" | .complement => "~"

inductive PointerOp where
  | add | reversedAdd | subtract | difference
  deriving Repr

inductive LibraryCall where
  | synchronise (op : SyncOp)
  | printf | puts | hasCapability | isReadonly | upperBound | lowerBound | strlen | strcmp | calloc | memset | fopen | fread | fwrite | fclose
  deriving Repr

def LibraryCall.name : LibraryCall → String
  | .synchronise op => op.name
  | .printf => "printf"
  | .puts => "puts"
  | .hasCapability => "zhasvalidcap" | .isReadonly => "zis_readonly"
  | .upperBound => "zgetupper" | .lowerBound => "zgetlower"
  | .fopen => "fopen" | .fread => "fread" | .fwrite => "fwrite" | .fclose => "fclose"
  | .strlen => "strlen" | .strcmp => "strcmp" | .calloc => "calloc" | .memset => "memset"

inductive CopyCall where
  | memcpy | memmove
  deriving Repr

def TypeCode.floating : TypeCode → Bool
  | .binary32 | .binary64 | .extended => true
  | _ => false

def floating_bits (ty : TypeCode) (numerator denominator : Nat) : Nat := Id.run do
  let (fraction, bias, explicitBit) := match ty with
    | .binary32 => (23, 127, false)
    | .binary64 => (52, 1023, false)
    | _ => (63, 16383, true)
  let exponentUnit := 2 ^ (fraction + if explicitBit then 1 else 0)
  let leading := 2 ^ fraction
  let infinity := (2 * bias + 1) * exponentUnit + if explicitBit then leading else 0
  if denominator == 0 then return infinity
  if numerator == 0 then return 0
  let guess := (numerator.log2 : Int) - denominator.log2
  let exponent := if numerator * 2 ^ (-guess).toNat < denominator * 2 ^ guess.toNat then guess - 1 else guess
  let scale := max (1 - (bias : Int)) exponent
  let shift := (fraction : Int) - scale
  let rounded := nearest_coefficient (numerator * 2 ^ shift.toNat) (denominator * 2 ^ (-shift).toNat)
  let carry := rounded == 2 * leading
  let significand := if carry then leading else rounded
  let finalExponent := if carry then scale + 1 else scale
  if finalExponent > bias then return infinity
  let biased := if significand < leading then 0 else (finalExponent + bias).toNat
  return biased * exponentUnit + significand % exponentUnit

inductive AtomicOperation where
  | load | store | initialise
  | fetch (op : WordUpdate) (returnOld : Bool)
  | pointerStep (op : WordUpdate) (stride : Nat) (returnOld : Bool)
  deriving Repr

inductive TransferKind where
  | load | store | exchange
  deriving Repr

def TransferKind.name : TransferKind → String
  | .load => "load" | .store => "store" | .exchange => "exchange"

inductive Expression where
  | truncateReal (ty : TypeCode) (operand : Expression)
  | compound (slot width : Nat) (writes : Expression)
  | compoundStore (slot : Nat) (offsets : List Nat) (ty : TypeCode) (value rest : Expression)
  | compoundEnd (slot : Nat)
  | compareWord (ty : TypeCode) (target successOrder expected failureOrder desired : Expression) (indirect : Bool := false)
  | atomicTransfer (op : TransferKind) (ty : TypeCode) (target args : Expression)
  | atomic (op : AtomicOperation) (ty : TypeCode) (target ordering operand : Expression)
  | literal (value : Int)
  | floatingLiteral (ty : TypeCode) (spelling : String) (bits : Nat)
  | byteLiteral (value : UInt8)
  | string (bytes : List UInt8)
  | library (function : LibraryCall) (arguments : Expression)
  | sizeLiteral (value : Nat)
  | nullPointer
  | slotAddress (slot : Nat)
  | arrayAddress (slot : Nat)
  | globalAddress (name : String)
  | load (ty : TypeCode) (address : Expression)
  | cast (ty : TypeCode) (operand : Expression)
  | materialise (ty : TypeCode) (operand : Expression)
  | offset (left right : Expression) (stride : Nat) (op : PointerOp := .add)
  | field (base : Expression) (offset : Nat)
  | logicalNot (operand : Expression)
  | unary (op : UnaryOp) (ty : TypeCode) (operand : Expression)
  | logic (conjunction : Bool) (left right : Expression)
  | shared (common fallback : Expression) (test result : List TypeCode)
  | conditional (condition yes no : Expression)
  | weakDesired (weak value : Expression)
  | comma (left right : Expression)
  | pointerCompare (op : ScalarOp) (left right : Expression)
  | spawn (worker : String) (destination argument : Expression)
  | join (handle destination : Expression)
  | self
  | equal (left right : Expression)
  | allocate (size : Expression)
  | move (function : CopyCall) (destination source size : Expression)
  | put (value : Expression)
  | release (address : Expression)
  | exit (status : Expression)
  | assign (ty : TypeCode) (address value : Expression)
  | update (op : ScalarOp) (storage arithmetic : TypeCode) (returnOld : Bool) (address value : Expression)
      (stride : Nat := 1)
  | scalar (op : ScalarOp) (ty : TypeCode) (left right : Expression)
  | functionAddress (name : String) (index : Nat)
  | indirect (symbols : List String) (ty : Option TypeCode) (callee arguments : Expression)
  | call (name : String) (ty : Option TypeCode) (arguments : Expression)
  | emptyArguments
  | argument (ty : TypeCode) (value rest : Expression)
  | dimension (bound rest : Expression)
  | arrayExtent (width : Nat) (bounds : Expression)
  | arrayOffset (op : PointerOp) (indexing : Bool) (slot rank : Nat) (left right : Expression)
  | arrayUpdate (op : ScalarOp) (slot rank : Nat) (returnOld : Bool) (address value : Expression)
  | arraySize (slot rank : Nat) (place : Expression)
  | aliasSize (slot : Nat)
  | vaStart (place : Expression)
  | vaCopy (destination source : Expression)
  | vaArg (ty : TypeCode) (place : Expression)
  | vaEnd (place : Expression)
  | vaAvailable (place : Expression)
  | argumentArea
  deriving Repr

structure Initialiser where
  offsets : List Nat
  ty : TypeCode
  value : Expression
  deriving Repr

private def Initialiser.start_bit (init : Initialiser) : Nat := 8 * init.offsets.sum + init.ty.bit_shift

inductive LabelChoice where
  | address (identity : String)
  | loaded (expression : Expression) (registry targets : List String)
  | conditional (test : Expression) (yes no : LabelChoice)
  deriving Repr

def LabelChoice.symbols : LabelChoice → List String
  | .address name => [name]
  | .loaded _ _ targets => targets
  | .conditional _ yes no => yes.symbols ++ no.symbols

def Initialiser.fits (width : Nat) (stores : List Initialiser) : Bool :=
  stores.all (fun init => decide (init.offsets.sum + init.ty.width ≤ width)) &&
    decide (stores.Pairwise (fun first later => first.start_bit + first.ty.bit_width ≤ later.start_bit))

inductive RegisterOp where
  | mov | add | sub | adc | sbb | cmp | inc | dec | neg | inv | band | bor | bxor
  | shl | shr | sar | rol | ror | clc | stc | cmc | setc
  deriving Repr, BEq

def RegisterOp.symbol : RegisterOp → String
  | .mov => "mov" | .add => "+" | .sub => "-" | .adc => "adc" | .sbb => "sbb"
  | .cmp => "cmp" | .inc => "inc" | .dec => "dec" | .neg => "neg" | .inv => "not"
  | .band => "&" | .bor => "|" | .bxor => "^" | .shl => "shl" | .shr => "shr"
  | .sar => "sar" | .rol => "rol" | .ror => "ror" | .clc => "clc" | .stc => "stc"
  | .cmc => "cmc" | .setc => "setc"

structure RegisterInstruction where
  op : RegisterOp
  width : Nat
  destination : Nat
  source : Sum Nat Int
  deriving Repr

structure RegisterBlock where
  outputs : List (TypeCode × Bool)
  inputs : List Nat
  instructions : List RegisterInstruction
  deriving Repr

inductive Statement where
  | empty
  | sequence (first rest : Statement)
  | declarations (body : Statement)
  | block (body : Statement)
  | skip
  | arrayProbe
  | assembly (block : RegisterBlock) (operands : Expression)
  | declareArray (slot width : Nat) (bounds : Expression) (typeOnly : Bool := false)
  | arrayFromAlias (slot source : Nat)
  | initialiseArrayPointer (slot width : Nat) (bounds : Expression) (initializer : Option Expression)
  | uninitialised (slot : Nat)
  | initialiseAtomic (slot : Nat) (ty : TypeCode) (value : Expression)
  | initialise (slot : Nat) (ty : TypeCode) (value : Expression)
  | initialiseAggregate (slot width : Nat) (stores : List Initialiser) (result : Option TypeCode := none)
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
  | .empty | .skip | .arrayProbe | .assembly .. | .declareArray .. | .arrayFromAlias .. | .initialise .. | .initialiseAtomic .. | .initialiseAggregate _ _ _ none
  | .initialiseArrayPointer .. | .uninitialised _
  | .discard _ | .whileDo .. | .doWhile .. => { next := true }
  | .sequence first rest => first.exits.sequence rest.exits
  | .declarations body | .block body => body.exits
  | .branch _ yes no => yes.exits.join no.exits
  | .forDo initial .. => initial.exits.sequence { next := true }
  | .stop => { stop := true }
  | .restart => { restart := true }
  | .result _ | .initialiseAggregate _ _ _ (some _) => {}
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
  | .loaded expr registry _ => .ok (.loaded expr registry (labels.map Prod.snd))
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

structure ParameterShape where
  slot : Nat
  elementWidth : Nat
  skip : Nat
  bounds : Expression
  deriving Repr

structure Kernel where
  expression : Source

instance : Repr Kernel where
  reprPrec kernel _ := repr (render_target (Heresy.lower kernel.expression))

structure Procedure where
  name : String
  resultType : Option TypeCode
  parameters : List TypeCode
  locals : List (Option Nat)
  slots : List String
  statements : Statement
  dispatch : Option Dispatch := none
  shapes : List ParameterShape := []
  shapedLocals : Bool := false
  introspects : Bool := false
  kernel : Option Kernel := none
  deriving Repr

def Procedure.may_fall_through (procedure : Procedure) : Bool :=
  procedure.resultType.isNone || procedure.name == "main"

def Procedure.control_checked (procedure : Procedure) : Bool :=
  match procedure.dispatch with
  | none => procedure.statements.exits.allowed procedure.may_fall_through
  | some dispatch => dispatch.control_checked procedure.may_fall_through

theorem Procedure.valid_graph (procedure : Procedure) (checked : procedure.control_checked = true)
    (dispatch : Dispatch) (found : procedure.dispatch = some dispatch) : valid_dispatch dispatch.graph = true := by
  simp only [Procedure.control_checked, found, Dispatch.control_checked, Bool.and_eq_true] at checked
  exact checked.1

structure Global where
  name : String
  width : Nat
  initialisers : List Initialiser
  threadLocal : Bool := false
  readOnly : Bool := false
  deriving Repr

def Global.initialisers_fit (object : Global) : Bool :=
  Initialiser.fits object.width object.initialisers

theorem Global.initialiser_in_bounds (object : Global) (checked : object.initialisers_fit = true)
    (init : Initialiser) (present : init ∈ object.initialisers) :
    init.offsets.sum + init.ty.width ≤ object.width := by
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
  parallel : Bool := false
  deriving Repr

structure Invocation where
  program : List UInt8 := []
  arguments : List (List UInt8) := []
  files : List FileEvent := []
  deriving Repr

private def decode_strings (current : List UInt8) : List UInt8 → Option (List (List UInt8))
  | [] => if current.isEmpty then some [] else none
  | byte :: rest =>
    if byte == 0 then (current.reverse :: ·) <$> decode_strings [] rest
    else decode_strings (byte :: current) rest

def Invocation.decode (bytes : List UInt8) (files : List FileEvent := []) : Option Invocation := do
  let program :: arguments ← decode_strings [] bytes | none
  return ⟨program, arguments, files⟩

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
    Invocation.decode invocation.encoding invocation.files = some invocation := by
  cases invocation with
  | mk program arguments files =>
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
  | aggregate (width alignment : Nat) (image : AggregateImage Nat)
  | wideArgument (bits : Int)
  | extended (bits : Int)
  | ieee (wide : Bool) (bits : Int)
  | complex (ty : TypeCode) (real imaginary : Int)

inductive Computation (α : Type) where
  | pure (value : α)
  | tick (next : Computation α)
  | output (bytes : List (List UInt8)) (next : Computation α)
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
  | .output byte rest => .output byte (rest.emit next)
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
  | .integer word | .wideArgument word => word != 0
  | .ieee wide bits => unsigned (if wide then 63 else 31) bits != 0
  | .extended bits => unsigned 64 bits != 0 || unsigned 15 (bits / 2 ^ 64) == 32767
  | .complex ty real imag =>
    let nonzero := fun bits => match ty with
      | .complex80 => unsigned 64 bits != 0 || unsigned 15 (bits / 2 ^ 64) == 32767
      | .complex32 => unsigned 31 bits != 0
      | _ => unsigned 63 bits != 0
    nonzero real || nonzero imag
  | .pointer address => address.address != 0
  | .arguments _ | .aggregate .. => false

private def logical (test : Bool) : Value := .integer (if test then 1 else 0)

private def convert : TypeCode → Value → Computation Value
  | ty@(.complex32), value | ty@(.complex64), value | ty@(.complex80), value =>
    let half := 4 * ty.width
    let bits := if ty == .complex80 then 80 else half
    match value with
    | .integer word => pure (.complex ty (unsigned bits word) (unsigned bits (word / 2 ^ half)))
    | .complex source real imag => if source == ty then pure (.complex ty real imag) else .invalid
    | _ => .invalid
  | .pointer, value@(.pointer _) => pure value
  | .binary32, .integer bits | .binary32, .ieee false bits => pure (.ieee false (unsigned 32 bits))
  | .binary64, .integer bits | .binary64, .ieee true bits => pure (.ieee true (unsigned 64 bits))
  | .extended, .extended bits => pure (.extended (unsigned 80 bits))
  | .byte, .integer value => pure (.integer (unsigned 8 value))
  | .signedByte, .integer value => pure (.integer (signed 8 value))
  | .integer, .integer value => pure (.integer (signed 32 value))
  | .unsignedInt, .integer value => pure (.integer (unsigned 32 value))
  | .size, .integer value => pure (.integer (unsigned 64 value))
  | .short, .integer value => pure (.integer (signed 16 value))
  | .unsignedShort, .integer value => pure (.integer (unsigned 16 value))
  | .long, .integer value => pure (.integer (signed 64 value))
  | .wide, .integer value => pure (.integer (signed 128 value))
  | .unsignedWide, .integer value => pure (.integer (unsigned 128 value))
  | .bitField _ width isSigned, .integer value =>
    pure (.integer (if isSigned then signed (width + 1) value else unsigned (width + 1) value))
  | .atomicRecord lastByte _ _ _, value@(.aggregate actual _ _)
  | .aggregate lastByte _, value@(.aggregate actual _ _) =>
    if actual == lastByte + 1 then pure value else .fault .incompatibleAggregate
  | .aggregate .., _ | .atomicRecord .., _ => .fault .incompatibleAggregate
  | _, _ => .invalid

private def convert_result (ty : Option TypeCode) (value : Value) : Computation Value :=
  match ty with
  | none => pure (.integer 0)
  | some ty => convert ty value

private def marshal_argument (ty : TypeCode) (value : Value) : Computation Value :=
  match ty with
  | .pointer | .aggregate .. | .extended | .complex32 | .complex64 | .complex80 => convert ty value
  | .binary32 | .binary64 => do
    let .ieee _ bits ← convert ty value | .invalid
    pure (.integer bits)
  | .wide | .unsignedWide => do pure (.wideArgument (unsigned 128 (← integer value)))
  | _ => do pure (.integer (unsigned ty.bit_width (← integer value)))

private def Value.unpacked : Value → Value
  | .wideArgument bits => .integer bits
  | value => value

private def perform (operation : HeapEffect) : Computation HeapReply := .heap operation .pure

private def alloc (size : Int) (heap : Bool := true) : Computation Value := do
  if size < 0 ∨ 9223372036854775807 < size then return ← .fault .hostSize
  match ← perform (.allocate size.toNat heap) with
  | .pointer address => pure (.pointer address)
  | _ => .invalid

private def image_word (image : AggregateImage Nat) (width : Nat) : Int :=
  little_endian_read width (fun i => (image.payload i).getD 0)

private def word_image (bits : Int) (size : Nat) (cap : Option Nat := none) : AggregateImage Nat :=
  ⟨fun i => if 0 ≤ i && i.toNat < size then some (little_endian_byte bits i.toNat) else none,
   fun i => if i == 0 then cap else none⟩

private def read (ty : TypeCode) (address : Value) : Computation Value := do
  let address ← pointer address
  match ty with
  | .complex32 | .complex64 | .complex80 | .binary32 | .binary64 =>
    let .word bits ← perform (.loadWord address ty.width) | .invalid
    convert ty (.integer bits)
  | .extended =>
    match ← perform (.loadWord address 16) with
    | .word bits => pure (.extended (unsigned 80 bits))
    | _ => .invalid
  | .pointer =>
    match ← perform (.loadPointer address) with
    | .pointer value => pure (.pointer value)
    | _ => .invalid
  | .byte | .signedByte =>
    match ← perform (.loadByte address) with
    | .byte value => convert ty (.integer value.toNat)
    | _ => .invalid
  | .integer | .unsignedInt | .size | .short | .unsignedShort | .long | .wide | .unsignedWide =>
    match ← perform (.loadWord address ty.width) with
    | .word value => convert ty (.integer value)
    | _ => .invalid
  | .bitField shift _ _ =>
    match ← perform (.loadWord address ty.width) with
    | .word value => convert ty (.integer (value / 2 ^ shift))
    | _ => .invalid
  | .atomicRecord last alignment storage mode =>
    let image ← match mode with
      | .copy => do
        let .aggregate image ← perform (.loadAggregate address (last + 1)) | .invalid
        pure image
      | .bytes => do
        let .word bits ← perform (.loadWord address (storage + 1)) | .invalid
        pure (word_image bits (last + 1))
      | .capability => do
        let .pointer ptr ← perform (.loadPointer address true) | .invalid
        pure (word_image ptr.address (last + 1) (some ptr.capability))
    return .aggregate (last + 1) alignment image
  | .aggregate lastByte alignment =>
    match ← perform (.loadAggregate address (lastByte + 1)) with
    | .aggregate image => pure (.aggregate (lastByte + 1) alignment image)
    | _ => .invalid

private def store (ty : TypeCode) (address value : Value) : Computation Value := do
  let p ← pointer address
  let converted ← convert ty value
  match ty, converted with
  | .complex32, .complex _ real imag | .complex64, .complex _ real imag | .complex80, .complex _ real imag =>
    let _ ← perform (.storeWord p ty.width (real + 2 ^ (4 * ty.width) * imag))
    pure converted
  | .binary32, .ieee false bits | .binary64, .ieee true bits =>
    let _ ← perform (.storeWord p ty.width bits)
    pure converted
  | .extended, .extended bits =>
    let _ ← perform (.storeWord p 16 bits)
    pure converted
  | .pointer, .pointer target =>
    let _ ← perform (.storePointer p target)
    pure converted
  | .byte, .integer scalar | .signedByte, .integer scalar =>
    let _ ← perform (.storeByte p (byte scalar))
    pure converted
  | .integer, .integer scalar | .unsignedInt, .integer scalar | .size, .integer scalar =>
    let _ ← perform (.storeWord p ty.width scalar)
    pure converted
  | .short, .integer scalar | .unsignedShort, .integer scalar | .long, .integer scalar
  | .wide, .integer scalar | .unsignedWide, .integer scalar =>
    let _ ← perform (.storeWord p ty.width scalar)
    pure converted
  | .bitField shift width _, .integer scalar =>
    let _ ← perform (.storeBits p shift (width + 1) scalar)
    pure converted
  | .atomicRecord last _ storage mode, .aggregate _ _ image =>
    let bits := image_word image (last + 1)
    let _ ← match mode with
      | .copy => perform (.storeAggregate p (last + 1) image)
      | .bytes => perform (.storeWord p (storage + 1) bits)
      | .capability => perform (.storePointer p ⟨(image.shadow 0).getD 0, bits⟩ true)
    pure converted
  | .aggregate lastByte _, .aggregate _ _ image =>
    let _ ← perform (.storeAggregate p (lastByte + 1) image)
    pure converted
  | _, _ => .invalid

theorem binary80_slot_roundtrip (state : HeapState) (address : Pointer) (slot : Nat) (bits : Int)
    (before : Object) (access : runtime_checked state.objects (some address) 16 = .ok (before, slot))
    (writable : before.readonly = false) :
    ∃ edit, heap_effect state (.storeWord address 16 (unsigned 80 bits)) = .ok edit ∧
      heap_effect (apply_heap_edit state edit) (.loadWord address 16) =
        .ok { reply := .word (unsigned 80 bits) } := by
  obtain ⟨written, loaded⟩ := scalar_slot_refines state address 16 slot (unsigned 80 bits) before access writable
  refine ⟨_, written, ?_⟩
  have bounds := unsigned_bounds 80 bits
  have fits : unsigned 80 bits < modulus (8 * 16) :=
    Int.lt_trans bounds.2 (Int.pow_lt_pow_of_lt (by decide : (1 : Int) < 2) (by decide : 80 < 8 * 16))
  simpa only [show unsigned (8 * 16) (unsigned 80 bits) = unsigned 80 bits from
    Int.emod_eq_of_lt bounds.1 fits] using loaded

private def critical (operation : Computation α) : Computation α := do
  let _ ← perform (.critical true)
  let result ← operation
  let _ ← perform (.critical false)
  return result

private def atomic_pointer_load (place : Value) : Computation Pointer := do
  let .pointer old ← perform (.loadPointer (← pointer place) true) | .invalid
  return old

private def atomic_pointer_store (place incoming : Value) : Computation Unit := do
  let _ ← perform (.storePointer (← pointer place) (← pointer incoming) true)
  pure ()

private def compare_word (ty : TypeCode) (target expected desired : Value) (indirect : Bool) : Computation Value := do
  if let .atomicRecord last alignment storage mode := ty then
    return ← critical do
      let plain := TypeCode.aggregate last alignment
      let replacement ← if indirect then read plain desired else pure desired
      let old ← read ty target
      let wanted ← read plain expected
      let .aggregate _ _ observed := old | return ← .invalid
      let .aggregate _ _ expectation := wanted | return ← .invalid
      let .word frozen ← perform (.readonlyCapability (← pointer target)) | .invalid
      if frozen != 0 then return ← .fault .readonly
      let actual ← if mode == .bytes && storage != last then do
        let .word raw ← perform (.loadWord (← pointer target) (storage + 1)) | .invalid
        pure raw
      else pure (image_word observed (last + 1))
      if actual == image_word expectation (last + 1) then
        let _ ← store ty target replacement
        return .integer 1
      if mode == .bytes then
        if storage == last then
          let _ ← perform (.storeWord (← pointer expected) (last + 1) actual)
      else
        let _ ← store plain expected old
      return .integer 0
  if ty == .pointer then
    return ← critical do
      let old ← atomic_pointer_load target
      let wanted ← pointer (← read .pointer expected)
      let .word frozen ← perform (.readonlyCapability (← pointer target)) | .invalid
      if frozen != 0 then return ← .fault .readonly
      if old.address == wanted.address then
        atomic_pointer_store target desired
        return .integer 1
      let _ ← store .pointer expected (.pointer old)
      return .integer 0
  let operation := HeapEffect.compareWord (← pointer target) (← pointer expected) ty.width (← integer desired)
  let .word result ← perform operation | .invalid
  pure (.integer result)

private def atomic_transfer_values (op : TransferKind) (ty : TypeCode) (target operands : Value) : Computation Value := do
  let .atomicRecord last alignment _ _ := ty | return ← .invalid
  let .arguments args := operands | return ← .invalid
  let plain := TypeCode.aggregate last alignment
  critical do
    match op, args with
    | .load, [_, destination] =>
      let _ ← store plain destination (← read ty target)
    | .store, [_, source] =>
      let _ ← store ty target (← read plain source)
    | .exchange, [_, source, destination] =>
      let desired ← read plain source
      let old ← read ty target
      let _ ← store ty target desired
      let _ ← store plain destination old
    | _, _ => return ← .invalid
    return .integer 0

private def atomic_word (op : AtomicOperation) (ty : TypeCode) (target operand : Value) : Computation Value := do
  if let .atomicRecord last alignment storage _ := ty then
    match op with
    | .initialise =>
      return ← critical do
        let _ ← store (.aggregate last alignment) target operand
        if last < storage then
          let p ← pointer target
          let _ ← perform (.storeWord (offset_pointer p (last + 1)) (storage - last) 0)
        return .integer 0
    | .fetch .exchange true =>
      return ← critical do
        let old ← read ty target
        let _ ← store ty target operand
        return old
    | _ => pure ()
  if ty == .pointer then
    match op with
    | .load => return .pointer (← atomic_pointer_load target)
    | .store =>
      atomic_pointer_store target operand
      return .integer 0
    | .fetch .exchange true =>
      return ← critical do
        let old ← atomic_pointer_load target
        atomic_pointer_store target operand
        return .pointer old
    | _ => pure ()
  match op with
  | .load => read ty target
  | .store | .initialise =>
    let _ ← store ty target operand
    pure (.integer 0)
  | .pointerStep operation stride returnOld =>
    let amount := (← integer operand) * stride
    let .word old ← perform (.fetchWord (← pointer target) 8 operation amount) | .invalid
    return .pointer ⟨0, unsigned 64 (if returnOld then old else operation.apply 8 old amount)⟩
  | .fetch operation returnOld =>
    let address ← pointer target
    let value ← integer operand
    let .word old ← perform (.fetchWord address ty.width operation value) | .invalid
    convert ty (.integer (if returnOld then old else operation.apply ty.width old value))

private def materialise_value (ty : TypeCode) (value : Value) : Computation Value := do
  let address ← alloc ty.width false
  let _ ← store ty address value
  pure address

private def move_bytes (destination source size : Value) : Computation Value := do
  let d ← pointer destination
  let s ← pointer source
  let count ← integer size
  if count < 0 ∨ 9223372036854775807 < count then return ← .fault .hostSize
  let _ ← perform (.copy s d count.toNat)
  pure destination

private def emit_byte (value : Value) : Computation Value := do
  let n ← integer value
  let b := byte n
  .output [[b]] (.pure (.integer b.toNat))

private def release_heap (value : Value) : Computation Value := do
  let address ← pointer value
  let _ ← perform (.release address)
  pure (.integer 0)

private def add_offset (stride : Nat) (base index : Value) : Computation Value := do
  let address ← pointer base
  let delta ← integer index
  pure (.pointer (offset_pointer address (stride * delta)))

private def pointer_arithmetic (op : PointerOp) (stride : Nat) (first second : Value) : Computation Value :=
  match op with
  | .add => add_offset stride first second
  | .reversedAdd => add_offset stride second first
  | .subtract => do
    let address ← pointer first
    let delta ← integer second
    pure (.pointer (offset_pointer address (-((stride : Int) * delta))))
  | .difference => do
    let left ← pointer first
    let right ← pointer second
    if stride == 0 then .invalid
    else pure (.integer (signed 64 ((left.address - right.address).tdiv (stride : Int))))

theorem pointer_distance_exact (base : Pointer) (stride : Nat) (first second : Int)
    (positive : 0 < stride)
    (left : 0 ≤ base.address + (stride : Int) * first ∧ base.address + (stride : Int) * first < modulus 64)
    (right : 0 ≤ base.address + (stride : Int) * second ∧ base.address + (stride : Int) * second < modulus 64) :
    pointer_arithmetic .difference stride (.pointer (offset_pointer base ((stride : Int) * first)))
      (.pointer (offset_pointer base ((stride : Int) * second))) = pure (.integer (signed 64 (first - second))) := by
  have nonzero : (stride : Int) ≠ 0 := by omega
  have delta : base.address + (stride : Int) * first - (base.address + (stride : Int) * second) =
      (stride : Int) * (first - second) := by
    rw [Int.mul_sub]
    omega
  change (if stride == 0 then Computation.invalid else Computation.pure (Value.integer (signed 64
    ((unsigned 64 (base.address + (stride : Int) * first) -
      unsigned 64 (base.address + (stride : Int) * second)).tdiv (stride : Int))))) =
      Computation.pure (.integer (signed 64 (first - second)))
  rw [unsigned_preserves_bits _ _ left.1 left.2, unsigned_preserves_bits _ _ right.1 right.2, delta,
    Int.mul_tdiv_cancel_left _ nonzero]
  simp [Nat.ne_of_gt positive]

def scalar_result (op : ScalarOp) (width : Nat) (isSigned : Bool) (x y : Int) : Except HeapFault Int :=
  let bound := modulus (width - 1)
  let wrap : Int → Except HeapFault Int := fun value => .ok (if isSigned then signed width value else unsigned width value)
  let arithmetic := fun result =>
    if isSigned && (result < -bound || bound ≤ result) then .error .signedOverflow else wrap result
  let leftBits := (unsigned width x).toNat
  let rightBits := (unsigned width y).toNat
  let comparison := fun test : Bool => Except.ok (if test then 1 else 0)
  match op with
  | .add => arithmetic (x + y)
  | .sub => arithmetic (x - y)
  | .mul => arithmetic (x * y)
  | .div => if y == 0 then .error .divisionByZero else arithmetic (x.tdiv y)
  | .rem =>
    if y == 0 then .error .divisionByZero
    else if isSigned && x == -bound && y == -1 then .error .divisionOverflow
    else wrap (x.tmod y)
  | .band => wrap (↑(leftBits &&& rightBits) : Int)
  | .bor => wrap (↑(leftBits ||| rightBits) : Int)
  | .bxor => wrap (↑(leftBits ^^^ rightBits) : Int)
  | .shl =>
    if y < 0 ∨ (width : Int) ≤ y then .error .shiftCount
    else if isSigned && x < 0 then .error .negativeShift
    else arithmetic (x <<< y.toNat)
  | .shr =>
    if y < 0 ∨ (width : Int) ≤ y then .error .shiftCount else wrap (x >>> y.toNat)
  | .eq => comparison (x == y)
  | .ne => comparison (x != y)
  | .lt => comparison (x < y)
  | .le => comparison (x ≤ y)
  | .gt => comparison (x > y)
  | .ge => comparison (x ≥ y)

private theorem scalar_bits_bounded (width : Nat) (value : Int) :
    (unsigned width value).toNat < 2 ^ width := by
  have inRange := unsigned_bounds width value
  apply Int.ofNat_lt.mp
  rw [Int.toNat_of_nonneg inRange.1, Int.natCast_pow]
  exact inRange.2

private theorem scalar_bits_wrap (width : Nat) (isSigned : Bool) (word : Nat) (within : word < 2 ^ width) :
    (unsigned width (if isSigned then signed width word else unsigned width word)).toNat = word := by
  have upper : (word : Int) < modulus width := by
    have widened := Int.ofNat_lt.mpr within
    rw [Int.natCast_pow 2 width] at widened
    exact widened
  have canonical := unsigned_preserves_bits width word (Int.natCast_nonneg word) upper
  cases isSigned with
  | false => simp [canonical]
  | true => simp [signed_preserves_bits, canonical]

theorem scalar_bitwise_bits (op : ScalarOp) (bitwise : op = .band ∨ op = .bor ∨ op = .bxor)
    (width : Nat) (isSigned : Bool) (x y : Int) (index : Nat) :
    ∃ value, scalar_result op width isSigned x y = .ok value ∧
      (unsigned width value).toNat.testBit index =
        let a := (unsigned width x).toNat.testBit index
        let b := (unsigned width y).toNat.testBit index
        match op with
        | .band => a && b
        | .bor => a || b
        | .bxor => a ^^ b
        | _ => false := by
  let left := (unsigned width x).toNat
  let right := (unsigned width y).toNat
  have first : left < 2 ^ width := scalar_bits_bounded width x
  have second : right < 2 ^ width := scalar_bits_bounded width y
  rcases bitwise with rfl | rfl | rfl
  · refine ⟨_, rfl, ?_⟩
    have same := congrArg (fun word : Nat => word.testBit index)
      (scalar_bits_wrap width isSigned (left &&& right) (Nat.and_lt_two_pow left second))
    exact same.trans (Nat.testBit_and left right index)
  · refine ⟨_, rfl, ?_⟩
    have same := congrArg (fun word : Nat => word.testBit index)
      (scalar_bits_wrap width isSigned (left ||| right) (Nat.or_lt_two_pow first second))
    exact same.trans (Nat.testBit_or left right index)
  · refine ⟨_, rfl, ?_⟩
    have same := congrArg (fun word : Nat => word.testBit index)
      (scalar_bits_wrap width isSigned (left ^^^ right) (Nat.xor_lt_two_pow first second))
    exact same.trans (Nat.testBit_xor left right index)

private def scalar_apply (op : ScalarOp) (ty : TypeCode) (left right : Value) : Computation Value := do
  match scalar_result op (8 * ty.width) ty.signed (← integer left) (← integer right) with
  | .ok value => pure (.integer value)
  | .error fault => .fault fault

private def pointer_compare (op : ScalarOp) (first second : Value) : Computation Value := do
  let left ← pointer first
  let right ← pointer second
  scalar_apply op .size (.integer left.address) (.integer right.address)

private def unary_apply (op : UnaryOp) (ty : TypeCode) (value : Value) : Computation Value :=
  match op with
  | .plus => pure value
  | .minus => scalar_apply .sub ty (.integer 0) value
  | .complement => do convert ty (.integer (~~~ (← integer value)))

private def update_value (op : ScalarOp) (storage arithmetic : TypeCode) (returnOld : Bool) (stride : Nat)
    (address old value : Value) : Computation Value := do
  let result ← if arithmetic == .pointer then
    match op with
    | .add => pointer_arithmetic .add stride old value
    | .sub => pointer_arithmetic .subtract stride old value
    | _ => .invalid
  else do
    let promoted ← convert arithmetic old
    scalar_apply op arithmetic promoted value
  let stored ← store storage address result
  pure (if returnOld then old else stored)

private def argument_values (value : Value) : Computation (List Value) :=
  match value with
  | .arguments values => pure values
  | _ => .invalid

def array_extent (width : Nat) (bounds : List Int) : Except HeapFault Int :=
  if bounds.any (· ≤ 0) then .error .invalidExtent
  else
    let size := bounds.foldr (· * ·) (Int.ofNat width)
    if size < 0 ∨ 9223372036854775807 < size then .error .hostSize else .ok size

theorem array_extent_exact (width : Nat) (bounds : List Int)
    (positive : ∀ bound ∈ bounds, 0 < bound)
    (fits : 0 ≤ bounds.foldr (· * ·) (Int.ofNat width) ∧
      bounds.foldr (· * ·) (Int.ofNat width) ≤ 9223372036854775807) :
    array_extent width bounds = .ok (bounds.foldr (· * ·) (Int.ofNat width)) := by
  have valid : bounds.any (· ≤ 0) = false := by
    apply List.any_eq_false.mpr
    intro bound present nonpositive
    exact (Int.not_le.mpr (positive bound present)) (of_decide_eq_true nonpositive)
  simp [array_extent, valid]
  exact fits

theorem array_extent_rejects (width : Nat) (bounds : List Int) (bound : Int)
    (present : bound ∈ bounds) (nonpositive : bound ≤ 0) :
    array_extent width bounds = .error .invalidExtent := by
  have invalid : bounds.any (· ≤ 0) = true :=
    List.any_eq_true.mpr ⟨bound, present, decide_eq_true nonpositive⟩
  simp [array_extent, invalid]

private def checked_extent (width : Nat) (arguments : Value) : Computation Value := do
  let bounds ← (← argument_values arguments).mapM integer
  match array_extent width bounds with
  | .ok size => pure (.integer size)
  | .error fault => .fault fault

def captured_spans (width : Int) : List Int → List Int
  | [] => [width]
  | extent :: rest =>
    let spans := captured_spans width rest
    extent * spans.headD width :: spans

theorem captured_span_exact (width : Int) (bounds : List Int) (rank : Nat) (within : rank ≤ bounds.length) :
    (captured_spans width bounds)[rank]? = some ((bounds.drop rank).foldr (· * ·) width) := by
  induction bounds generalizing rank with
  | nil =>
    have first : rank = 0 := by simpa using within
    subst rank
    rfl
  | cons extent rest ih =>
    cases rank with
    | zero =>
      have tail := ih 0 (Nat.zero_le _)
      simp [captured_spans, List.head?_eq_getElem?, tail]
    | succ rank =>
      simpa [captured_spans] using ih rank (Nat.le_of_succ_le_succ within)

theorem captured_array_extent_readback (state : HeapState) (address : Pointer) (width : Int)
    (bounds : List Int) (edit : HeapEdit)
    (stored : heap_effect state (.setArraySpans address (captured_spans width bounds)) = .ok edit)
    (rank : Nat) (within : rank ≤ bounds.length) :
    heap_effect (apply_heap_edit state edit) (.arraySpan address rank) =
      .ok { reply := .word ((bounds.drop rank).foldr (· * ·) width) } :=
  captured_array_span_load state address _ edit stored rank _ (captured_span_exact width bounds rank within)

private def current_array (slot : Nat) : Computation Value := do
  match ← perform (.locateArray slot) with
  | .pointer address => pure (.pointer address)
  | _ => .invalid

private def current_span (slot rank : Nat) : Computation Int := do
  let address ← pointer (← current_array slot)
  match ← perform (.arraySpan address rank) with
  | .word width => pure width
  | _ => .invalid

private def register_shape (slot : Nat) (address : Pointer) (spans : List Int) : Computation Unit := do
  let _ ← perform (.registerArray slot address)
  let _ ← perform (.setArraySpans address spans)
  pure ()

private def bind_array_shape (slot width skip : Nat) (place bounds : Value) : Computation Unit := do
  let address ← pointer place
  let extents ← (← argument_values bounds).mapM integer
  if extents.any (· ≤ 0) then return ← .fault .invalidExtent
  register_shape slot address ((captured_spans width extents).drop skip)

private def allocate_array (slot : Nat) (size : Int) (spans : List Int) : Computation Unit := do
  let address ← pointer (← alloc size false)
  register_shape slot address spans

private def declare_array (slot width : Nat) (typeOnly : Bool) (arguments : Value) : Computation Unit := do
  let bounds ← (← argument_values arguments).mapM integer
  let spans := captured_spans width bounds
  if typeOnly then
    if bounds.any (· ≤ 0) then .fault .invalidExtent else allocate_array slot 0 spans
  else
    match array_extent width bounds with
    | .error fault => .fault fault
    | .ok size => allocate_array slot size spans

private def instantiate_array (slot source : Nat) : Computation Unit := do
  let address ← pointer (← current_array source)
  match ← perform (.arrayShape address) with
  | .shape spans@(size :: _) => allocate_array slot size spans
  | _ => .fault .missingArray

abbrev Calls := String → List Value → Computation Value

abbrev Globals := List (String × Value)

structure Locals where
  slots : List (Option Value)
  globals : Globals
  area : Option Value := none
  named : List TypeCode := []

private def locate (locals : Locals) (index : Nat) : Computation Value :=
  match locals.slots[index]?.join with
  | none => .invalid
  | some value => pure value

private def locate_global (globals : Globals) (name : String) : Computation Value :=
  match globals.lookup name with
  | none => .invalid
  | some address => pure address

private def slot_for (ty : TypeCode) : ArgumentSlot :=
  ⟨ty.width, match ty with | .aggregate _ alignment => max 8 alignment | .extended | .complex80 => 16 | _ => 8⟩

private def packed_slot (value : Value) : Computation (TypeCode × Value) :=
  match value with
  | .integer _ => pure (.size, value)
  | .pointer _ => pure (.pointer, value)
  | .wideArgument bits => pure (.unsignedWide, .integer bits)
  | .extended _ => pure (.extended, value)
  | .complex ty _ _ => pure (ty, value)
  | .aggregate (last + 1) alignment _ => pure (.aggregate last alignment, value)
  | _ => .invalid

private def write_arguments (area : Pointer) (position : Nat) : List (TypeCode × Value) → Computation Unit
  | [] => pure ()
  | (ty, value) :: rest => do
    let layout := slot_for ty
    let (start, next) := aligned_slot position layout.width layout.alignment
    let _ ← store ty (.pointer (offset_pointer area start)) value
    write_arguments area next rest

private def construct_argument_area (values : List Value) : Computation Value := do
  let slots ← values.mapM packed_slot
  let size := argument_cursor 0 (slots.map (slot_for ∘ Prod.fst))
  let area ← pointer (← alloc size false)
  write_arguments area 0 slots
  let _ ← perform (.freeze area)
  pure (.pointer area)

private def current_argument_area (locals : Locals) : Computation Value :=
  match locals.area with
  | none => .invalid
  | some area => pure area

private def start_va (locals : Locals) (place : Value) : Computation Value := do
  let area ← pointer (← current_argument_area locals)
  let delta := argument_cursor 0 (locals.named.map slot_for)
  let _ ← store .pointer place (.pointer (offset_pointer area delta))
  pure (.integer 0)

private def copy_va (destination source : Value) : Computation Value := do
  let cursor ← read .pointer source
  let _ ← store .pointer destination cursor
  pure (.integer 0)

private def fetch_va (ty : TypeCode) (place : Value) : Computation Value := do
  let cursor ← pointer (← read .pointer place)
  let (start, next) := variadic_access cursor.address.toNat (slot_for ty)
    (ty == .wide || ty == .unsignedWide)
  let value ← read ty (.pointer (offset_pointer cursor ((start : Int) - cursor.address)))
  let _ ← store .pointer place (.pointer (offset_pointer cursor ((next : Int) - cursor.address)))
  pure value

private def available_va (place : Value) : Computation Value := do
  let cursor ← pointer (← read .pointer place)
  match ← perform (.readable cursor 8) with
  | .word bits => pure (.integer bits)
  | _ => .invalid

private def request (operation : ThreadRequest) : Computation HeapReply := do
  match ← perform (.thread operation) with
  | .pending => .suspend
  | reply => pure reply

private def spawn_thread (globals : Globals) (worker : String) (destination argument : Value) : Computation Value := do
  let handle ← alloc 0 false
  let _ ← store .pointer destination handle
  let addresses ← globals.mapM fun (name, value) => do pure (name, ← pointer value)
  let _ ← request (.create (← pointer handle) worker (← pointer argument) addresses)
  pure (.integer 0)

private def join_thread (handle destination : Value) : Computation Value := do
  match ← request (.join (← pointer handle)) with
  | .word status => pure (.integer status)
  | .pointer value =>
    if truth destination then
      let _ ← store .pointer destination (.pointer value)
    pure (.integer 0)
  | _ => .invalid

private def thread_self : Computation Value := do
  match ← request .self with
  | .pointer address => pure (.pointer address)
  | _ => .invalid

private def thread_equal (left right : Value) : Computation Value := do
  pure (logical ((← pointer left).address == (← pointer right).address))

private def literal_string (bytes : List UInt8) : Computation Value := do
  let .pointer ptr ← perform (.intern bytes) | .invalid
  return .pointer ptr

theorem literal_reuse (memory : HeapState) (found : memory.literals.lookup bytes = some ptr)
    (next : Value → TraceProgram) (fuel : Nat) (out : StdoutState) (terminal : Bool)
    (blocks : Nat → Option TraceProgram) :
    run_trace abstract_machine terminal blocks (fuel + 1) ((literal_string bytes).emit next) memory out =
      run_trace abstract_machine terminal blocks fuel (next (.pointer ptr)) memory out := by
  simp [literal_string, perform, Computation.emit, Bind.bind, Computation.bind, pure, run_trace,
    abstract_machine, heap_effect, found, apply_heap_edit]

private def scan_string (address : Pointer) (reversed : List UInt8) : Nat → Computation (List UInt8)
  | 0 => do
    let _ ← perform (.loadByte address)
    .fault (.access .bounds)
  | left + 1 => do
    let .byte b ← perform (.loadByte address) | .invalid
    if b == 0 then return reversed.reverse
    scan_string (offset_pointer address 1) (b :: reversed) left

private def string_bytes (value : Value) : Computation (List UInt8) := do
  let ptr ← pointer value
  let .word size ← perform (.remaining ptr) | .invalid
  scan_string ptr [] size.toNat

inductive StringRead (memory : HeapState) : Pointer → Nat → Nat → Except HeapFault (List UInt8) → Prop where
  | zero : heap_effect memory (.loadByte address) = .ok { reply := .byte 0 } →
      StringRead memory address (room + 1) 1 (.ok [])
  | fault : heap_effect memory (.loadByte address) = .error why →
      StringRead memory address room 1 (.error why)
  | byte : heap_effect memory (.loadByte address) = .ok { reply := .byte b } → b ≠ 0 →
      StringRead memory (offset_pointer address 1) room steps result →
      StringRead memory address (room + 1) (steps + 1) (result.map (b :: ·))

theorem string_read_correct (run : StringRead memory address room steps result)
    (next : List UInt8 → TraceProgram) (reversed : List UInt8) (fuel : Nat) (out : StdoutState)
    (terminal : Bool) (blocks : Nat → Option TraceProgram) :
    run_trace abstract_machine terminal blocks (fuel + 1 + steps) ((scan_string address reversed room).emit next)
        memory out =
      match result with
      | .ok bytes => run_trace abstract_machine terminal blocks (fuel + 1) (next (reversed.reverse ++ bytes)) memory out
      | .error why => ⟨.fault why, memory, out⟩ := by
  induction run generalizing reversed with
  | zero loaded =>
    simp [scan_string, perform, Computation.emit, Bind.bind, Computation.bind, pure, run_trace,
      abstract_machine, loaded, apply_heap_edit]
  | fault failed =>
    rename_i room
    cases room <;> simp [scan_string, perform, Computation.emit, Bind.bind, Computation.bind,
      run_trace, abstract_machine, failed]
  | @byte ptr b room steps result loaded nonzero following ih =>
    simp only [Nat.add_succ, scan_string, perform, Bind.bind, Computation.bind, Computation.emit, run_trace,
      abstract_machine, id_eq, loaded, apply_heap_edit]
    simp only [beq_eq_false_iff_ne.mpr nonzero, Bool.false_eq_true, if_false]
    cases result <;> simpa [Except.map, List.reverse_cons, List.append_assoc] using ih (b :: reversed)

inductive Conversion where
  | number (bits base : Nat) (signed upper : Bool)
  | character | string
  | fixed (precision : Nat) (upper : Bool)

inductive FormatItem where
  | byte (value : UInt8)
  | conversion (operation : Conversion) (field : Nat) (zero : Bool)

private def format_conversion (options : List UInt8) (specifier : UInt8) : Option FormatItem := do
  let digit := fun (b : UInt8) => 48 ≤ b && b ≤ 57
  let digits := options.takeWhile digit
  let field := digits.foldl (fun n b => n * 10 + (b.toNat - 48)) 0
  guard (field ≤ 9223372036854775807)
  let modifier := options.dropWhile digit
  if specifier == 102 || specifier == 70 then
    let (places, length) := match modifier with
      | 46 :: rest => (some (rest.takeWhile digit), rest.dropWhile digit)
      | _ => (none, modifier)
    guard (length.isEmpty || length == [108])
    let precision := places.elim 6 (fun ps => ps.foldl (fun n b => n * 10 + (b.toNat - 48)) 0)
    guard (precision ≤ 1024)
    return .conversion (.fixed precision (specifier == 70)) field (digits.head? == some 48)
  let bits ← match modifier with
    | [] => some 32 | [104, 104] => some 8 | [104] => some 16
    | [108] | [108, 108] | [122] => some 64 | _ => none
  let op ← match specifier.toNat with
    | 100 | 105 => some (.number bits 10 true false)
    | 117 => some (.number bits 10 false false)
    | 120 => some (.number bits 16 false false)
    | 88 => some (.number bits 16 false true)
    | 111 => some (.number bits 8 false false)
    | 99 => if modifier.isEmpty then some .character else none
    | 115 => if modifier.isEmpty then some .string else none
    | _ => none
  return .conversion op field (digits.head? == some 48)

def format_items (bytes : List UInt8) : Option (List FormatItem) := Id.run do
  let rec parse : Option (List UInt8) → List UInt8 → Option (List FormatItem)
    | none, [] | none, 0 :: _ => some []
    | none, 37 :: rest => parse (some []) rest
    | none, b :: rest => (.byte b :: ·) <$> parse none rest
    | some [], 37 :: rest => (.byte 37 :: ·) <$> parse none rest
    | some options, b :: rest => do
      if (48 ≤ b && b ≤ 57) || [46, 104, 108, 122].contains b then
        parse (some (b :: options)) rest
      else
        return (← format_conversion options.reverse b) :: (← parse none rest)
    | some _, [] => none
  return parse none bytes

private def fixed_decimal (word precision : Nat) (upper : Bool) : List UInt8 := Id.run do
  let exponent : Nat := word / 2 ^ 52 % 2048
  let fraction := word % 2 ^ 52
  let sign : List UInt8 := if word.testBit 63 then [45] else []
  if exponent == 2047 then
    let text := if fraction == 0 then "inf" else "nan"
    return sign ++ (if upper then text.toUpper else text).toUTF8.data.toList
  let significand := if exponent == 0 then fraction else 2 ^ 52 + fraction
  let shift := (max exponent 1 : Int) - 1075
  let scaled := significand * 10 ^ precision * 2 ^ shift.toNat
  let rounded := nearest_coefficient scaled (2 ^ (-shift).toNat)
  let digits := (toString rounded).toUTF8.data.toList
  if precision == 0 then return sign ++ digits
  let padded := List.replicate (precision + 1 - digits.length) 48 ++ digits
  let point := padded.length - precision
  return sign ++ padded.take point ++ [46] ++ padded.drop point

private def format_piece (op : Conversion) (value : Value) : Computation (List UInt8) := do
  match op with
  | .string => string_bytes value
  | .fixed precision upper => return fixed_decimal (unsigned 64 (← integer value.unpacked)).toNat precision upper
  | .character => return [byte (← integer value.unpacked)]
  | .number width base sign upper =>
    let raw ← integer value.unpacked
    let n := if sign then signed width raw else unsigned width raw
    let digits := (Nat.toDigits base n.natAbs).map fun c =>
      UInt8.ofNat (if upper then c.toUpper.toNat else c.toLower.toNat)
    return if n < 0 then 45 :: digits else digits

private def format_output : List FormatItem → List Value → Computation (List UInt8)
  | [], _ => pure []
  | .byte b :: rest, values => return b :: (← format_output rest values)
  | .conversion op width zero :: rest, value :: values => do
    let piece ← format_piece op value
    let padZero := match op with
      | .number .. => zero
      | .fixed .. => zero && piece.any (fun b => 48 ≤ b && b ≤ 57)
      | _ => false
    let padding := List.replicate (width - piece.length) (if padZero then 48 else 32)
    let field := if padZero && piece.head? == some 45 then 45 :: padding ++ piece.tail else padding ++ piece
    return field ++ (← format_output rest values)
  | .conversion .. :: _, [] => .invalid

def function_pointer (index : Nat) : Pointer := ⟨2 ^ 64 + index, (2 ^ 63 : Int) + index⟩

def resolve_function (names : List String) (ptr : Pointer) : Option String :=
  let index : Nat := ptr.capability - 2 ^ 64
  if ptr.capability = 2 ^ 64 + index ∧ ptr.address = (2 ^ 63 : Int) + (index : Int) then names[index]? else none

theorem resolve_function_iff (names : List String) (ptr : Pointer) (name : String) :
    resolve_function names ptr = some name ↔ ∃ index, ptr = function_pointer index ∧ names[index]? = some name := by
  constructor
  · intro found
    dsimp only [resolve_function] at found
    split at found
    · rename_i valid
      refine ⟨ptr.capability - 2 ^ 64, ?_, found⟩
      cases ptr
      simp only [function_pointer, Pointer.mk.injEq]
      exact valid
    · contradiction
  · rintro ⟨index, rfl, found⟩
    simpa [resolve_function, function_pointer, Nat.add_sub_cancel_left] using found

theorem stored_function_resolves (names : List String) (index slot : Nat) (object : Object)
    (fits : index < 2 ^ 63) :
    let (cap, address) := data_pointer_word (write_pointer_word object slot (function_pointer index)) slot
    resolve_function names ⟨cap.getD 0, address⟩ = names[index]? := by
  rw [data_pointer_word_roundtrip]
  change index < 9223372036854775808 at fits
  have range : (index : Int) < 9223372036854775808 := Int.ofNat_lt.mpr fits
  have repr : unsigned 64 ((2 ^ 63 : Int) + index) = 2 ^ 63 + index := by
    change (9223372036854775808 + (index : Int)) % 18446744073709551616 = _
    apply Int.emod_eq_of_lt <;> omega
  dsimp only [function_pointer, Option.getD_some]
  rw [repr]
  simp [resolve_function]

theorem changed_function_rejected (names : List String) (index : Nat) (address : Int)
    (changed : address ≠ (function_pointer index).address) :
    resolve_function names ⟨(function_pointer index).capability, address⟩ = none := by
  change address ≠ 9223372036854775808 + (index : Int) at changed
  simp [resolve_function, function_pointer, changed]

private def callable (symbols : List String) (value : Value) : Computation String := do
  let some name := resolve_function symbols (← pointer value) | .fault .invalidFunction
  return name

private def compare_bytes (left right : Pointer) : Nat → Computation Value
  | 0 => do
    let _ ← perform (.loadByte left)
    .fault (.access .bounds)
  | room + 1 => do
    let .byte x ← perform (.loadByte left) | .invalid
    let .byte y ← perform (.loadByte right) | .invalid
    if x != y || x == 0 then return .integer ((x.toNat : Int) - y.toNat)
    compare_bytes (offset_pointer left 1) (offset_pointer right 1) room

private def compare_strings (lhs rhs : Value) : Computation Value := do
  let a ← pointer lhs
  let b ← pointer rhs
  let .word size ← perform (.remaining a) | .invalid
  compare_bytes a b size.toNat

inductive StringComparison (memory : HeapState) : Pointer → Pointer → Nat → Nat → Except HeapFault Int → Prop where
  | leftFault : heap_effect memory (.loadByte left) = .error why →
      StringComparison memory left right room 1 (.error why)
  | rightFault : heap_effect memory (.loadByte left) = .ok { reply := .byte x } →
      heap_effect memory (.loadByte right) = .error why →
      StringComparison memory left right (room + 1) 2 (.error why)
  | stop : heap_effect memory (.loadByte left) = .ok { reply := .byte x } →
      heap_effect memory (.loadByte right) = .ok { reply := .byte y } → (x ≠ y ∨ x = 0) →
      StringComparison memory left right (room + 1) 2 (.ok ((x.toNat : Int) - y.toNat))
  | equal : heap_effect memory (.loadByte left) = .ok { reply := .byte x } →
      heap_effect memory (.loadByte right) = .ok { reply := .byte x } → x ≠ 0 →
      StringComparison memory (offset_pointer left 1) (offset_pointer right 1) room steps result →
      StringComparison memory left right (room + 1) (steps + 2) result

theorem string_comparison_correct (comparison : StringComparison memory left right room steps result)
    (next : Value → TraceProgram) (fuel : Nat) (out : StdoutState) (terminal : Bool)
    (blocks : Nat → Option TraceProgram) :
    run_trace abstract_machine terminal blocks (fuel + 1 + steps) ((compare_bytes left right room).emit next) memory out =
      match result with
      | .ok difference => run_trace abstract_machine terminal blocks (fuel + 1) (next (.integer difference)) memory out
      | .error why => ⟨.fault why, memory, out⟩ := by
  induction comparison with
  | leftFault failed =>
    rename_i room
    cases room <;> simp [compare_bytes, perform, Bind.bind, Computation.bind, Computation.emit, run_trace,
      abstract_machine, failed]
  | rightFault loaded failed =>
    simp [compare_bytes, perform, Bind.bind, Computation.bind, Computation.emit, run_trace,
      abstract_machine, loaded, failed, apply_heap_edit]
  | stop leftRead rightRead stops =>
    rcases stops with mismatch | rfl <;>
      simp_all [compare_bytes, perform, Bind.bind, Computation.bind, Computation.emit, pure, run_trace,
        abstract_machine, apply_heap_edit]
  | @equal left x right room steps result leftRead rightRead nonzero more ih =>
    simp only [Nat.add_succ, Nat.add_zero, compare_bytes, perform, Bind.bind, Computation.bind,
      Computation.emit, run_trace, abstract_machine, id_eq, leftRead, apply_heap_edit, Option.getD_none,
      rightRead, bne_self_eq_false, beq_eq_false_iff_ne.mpr nonzero, Bool.or_self, Bool.false_eq_true, if_false]
    cases result <;> exact ih

theorem StringComparison.total (memory : HeapState) (left right : Pointer) (object : Object)
    (present : memory.objects left.capability = some object) (live : object.live = true)
    (base : 0 ≤ object.base) (fits : object.base + object.size < 2 ^ 64)
    (offset room : Nat) (address : left.address = object.base + offset) (extent : offset + room = object.size) :
    ∃ steps result, StringComparison memory left right room steps result := by
  induction room generalizing offset left right with
  | zero =>
    refine ⟨1, .error (.access .bounds), .leftFault ?_⟩
    have endAddr : left.address - object.base = object.size := by omega
    simp [heap_effect, runtime_checked, present, live, endAddr, Except.mapError, Bind.bind, Except.bind]
  | succ room ih =>
    let x := UInt8.ofNat (object.bytes offset).toNat
    have valid : runtime_checked memory.objects (some left) 1 = .ok (object, offset) := by
      have span : ¬ ((1 : Int) < 0 ∨ (offset : Int) < 0 ∨
          (object.size : Int) < offset ∨ (object.size : Int) - offset < 1) := by omega
      have displacement : left.address - object.base = (offset : Int) := by omega
      simp only [runtime_checked, present, live, Bool.true_eq_false, if_false, span, displacement, Int.toNat_natCast]
    have leftRead : heap_effect memory (.loadByte left) = .ok {reply := .byte x} := by
      simp [heap_effect, valid, x, Except.mapError, Bind.bind, Except.bind, pure, Except.pure]
    cases accessed : runtime_checked memory.objects (some right) 1 with
    | error why =>
      refine ⟨2, .error (.access why), .rightFault leftRead ?_⟩
      simp [heap_effect, accessed, Except.mapError, Bind.bind, Except.bind]
    | ok pair =>
      obtain ⟨other, index⟩ := pair
      let y := UInt8.ofNat (other.bytes index).toNat
      have rightRead : heap_effect memory (.loadByte right) = .ok {reply := .byte y} := by
        simp [heap_effect, accessed, y, Except.mapError, Bind.bind, Except.bind, pure, Except.pure]
      by_cases stop : x ≠ y ∨ x = 0
      · exact ⟨2, _, .stop leftRead rightRead stop⟩
      · have same : x = y := Classical.byContradiction (fun h => stop (Or.inl h))
        have next : (offset_pointer left 1).address = object.base + (offset + 1 : Nat) := by
          have bounded : (left.address + 1) % 18446744073709551616 = left.address + 1 :=
            Int.emod_eq_of_lt (by omega) (by change object.base + object.size < 18446744073709551616 at fits; omega)
          change (left.address + 1) % 18446744073709551616 = _
          rw [bounded, address]
          omega
        obtain ⟨steps, result, tail⟩ := ih (offset_pointer left 1) (offset_pointer right 1) present (offset + 1) next (by omega)
        exact ⟨steps + 2, result, .equal leftRead (same.symm ▸ rightRead) (fun h => stop (Or.inr h)) tail⟩

theorem strcmp_complete (memory : HeapState) (left right : Pointer)
    (bounds : ∀ obj, memory.objects left.capability = some obj →
      0 ≤ obj.base ∧ obj.base + obj.size < 2 ^ 64) :
    ∃ room steps result, StringComparison memory left right room steps result ∧
      ∀ (next : Value → TraceProgram) (fuel : Nat) (out : StdoutState) (terminal : Bool) (blocks : Nat → Option TraceProgram),
        run_trace abstract_machine terminal blocks (fuel + 1 + steps + 1)
          ((compare_strings (.pointer left) (.pointer right)).emit next) memory out =
            match result with
            | .ok difference => run_trace abstract_machine terminal blocks (fuel + 1) (next (.integer difference)) memory out
            | .error why => ⟨.fault why, memory, out⟩ := by
  cases access : runtime_checked memory.objects (some left) 1 with
  | error why =>
    have failed : heap_effect memory (.loadByte left) = .error (.access why) := by
      simp [heap_effect, access, Except.mapError, Bind.bind, Except.bind]
    refine ⟨0, 1, .error (.access why), .leftFault failed, ?_⟩
    intro next fuel out terminal blocks
    simp [compare_strings, pointer, perform, Bind.bind, Computation.bind, Computation.emit, pure, run_trace,
      abstract_machine, heap_effect, access, Except.mapError, Except.bind]
  | ok pair =>
    obtain ⟨obj, index⟩ := pair
    obtain ⟨checked, displacement⟩ := (checked_refines memory.objects left 1 index obj).mp access
    obtain ⟨present, live, lower, upper, enough⟩ := checked_sound _ _ _ _ checked
    obtain ⟨base, fits⟩ := bounds obj present
    have address : left.address = obj.base + (index : Int) := by
      rw [displacement, Int.toNat_of_nonneg (by omega)]
      omega
    obtain ⟨steps, result, comparison⟩ := StringComparison.total memory left right obj present live base fits index
      (obj.size - index) address (by omega)
    refine ⟨_, steps, result, comparison, ?_⟩
    intro next fuel out terminal blocks
    have remaining : heap_effect memory (.remaining left) = .ok { reply := .word (obj.size - index : Nat) } := by
      simp [heap_effect, access, Except.mapError, Bind.bind, Except.bind, pure, Except.pure]
    simp only [compare_strings, pointer, perform, Bind.bind, Computation.bind, Pure.pure, Computation.emit,
      run_trace, abstract_machine, id_eq, remaining, apply_heap_edit, Option.getD_none, Int.toNat_natCast]
    cases result <;> exact string_comparison_correct comparison next fuel out terminal blocks

private def set_bytes (value fill count : Value) : Computation Value := do
  let n ← integer count
  if n < 0 || n > 9223372036854775807 then return ← .fault .hostSize
  if n == 0 then return value
  let address ← pointer value
  let .word size ← perform (.remaining address) | .invalid
  if n > size then return ← .fault (.access .bounds)
  let b := byte (← integer fill)
  let rec write (ptr : Pointer) : Nat → Computation Value
    | 0 => pure value
    | left + 1 => do
      let _ ← perform (.storeByte ptr b)
      write (offset_pointer ptr 1) left
  write address n.toNat

private def file_request (op : FileRequest) : Computation HeapReply := do
  match ← perform (.file op) with
  | .pending => .suspend
  | reply => pure reply

private def transfer_file (input : Bool) (buffer size count handle : Value) : Computation Value := do
  let width ← integer size
  let length ← integer count
  let total := width * length
  if total < 0 || total > 9223372036854775807 then .fault .space else
    let handle ← pointer handle
    let _ ← file_request (.inspect handle)
    if total == 0 then return .integer 0
    let address ← pointer buffer
    let snapshot ← perform (.fileBuffer address total.toNat input)
    if input then
      let .bytes bytes ← file_request (.readFile handle total.toNat) | .invalid
      let _ ← perform (.fileCommit address total.toNat bytes)
      return .integer ((bytes.length : Int) / width)
    else
      let .bytes bytes := snapshot | .invalid
      let _ ← file_request (.writeFile handle bytes)
      return .integer length

private def library_call (function : LibraryCall) (arguments : Value) : Computation Value := do
  match function, ← argument_values arguments with
  | .synchronise op, .pointer ptr :: extra =>
    let other ← match extra with
      | [] => pure (⟨0, 0⟩ : Pointer)
      | [.pointer other] => pure other
      | _ => .invalid
    let .word result ← perform (.thread (.synchronise op ptr other)) | .invalid
    return .integer result
  | .fopen, [path, mode] =>
    let .pointer handle ← file_request (.openFile (← string_bytes path) (← string_bytes mode)) | .invalid
    return .pointer handle
  | .fclose, [handle] =>
    let .word status ← file_request (.closeFile (← pointer handle)) | .invalid
    return .integer status
  | .fread, [buffer, size, count, handle] => transfer_file true buffer size count handle
  | .fwrite, [buffer, size, count, handle] => transfer_file false buffer size count handle
  | .strlen, [value] => return .integer (← string_bytes value).length
  | .strcmp, [lhs, rhs] => compare_strings lhs rhs
  | .calloc, [count, size] => alloc ((← integer count) * (← integer size))
  | .memset, [dst, fill, count] => set_bytes dst fill count
  | .upperBound, [value] | .lowerBound, [value] =>
    let upper := match function with | .upperBound => true | _ => false
    let .pointer ptr ← perform (.bound upper (← pointer value)) | .invalid
    return .pointer ptr
  | .hasCapability, [value] | .isReadonly, [value] =>
    let ptr ← pointer value
    let op := match function with | .isReadonly => HeapEffect.readonlyCapability ptr | _ => .liveCapability ptr
    let .word live ← perform op | .invalid
    return .integer live
  | .puts, [value] => .output [← string_bytes value, [10]] (.pure (.integer 0))
  | .printf, pattern :: values =>
    let some items := format_items (← string_bytes pattern) | .invalid
    let bytes ← format_output items values
    .output [bytes] (.pure (.integer (signed 32 bytes.length)))
  | _, _ => .invalid

private def floating_value (ty : TypeCode) (bits : Nat) : Value :=
  match ty with
  | .binary32 => .ieee false bits
  | .binary64 => .ieee true bits
  | _ => .extended bits

private def truncate_real (ty : TypeCode) (value : Value) : Computation Value := do
  let (raw, fraction, bias, explicitBit) ← match value with
    | .ieee false bits => pure (bits.toNat, 23, 127, false)
    | .ieee true bits => pure (bits.toNat, 52, 1023, false)
    | .extended bits => pure (bits.toNat, 63, 16383, true)
    | _ => .invalid
  let exponentUnit := 2 ^ (fraction + if explicitBit then 1 else 0)
  let exponent := raw / exponentUnit % (2 * (bias + 1))
  if exponent == 2 * bias + 1 then return ← .fault .signedOverflow
  let significand := raw % exponentUnit + if explicitBit || exponent == 0 then 0 else 2 ^ fraction
  let shift := (max 1 exponent : Int) - bias - fraction
  let magnitude := (significand * 2 ^ shift.toNat / 2 ^ (-shift).toNat : Nat)
  let n : Int := if raw / exponentUnit ≥ 2 * (bias + 1) then -(magnitude : Int) else magnitude
  let normal := if ty.signed then signed (8 * ty.width) n else unsigned (8 * ty.width) n
  if normal != n then return ← .fault .signedOverflow
  return .integer n

private def source_cast (ty : TypeCode) (value : Value) : Computation Value := do
  if !ty.floating then return ← convert ty value
  let n ← integer value
  let signBit := match ty with
    | .binary32 => 31 | .binary64 => 63 | _ => 79
  return floating_value ty (floating_bits ty n.natAbs 1 + if n < 0 then 2 ^ signBit else 0)

private def shared_cast (types : List TypeCode) (value : Value) : Computation Value :=
  types.foldlM (fun current ty => source_cast ty current) value

private def initialiser_address (base : Value) : List Nat → Computation Value
  | [] => pure base
  | displacement :: rest => do
    initialiser_address (← add_offset 1 base (.integer displacement)) rest

private def clear (address : Value) (width : Nat) : Computation Unit := do
  let _ ← perform (.clear (← pointer address) width)
  pure ()

private def clear_slot (locals : Locals) (slot width : Nat) : Computation Unit := do
  clear (← locate locals slot) width

private def write_slot (locals : Locals) (slot : Nat) (offsets : List Nat) (ty : TypeCode) (value : Value) :
    Computation Value := do
  store ty (← initialiser_address (← locate locals slot) offsets) value

def Expression.evaluate (calls : Calls) (locals : Locals) : Expression → Computation Value
  | .truncateReal ty operand => do truncate_real ty (← operand.evaluate calls locals)
  | .compound slot width writes => do
    clear_slot locals slot width
    writes.evaluate calls locals
  | .compoundStore slot offsets ty value rest => do
    let _ ← write_slot locals slot offsets ty (← value.evaluate calls locals)
    rest.evaluate calls locals
  | .compoundEnd slot => locate locals slot
  | .spawn worker dst arg => do spawn_thread locals.globals worker (← dst.evaluate calls locals) (← arg.evaluate calls locals)
  | .join handle dst => do join_thread (← handle.evaluate calls locals) (← dst.evaluate calls locals)
  | .floatingLiteral ty _ bits => pure (floating_value ty bits)
  | .byteLiteral b => pure (.integer b.toNat)
  | .string bytes => literal_string bytes
  | .library function args => do library_call function (← args.evaluate calls locals)
  | .atomicTransfer op ty target args => do
    atomic_transfer_values op ty (← target.evaluate calls locals) (← args.evaluate calls locals)
  | .compareWord ty target successOrder expected failureOrder desired byAddress => do
    let address ← target.evaluate calls locals
    let _ ← successOrder.evaluate calls locals
    let expectation ← expected.evaluate calls locals
    let _ ← failureOrder.evaluate calls locals
    compare_word ty address expectation (← desired.evaluate calls locals) byAddress
  | .atomic op ty target ordering operand => do
    let address ← target.evaluate calls locals
    let _ ← ordering.evaluate calls locals
    atomic_word op ty address (← operand.evaluate calls locals)
  | .self => thread_self
  | .equal left right => do thread_equal (← left.evaluate calls locals) (← right.evaluate calls locals)
  | .literal n => pure (.integer n)
  | .sizeLiteral n => pure (.integer n)
  | .nullPointer => pure (.pointer ⟨0, 0⟩)
  | .slotAddress slot => locate locals slot
  | .arrayAddress slot => current_array slot
  | .globalAddress name => locate_global locals.globals name
  | .load ty address => do read ty (← address.evaluate calls locals)
  | .cast ty operand => do source_cast ty (← operand.evaluate calls locals)
  | .materialise ty operand => do materialise_value ty (← operand.evaluate calls locals)
  | .offset first second stride op =>
    do pointer_arithmetic op stride (← first.evaluate calls locals) (← second.evaluate calls locals)
  | .field base displacement => do add_offset 1 (← base.evaluate calls locals) (.integer displacement)
  | .logicalNot operand => do pure (logical (! truth (← operand.evaluate calls locals)))
  | .unary op ty operand => do unary_apply op ty (← operand.evaluate calls locals)
  | .logic conjunction lhs rhs => do
    if truth (← lhs.evaluate calls locals) == conjunction then pure (logical (truth (← rhs.evaluate calls locals)))
    else pure (logical (!conjunction))
  | .shared common fallback test result => do
    let value ← common.evaluate calls locals
    if truth (← shared_cast test value) then shared_cast result value else fallback.evaluate calls locals
  | .conditional condition yes no => do
    if truth (← condition.evaluate calls locals) then yes.evaluate calls locals else no.evaluate calls locals
  | .weakDesired left right | .comma left right => do
    let _ ← left.evaluate calls locals
    right.evaluate calls locals
  | .pointerCompare op lhs rhs =>
    do pointer_compare op (← lhs.evaluate calls locals) (← rhs.evaluate calls locals)
  | .allocate size => do alloc (← integer (← size.evaluate calls locals))
  | .move _ dst src size => do move_bytes (← dst.evaluate calls locals) (← src.evaluate calls locals) (← size.evaluate calls locals)
  | .put value => do emit_byte (← value.evaluate calls locals)
  | .release address => do release_heap (← address.evaluate calls locals)
  | .exit status => do terminate (← status.evaluate calls locals)
  | .assign ty address value =>
    if ty.aggregate_assignment then do store ty (← address.evaluate calls locals) (← value.evaluate calls locals)
    else do
      let incoming ← value.evaluate calls locals
      store ty (← address.evaluate calls locals) incoming
  | .update op storage arithmetic returnOld address value stride => do
    let incoming ← value.evaluate calls locals
    let address ← address.evaluate calls locals
    let old ← read storage address
    update_value op storage arithmetic returnOld stride address old incoming

  | .scalar op ty left right => do scalar_apply op ty (← left.evaluate calls locals) (← right.evaluate calls locals)
  | .functionAddress _ index => pure (.pointer (function_pointer index))
  | .indirect symbols ty callee arguments => do
    let target ← callee.evaluate calls locals
    let values ← argument_values (← arguments.evaluate calls locals)
    let name ← callable symbols target
    convert_result ty (← calls name values)
  | .call name ty arguments => do
    let values ← argument_values (← arguments.evaluate calls locals)
    convert_result ty (← calls name values)
  | .emptyArguments => pure (.arguments [])
  | .argument ty value rest => do
    let packed ← marshal_argument ty (← value.evaluate calls locals)
    pure (.arguments (packed :: (← argument_values (← rest.evaluate calls locals))))
  | .dimension bound rest => do
    let value ← bound.evaluate calls locals
    pure (.arguments (value :: (← argument_values (← rest.evaluate calls locals))))
  | .arrayExtent width bounds => do checked_extent width (← bounds.evaluate calls locals)
  | .arrayOffset op _ slot rank left right => do
    let first ← left.evaluate calls locals
    let second ← right.evaluate calls locals
    pointer_arithmetic op (← current_span slot rank).toNat first second
  | .arrayUpdate op slot rank returnOld address incoming => do
    let width ← current_span slot rank
    let value ← incoming.evaluate calls locals
    let place ← address.evaluate calls locals
    let old ← read .pointer place
    update_value op .pointer .pointer returnOld width.toNat place old value
  | .arraySize slot rank place => do
    let _ ← place.evaluate calls locals
    pure (.integer (← current_span slot rank))
  | .aliasSize slot => do pure (.integer (← current_span slot 0))
  | .vaStart place => do start_va locals (← place.evaluate calls locals)
  | .vaCopy destination source => do copy_va (← destination.evaluate calls locals) (← source.evaluate calls locals)
  | .vaArg ty place => do fetch_va ty (← place.evaluate calls locals)
  | .vaEnd place => do
    let _ ← place.evaluate calls locals
    pure (.integer 0)
  | .vaAvailable place => do available_va (← place.evaluate calls locals)
  | .argumentArea => current_argument_area locals


private def Computation.immediate (action : Computation Value) : Option { value // action = .pure value } :=
  match action with
  | .pure value => some ⟨value, rfl⟩
  | _ => none

def Expression.constant (expr : Expression) : Option { value // ∀ calls locals, expr.evaluate calls locals = .pure value } :=
  match expr with
  | .literal n => some ⟨.integer n, fun _ _ => rfl⟩
  | .sizeLiteral n => some ⟨.integer n, fun _ _ => rfl⟩
  | .nullPointer => some ⟨.pointer ⟨0, 0⟩, fun _ _ => rfl⟩
  | .functionAddress _ index => some ⟨.pointer (function_pointer index), fun _ _ => rfl⟩
  | .logicalNot operand => do
    let ⟨v, pureOperand⟩ ← operand.constant
    return ⟨logical (!truth v), fun calls locals => by simp only [Expression.evaluate, pureOperand]; rfl⟩
  | .cast ty operand => do
    let ⟨v, pureOperand⟩ ← operand.constant
    let ⟨result, computed⟩ ← (source_cast ty v).immediate
    return ⟨result, fun calls locals => by simpa only [Expression.evaluate, pureOperand, Bind.bind, Computation.bind] using computed⟩
  | .unary op ty operand => do
    let ⟨v, pureOperand⟩ ← operand.constant
    let ⟨result, computed⟩ ← (unary_apply op ty v).immediate
    return ⟨result, fun calls locals => by simpa only [Expression.evaluate, pureOperand, Bind.bind, Computation.bind] using computed⟩
  | .pointerCompare op left right => do
    let ⟨a, pureLeft⟩ ← left.constant
    let ⟨b, pureRight⟩ ← right.constant
    let ⟨result, computed⟩ ← (pointer_compare op a b).immediate
    return ⟨result, fun calls locals => by
      simpa only [Expression.evaluate, pureLeft, pureRight, Bind.bind, Computation.bind] using computed⟩
  | .scalar op ty left right => do
    let ⟨a, pureLeft⟩ ← left.constant
    let ⟨b, pureRight⟩ ← right.constant
    let ⟨result, computed⟩ ← (scalar_apply op ty a b).immediate
    return ⟨result, fun calls locals => by
      simpa only [Expression.evaluate, pureLeft, pureRight, Bind.bind, Computation.bind] using computed⟩
  | _ => none

theorem constant_commutes (expr : Expression) (constant : expr.constant.isSome = true) (calls : Calls) (locals : Locals)
    (other : Computation α) (next : Value → α → Computation β) :
    (do let value ← expr.evaluate calls locals; let x ← other; next value x) =
      (do let x ← other; let value ← expr.evaluate calls locals; next value x) := by
  cases found : expr.constant with
  | none => simp [found] at constant
  | some result => rw [result.property]; rfl


private def initialise_stores (calls : Calls) (locals : Locals) (base : Value) : List Initialiser → Computation Unit
  | [] => pure ()
  | init :: rest => do
    let value ← init.value.evaluate calls locals
    let address ← initialiser_address base init.offsets
    let _ ← store init.ty address value
    initialise_stores calls locals base rest

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

private def aggregate_flow (base : Value) : Option TypeCode → Computation Flow
  | none => pure .next
  | some ty => do pure (.returned (← read ty base))

private abbrev Registers := List (Nat × Value)

private def register_step (state : Registers × Option Bool) (instruction : RegisterInstruction) :
    Computation (Registers × Option Bool) := do
  let (registers, carry) := state
  let get := fun key => match registers.lookup key with
    | some value => pure value
    | none => (Computation.fault .assembly)
  let flag := match carry with
    | some value => pure (if value then (1 : Int) else 0)
    | none => (Computation.fault .assembly)
  let op := instruction.op
  if op == .clc then return (registers, some false)
  if op == .stc then return (registers, some true)
  if op == .cmc then return (registers, some ((← flag) == 0))
  let width := instruction.width
  let source ← match instruction.source with
    | .inl key => integer (← get key)
    | .inr word => pure word
  let right := unsigned width source
  let left ← if op == .mov || op == .setc then pure 0 else do
    pure (unsigned width (← integer (← get instruction.destination)))
  let count := right.toNat % (if width == 64 then 64 else 32)
  let rotation := count % width
  let addition := fun (extra : Int) =>
    let result := left + right + extra
    (result, some (decide (result ≥ 2 ^ width)))
  let subtraction := fun (extra : Int) =>
    let result := left - right - extra
    (result, some (decide (result < 0)))
  let shift := fun (result : Int) bit defined =>
    if count == 0 then (left, carry)
    else (result, if defined then some (left.toNat.testBit bit) else none)
  let rotate := fun (result : Nat) bit =>
    ((result : Int), if count == 0 then carry else some (result.testBit bit))
  let (word, updated) ← match op with
    | .mov => pure (right, carry)
    | .setc => pure (← flag, carry)
    | .add => pure (addition 0)
    | .adc => pure (addition (← flag))
    | .sub => pure (subtraction 0)
    | .sbb => pure (subtraction (← flag))
    | .cmp => pure (left, some (decide (left < right)))
    | .inc => pure (left + 1, carry)
    | .dec => pure (left - 1, carry)
    | .neg => pure (-left, some (left != 0))
    | .inv => pure (-left - 1, carry)
    | .band => pure (Int.ofNat (left.toNat &&& right.toNat), some false)
    | .bor => pure (Int.ofNat (left.toNat ||| right.toNat), some false)
    | .bxor => pure (Int.ofNat (left.toNat ^^^ right.toNat), some false)
    | .shl => pure (shift (left * 2 ^ count) (width - count) (decide (count < width)))
    | .shr => pure (shift (left / 2 ^ count) (count - 1) (decide (count < width)))
    | .sar => pure (shift (signed width left / 2 ^ count) (min (width - 1) (count - 1)) true)
    | .rol => pure (rotate ((left.toNat <<< rotation) ||| (left.toNat >>> (width - rotation))) 0)
    | .ror => pure (rotate ((left.toNat >>> rotation) ||| (left.toNat <<< (width - rotation))) (width - 1))
    | .clc | .stc | .cmc => .invalid
  return ((instruction.destination, .integer (unsigned width word)) :: registers, updated)

private def run_registers (block : RegisterBlock) (operands : Value) : Computation Unit := do
  let values ← argument_values operands
  let _ ← perform (.critical true)
  let destinations := block.outputs.zip (values.take block.outputs.length)
  let mut registers : Registers := []
  for (((ty, readWrite), place), key) in destinations.zipIdx do
    if readWrite then registers := (key, ← read ty place) :: registers
  for input in block.inputs.zip (values.drop block.outputs.length) do
    registers := input :: registers
  let (result, _) ← block.instructions.foldlM register_step (registers, none)
  for (((ty, _), place), key) in destinations.zipIdx do
    let some value := result.lookup key | return ← .fault .assembly
    let _ ← store ty place value
  let _ ← perform (.critical false)
  pure ()

private def execute (calls : Calls) (locals : Locals) (iterations : Nat) : Statement → Computation Flow
  | .empty | .skip | .arrayProbe => pure .next
  | .assembly block operands => do
    run_registers block (← operands.evaluate calls locals)
    pure .next
  | .declareArray slot width bounds typeOnly => do
    declare_array slot width typeOnly (← bounds.evaluate calls locals)
    pure .next
  | .arrayFromAlias slot source => do
    instantiate_array slot source
    pure .next
  | .initialiseArrayPointer slot width bounds initializer => do
    let place ← locate locals slot
    bind_array_shape slot width 0 place (← bounds.evaluate calls locals)
    if let some value := initializer then
      let _ ← store .pointer place (← value.evaluate calls locals)
      pure ()
    pure .next
  | .uninitialised slot => do
    let _ ← locate locals slot
    pure .next
  | .sequence first rest => sequence (execute calls locals iterations first) (execute calls locals iterations rest)
  | .declarations body | .block body => execute calls locals iterations body
  | .initialiseAtomic slot ty value => do
    let place ← locate locals slot
    let _ ← atomic_word .initialise ty place (← value.evaluate calls locals)
    pure .next
  | .initialise slot ty value => do
    let _ ← store ty (← locate locals slot) (← value.evaluate calls locals)
    pure .next
  | .initialiseAggregate slot width stores result => do
    let base ← locate locals slot
    clear base width
    initialise_stores calls locals base stores
    aggregate_flow base result
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
  | empty | skip | arrayProbe | stop | restart => rfl
  | uninitialised slot => exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => rfl)
  | assembly _ operands | declareArray _ _ operands _ =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro arguments _
    exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => rfl)
  | arrayFromAlias slot source => exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => rfl)
  | initialiseArrayPointer slot width bounds initializer =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro place _
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro extents _
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro _ _
    cases initializer with
    | none => rfl
    | some value =>
      apply Computation.all_bind _ _ (Computation.all_values _)
      intro _ _
      exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => rfl)
  | sequence first rest head tail => exact sequence_exits head tail
  | declarations body allowed | block body allowed => exact allowed
  | initialiseAtomic slot ty value | initialise slot ty value =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro address _
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro initial _
    exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => rfl)
  | initialiseAggregate slot width stores result =>
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro base _
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro _ _
    apply Computation.all_bind _ _ (Computation.all_values _)
    intro _ _
    cases result with
    | none => rfl
    | some ty => exact Computation.all_bind _ _ (Computation.all_values _) (fun _ _ => trivial)
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

private theorem structured_control_correct (statement : Statement) (allowNext : Bool)
    (calls : Calls) (locals : Locals) (iterations : Nat) (checked : statement.exits.allowed allowNext = true) :
    (execute calls locals iterations statement).all (fun flow => match flow with
      | .returned _ => True
      | .next => allowNext = true
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

private def loaded_label (registry targets : List String) : Value → Computation String
  | .pointer ptr =>
    match resolve_function registry ptr with
    | some name => if targets.contains name then pure name else .fault .invalidFunction
    | none => .fault .invalidFunction
  | _ => .fault .invalidFunction

theorem loaded_label_iff (registry targets : List String) (ptr : Pointer) (name : String) :
    loaded_label registry targets (.pointer ptr) = .pure name ↔
      name ∈ targets ∧ ∃ index, ptr = function_pointer index ∧ registry[index]? = some name := by
  rw [← resolve_function_iff]
  cases found : resolve_function registry ptr with
  | none => simp [loaded_label, found]
  | some candidate =>
    by_cases localTarget : candidate ∈ targets
    · simp [loaded_label, found, localTarget, pure, Computation.pure.injEq]
      exact fun equal => equal ▸ localTarget
    · simp [loaded_label, found, localTarget]
      exact fun member equal => localTarget (equal.symm ▸ member)

private def LabelChoice.evaluate (calls : Calls) (locals : Locals) : LabelChoice → Computation String
  | .address symbol => pure symbol
  | .loaded expr registry targets => do loaded_label registry targets (← expr.evaluate calls locals)
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

private theorem dispatch_control_correct (dispatch : Dispatch) (allowNext : Bool) (calls : Calls) (locals : Locals)
    (depth steps index : Nat) (checked : dispatch.control_checked allowNext = true)
    (reachable : index ∈ dispatch.region) :
    (execute_dispatch dispatch calls locals depth steps index).all (fun flow => match flow with
      | .returned _ => True
      | .next => allowNext = true
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
      | .next => procedure.may_fall_through = true
      | .stop | .restart => False) := by
  cases graph : procedure.dispatch with
  | none =>
    simp only [Procedure.control_checked, graph] at checked
    simpa only [Procedure.execute, graph] using
      structured_control_correct procedure.statements procedure.may_fall_through calls locals depth checked
  | some dispatch =>
    simp only [Procedure.control_checked, graph] at checked
    have entry : dispatch.entry ∈ dispatch.region := by
      simp only [Dispatch.control_checked, Bool.and_eq_true, List.contains_iff_mem] at checked
      exact checked.2.1
    simpa only [Procedure.execute, graph] using
      dispatch_control_correct dispatch procedure.may_fall_through calls locals depth depth dispatch.entry checked entry

private def allocate_locals : List (Option Nat) → Computation (List (Option Value))
  | [] => pure []
  | none :: rest => do pure (none :: (← allocate_locals rest))
  | some width :: rest => do pure (some (← alloc width false) :: (← allocate_locals rest))

private def allocate_parameters : List TypeCode → List Value → Computation (List Value)
  | [], [] => pure []
  | ty :: types, value :: values => do
    let address ← alloc ty.width false
    let _ ← store ty address value.unpacked
    return address :: (← allocate_parameters types values)
  | _, _ => .invalid

private def capture_parameters (calls : Calls) (locals : Locals) : List ParameterShape → Computation Unit
  | [] => pure ()
  | shape :: rest => do
    let address ← locate locals shape.slot
    let sizes ← shape.bounds.evaluate calls locals
    bind_array_shape shape.slot shape.elementWidth shape.skip address sizes
    capture_parameters calls locals rest

private def Procedure.has_array_frame (procedure : Procedure) : Bool :=
  procedure.shapedLocals || !procedure.shapes.isEmpty || procedure.locals.any Option.isNone

private def Procedure.open_frame (procedure : Procedure) : Computation Unit := do
  if procedure.has_array_frame then
    let _ ← perform .enterArrayFrame
    pure ()

private def Procedure.argument_area (procedure : Procedure) (values : List Value) : Computation (Option Value) :=
  if procedure.introspects then some <$> construct_argument_area values else pure none

private def Procedure.frame (procedure : Procedure) (calls : Calls) (globals : Globals) (values : List Value) :
    Computation Locals := do
  procedure.open_frame
  let area ← procedure.argument_area values
  let arguments ← allocate_parameters procedure.parameters (values.take procedure.parameters.length)
  let locals : Locals := ⟨arguments.map some, globals, area, procedure.parameters⟩
  capture_parameters calls locals procedure.shapes
  return { locals with slots := locals.slots ++ (← allocate_locals procedure.locals) }

private def Procedure.return_value (procedure : Procedure) (flow : Flow) : Computation Value := do
  let value ← flow.result
  if procedure.has_array_frame then
    let _ ← perform .leaveArrayFrame
    pure ()
  convert_result procedure.resultType value

private def allocate_globals : List Global → Computation Globals
  | [] => pure []
  | object :: rest => do
    match ← perform (.allocateGlobal object.width) with
    | .pointer address => return (object.name, .pointer address) :: (← allocate_globals rest)
    | _ => .invalid

private def UnitBody.objects (unit : UnitBody) (threadLocal : Bool) :=
  unit.globals.filter (fun object => object.threadLocal == threadLocal)

private def Program.objects (program : Program) (threadLocal : Bool) :=
  program.units.flatMap (fun unit => unit.objects threadLocal)

private def Program.initialisations (program : Program) (threadLocal : Bool) : List (Global ⊕ String) :=
  program.units.flatMap fun unit =>
    let objects := unit.objects threadLocal
    objects.map Sum.inl ++ (objects.filter (·.readOnly)).map (fun object => Sum.inr object.name)

private def freeze_global (globals : Globals) (name : String) : Computation Unit := do
  let address ← pointer (← locate_global globals name)
  let _ ← perform (.freeze address)

private def initialise_globals (globals : Globals) : List (Global ⊕ String) → Computation Unit
  | [] => pure ()
  | .inr name :: rest => do
    freeze_global globals name
    initialise_globals globals rest
  | .inl object :: rest => do
    if !object.initialisers.isEmpty then
      let address ← locate_global globals object.name
      initialise_stores (fun _ _ => .invalid) ⟨[], globals, none, []⟩ address object.initialisers
    initialise_globals globals rest

def install_globals (fresh inherited : Globals) : Globals :=
  fresh ++ inherited.filter (fun entry => (fresh.lookup entry.1).isNone)

theorem install_globals_lookup (fresh inherited : Globals) (key : String) :
    (install_globals fresh inherited).lookup key = (fresh.lookup key).or (inherited.lookup key) := by
  unfold install_globals
  rw [List.lookup_append]
  cases found : fresh.lookup key with
  | some _ => rfl
  | none =>
    change (inherited.filter _).lookup key = inherited.lookup key
    induction inherited with
    | nil => rfl
    | cons entry rest ih =>
      obtain ⟨name, address⟩ := entry
      by_cases same : key = name
      · subst name
        simp [found]
      · have different : (key == name) = false := by simpa using same
        cases present : fresh.lookup name <;> simp [List.lookup_cons, present, different, ih]

private def Program.storage (program : Program) (threadLocal : Bool) (inherited : Globals) : Computation Globals := do
  let objects := program.objects threadLocal
  let fresh ← allocate_globals objects
  let globals := install_globals fresh inherited
  initialise_globals globals (program.initialisations threadLocal)
  pure globals

private def Program.register_root (program : Program) : Computation Unit := do
  if program.parallel then
    let handle ← alloc 0 false
    let _ ← request (.root (← pointer handle))

private def Program.startup (program : Program) : Computation Globals := do
  let globals ← program.storage false []
  program.register_root
  program.storage true globals

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

private def kernel_value (arity : Nat) (evaluate : (Nat → Int) → Int) (values : List Value) : Computation Value := do
  if values.length < arity then .invalid else
    let words ← (values.take arity).mapM integer
    pure (.integer (unsigned 64 (evaluate (fun slot => words[slot]?.getD 0))))

private def external_call (name : String) (arguments : List Value) : Computation Value :=
  if name == "pthread_self" && arguments.isEmpty then thread_self else .invalid

private def source_calls (program : Program) (globals : Globals) : Nat → Calls
  | 0, _, _ => .suspend
  | depth + 1, name, values => .tick <| do
    match program.lookup name with
    | none => external_call name values
    | some procedure => match procedure.kernel with
      | some kernel => kernel_value procedure.parameters.length (fun slots => source_eval slots kernel.expression) values
      | none => do
        let locals ← procedure.frame (source_calls program globals depth) globals values
        let flow ← procedure.execute (source_calls program globals depth) locals depth
        procedure.return_value flow

def Program.source (program : Program) (depth : Nat) (invocation : Invocation := {}) : Computation Int := do
  let globals ← program.startup
  let arguments ← argument_vector invocation
  integer (← source_calls program globals depth "main" (program.entry_arguments arguments))

private abbrev Action (α : Type) := (α → TraceProgram) → TraceProgram

private def action (source : Computation α) : Action α := source.emit

private abbrev LoweredCalls := String → List Value → Action Value

private def lower (linked : LoweredCalls) (locals : Locals) : Expression → Action Value
  | .truncateReal ty operand, next => lower linked locals operand fun value => action (truncate_real ty value) next
  | .compound slot width writes, next => action (clear_slot locals slot width) fun _ =>
    lower linked locals writes next
  | .compoundStore slot offsets ty value rest, next => lower linked locals value fun v =>
    action (write_slot locals slot offsets ty v) fun _ => lower linked locals rest next
  | .compoundEnd slot, next => action (locate locals slot) next
  | .spawn worker dst arg, next => lower linked locals dst fun place =>
    lower linked locals arg fun value => action (spawn_thread locals.globals worker place value) next
  | .join handle dst, next => lower linked locals handle fun child =>
    lower linked locals dst fun place => action (join_thread child place) next
  | .floatingLiteral ty _ bits, next => next (floating_value ty bits)
  | .byteLiteral b, next => next (.integer b.toNat)
  | .string bytes, next => action (literal_string bytes) next
  | .library function args, next => lower linked locals args fun values => action (library_call function values) next
  | .atomicTransfer op ty target args, next => lower linked locals target fun address =>
    lower linked locals args fun values => action (atomic_transfer_values op ty address values) next
  | .compareWord ty target successOrder expected failureOrder desired byAddress, next =>
    lower linked locals target fun address => lower linked locals successOrder fun _ =>
      lower linked locals expected fun expectation => lower linked locals failureOrder fun _ =>
        lower linked locals desired fun value => action (compare_word ty address expectation value byAddress) next
  | .atomic op ty target ordering operand, next => lower linked locals target fun address =>
    lower linked locals ordering fun _ => lower linked locals operand fun value => action (atomic_word op ty address value) next
  | .self, next => action thread_self next
  | .equal left right, next => lower linked locals left fun lhs =>
    lower linked locals right fun rhs => action (thread_equal lhs rhs) next
  | .literal n, next => next (.integer n)
  | .sizeLiteral n, next => next (.integer n)
  | .nullPointer, next => next (.pointer ⟨0, 0⟩)
  | .slotAddress slot, next => action (locate locals slot) next
  | .arrayAddress slot, next => action (current_array slot) next
  | .globalAddress name, next => action (locate_global locals.globals name) next
  | .load ty address, next => lower linked locals address fun value => action (read ty value) next
  | .cast ty operand, next => lower linked locals operand fun value => action (source_cast ty value) next
  | .materialise ty operand, next => lower linked locals operand fun value => action (materialise_value ty value) next
  | .offset first second stride op, next =>
    lower linked locals first fun l => lower linked locals second fun r => action (pointer_arithmetic op stride l r) next
  | .field base displacement, next => lower linked locals base fun b => action (add_offset 1 b (.integer displacement)) next
  | .logicalNot operand, next => lower linked locals operand fun value => next (logical (! truth value))
  | .unary op ty operand, next => lower linked locals operand fun value => action (unary_apply op ty value) next
  | .logic conjunction lhs rhs, next => lower linked locals lhs fun result =>
    if truth result == conjunction then lower linked locals rhs fun value => next (logical (truth value))
    else next (logical (!conjunction))
  | .shared common fallback test result, next => lower linked locals common fun value =>
    action (shared_cast test value) fun tested =>
      if truth tested then action (shared_cast result value) next else lower linked locals fallback next
  | .conditional condition yes no, next => lower linked locals condition fun value =>
    if truth value then lower linked locals yes next else lower linked locals no next
  | .weakDesired left right, next | .comma left right, next => lower linked locals left fun _ => lower linked locals right next
  | .pointerCompare op lhs rhs, next => lower linked locals lhs fun first =>
    lower linked locals rhs fun second => action (pointer_compare op first second) next
  | .allocate size, next => lower linked locals size fun n =>
    action (integer n) fun size => action (alloc size) next
  | .move _ dst src size, next => lower linked locals dst fun d => lower linked locals src fun s =>
    lower linked locals size fun count => action (move_bytes d s count) next
  | .put value, next => lower linked locals value fun n => action (emit_byte n) next
  | .release address, next => lower linked locals address fun p => action (release_heap p) next
  | .exit status, next => lower linked locals status fun code => action (terminate code) next
  | .assign ty address value, next =>
    if ty.aggregate_assignment then lower linked locals address fun p =>
      lower linked locals value fun v => action (store ty p v) next
    else lower linked locals value fun v =>
      lower linked locals address fun p => action (store ty p v) next
  | .update op storage arithmetic returnOld address value stride, next => lower linked locals value fun v =>
    lower linked locals address fun p => action (read storage p) fun old =>
      action (update_value op storage arithmetic returnOld stride p old v) next

  | .scalar op ty left right, next => lower linked locals left fun l =>
    lower linked locals right fun r => action (scalar_apply op ty l r) next
  | .functionAddress _ index, next => next (.pointer (function_pointer index))
  | .indirect symbols ty callee arguments, next => lower linked locals callee fun target =>
    lower linked locals arguments fun args => action (argument_values args) fun values =>
      action (callable symbols target) fun name => linked name values fun result => action (convert_result ty result) next
  | .call name ty arguments, next => lower linked locals arguments fun args =>
    action (argument_values args) fun values => linked name values fun result => action (convert_result ty result) next
  | .emptyArguments, next => next (.arguments [])
  | .argument ty value rest, next => lower linked locals value fun v =>
    action (marshal_argument ty v) fun packed => lower linked locals rest fun args =>
    action (argument_values args) fun values => next (.arguments (packed :: values))
  | .dimension bound rest, next => lower linked locals bound fun value =>
    lower linked locals rest fun args =>
      action (argument_values args) fun values => next (.arguments (value :: values))
  | .arrayExtent width bounds, next => lower linked locals bounds fun args => action (checked_extent width args) next
  | .arrayOffset op _ slot rank left right, next =>
    lower linked locals left fun first => lower linked locals right fun second =>
      action (current_span slot rank) fun width => action (pointer_arithmetic op width.toNat first second) next
  | .arrayUpdate op slot rank returnOld address incoming, next =>
    action (current_span slot rank) fun width =>
      lower linked locals incoming fun value =>
        lower linked locals address fun place =>
          action (read .pointer place) fun old =>
            action (update_value op .pointer .pointer returnOld width.toNat place old value) next
  | .arraySize slot rank place, next =>
    lower linked locals place fun _ => action (current_span slot rank) fun width => next (.integer width)
  | .aliasSize slot, next => action (current_span slot 0) fun width => next (.integer width)
  | .vaStart place, next => lower linked locals place fun address => action (start_va locals address) next
  | .vaCopy destination source, next => lower linked locals destination fun target =>
    lower linked locals source fun address => action (copy_va target address) next
  | .vaArg ty place, next => lower linked locals place fun address => action (fetch_va ty address) next
  | .vaEnd place, next => lower linked locals place fun _ => next (.integer 0)
  | .vaAvailable place, next => lower linked locals place fun address => action (available_va address) next
  | .argumentArea, next => action (current_argument_area locals) next

private theorem lower_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (locals : Locals) (expression : Expression) (next : Value → TraceProgram) :
    lower linked locals expression next = (expression.evaluate calls locals).emit next := by
  induction expression generalizing next <;>
    simp only [lower, Expression.evaluate, action, emit_monad_bind, emit_pure, *]
  case assign ty address value _ _ =>
    split <;> simp only [*, emit_monad_bind]
  case shared common fallback test result _ _ =>
    apply congrArg (fun k => (common.evaluate calls locals).emit k)
    funext value
    apply congrArg (fun k => (shared_cast test value).emit k)
    funext tested
    split <;> rfl
  case logic conjunction lhs rhs _ _ =>
    apply congrArg (fun continuation => (lhs.evaluate calls locals).emit continuation)
    funext value
    split <;> simp [*]
  case conditional condition yes no _ _ _ =>
    apply congrArg (fun continuation => (condition.evaluate calls locals).emit continuation)
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
      action (initialiser_address base init.offsets) fun address =>
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
  | .empty, next | .skip, next | .arrayProbe, next => next .next
  | .assembly block operands, next =>
    lower linked locals operands fun values => action (run_registers block values) fun _ => next .next
  | .declareArray slot width bounds typeOnly, next =>
    lower linked locals bounds fun arguments => action (declare_array slot width typeOnly arguments) fun _ => next .next
  | .arrayFromAlias slot source, next => action (instantiate_array slot source) fun _ => next .next
  | .uninitialised slot, next => action (locate locals slot) fun _ => next .next
  | .initialiseArrayPointer slot width bounds initializer, next => action (locate locals slot) fun place =>
    lower linked locals bounds fun extents => action (bind_array_shape slot width 0 place extents) fun _ =>
      match initializer with
      | none => next .next
      | some value => lower linked locals value fun incoming => action (store .pointer place incoming) fun _ => next .next
  | .sequence first rest, next =>
    lower_sequence (lower_statements linked locals iterations first) (lower_statements linked locals iterations rest) next
  | .declarations body, next | .block body, next => lower_statements linked locals iterations body next
  | .initialiseAtomic slot ty value, next => action (locate locals slot) fun address =>
    lower linked locals value fun v => action (atomic_word .initialise ty address v) fun _ => next .next
  | .initialise slot ty value, next => action (locate locals slot) fun address =>
    lower linked locals value fun v => action (store ty address v) fun _ => next .next
  | .initialiseAggregate slot width stores result, next => action (locate locals slot) fun base =>
    action (clear base width) fun _ => lower_stores linked locals base stores fun _ => action (aggregate_flow base result) next
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
  | initialise | initialiseAtomic | declareArray | assembly | arrayFromAlias | uninitialised | discard | result =>
    simp only [lower_statements, execute, expression, action, emit_monad_bind, emit_pure]
  | initialiseArrayPointer slot width bounds initializer =>
    cases initializer <;> simp only [lower_statements, execute, expression, action, emit_monad_bind, emit_pure]
  | initialiseAggregate =>
    simp only [lower_statements, execute, action, lower_stores_correct calls linked related, emit_monad_bind]
  | declarations body correct | block body correct => exact correct next
  | empty | skip | arrayProbe | stop | restart | gotoLabel | indirect | label | select | caseOf => rfl

private def lower_label (linked : LoweredCalls) (locals : Locals) : LabelChoice → Action String
  | .address symbol, next => next symbol
  | .loaded expr registry targets, next => lower linked locals expr fun value => action (loaded_label registry targets value) next
  | .conditional condition yes no, next => lower linked locals condition fun value =>
    if truth value then lower_label linked locals yes next else lower_label linked locals no next

private theorem lower_label_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (locals : Locals) (choice : LabelChoice) (next : String → TraceProgram) :
    lower_label linked locals choice next = (choice.evaluate calls locals).emit next := by
  induction choice with
  | address => rfl
  | loaded => simp only [lower_label, LabelChoice.evaluate, lower_correct calls linked related, emit_monad_bind, action]
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

private def lower_parameters (linked : LoweredCalls) (locals : Locals) : List ParameterShape → Action Unit
  | [], next => next ()
  | shape :: rest, next =>
    action (locate locals shape.slot) fun address => lower linked locals shape.bounds fun bounds =>
      action (bind_array_shape shape.slot shape.elementWidth shape.skip address bounds) fun _ =>
        lower_parameters linked locals rest next

private theorem lower_parameters_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (locals : Locals) (shapes : List ParameterShape) (next : Unit → TraceProgram) :
    lower_parameters linked locals shapes next = (capture_parameters calls locals shapes).emit next := by
  induction shapes with
  | nil => rfl
  | cons shape rest ih =>
    simp only [lower_parameters, capture_parameters, action, emit_monad_bind, ih, lower_correct calls linked related]

private def Procedure.lower_frame (procedure : Procedure) (linked : LoweredCalls) (globals : Globals)
    (values : List Value) : Action Locals := fun next =>
  action procedure.open_frame fun _ =>
    action (procedure.argument_area values) fun area =>
      action (allocate_parameters procedure.parameters (values.take procedure.parameters.length)) fun arguments =>
        let locals : Locals := ⟨arguments.map some, globals, area, procedure.parameters⟩
        lower_parameters linked locals procedure.shapes fun _ =>
          action (allocate_locals procedure.locals) fun frame => next { locals with slots := locals.slots ++ frame }

private theorem lower_frame_correct (calls : Calls) (linked : LoweredCalls)
    (related : ∀ name arguments next, linked name arguments next = (calls name arguments).emit next)
    (procedure : Procedure) (globals : Globals) (values : List Value) (next : Locals → TraceProgram) :
    procedure.lower_frame linked globals values next = (procedure.frame calls globals values).emit next := by
  simp only [Procedure.lower_frame, Procedure.frame, action, emit_monad_bind, emit_pure,
    lower_parameters_correct calls linked related]

private def target_calls (program : Program) (globals : Globals) : Nat → LoweredCalls
  | 0, _, _, _ => .jump 1
  | depth + 1, name, arguments, next => .tick <|
    match program.lookup name with
    | none => action (external_call name arguments) next
    | some procedure => match procedure.kernel with
      | some kernel => action (kernel_value procedure.parameters.length
          (fun slots => target_eval slots (Heresy.lower kernel.expression)) arguments) next
      | none => procedure.lower_frame (target_calls program globals depth) globals arguments fun locals =>
        procedure.lower (target_calls program globals depth) locals depth fun flow =>
          action (procedure.return_value flow) next

theorem calls_correct (program : Program) (globals : Globals) (depth : Nat) (name : String) (arguments : List Value)
    (next : Value → TraceProgram) :
    target_calls program globals depth name arguments next = (source_calls program globals depth name arguments).emit next := by
  induction depth generalizing name arguments next with
  | zero => rfl
  | succ depth ih =>
    cases found : program.lookup name with
    | none => simp [target_calls, source_calls, found, Computation.emit, action]
    | some procedure =>
      cases chosen : procedure.kernel with
      | some kernel =>
        simp only [target_calls, source_calls, found, chosen, action, Heresy.lower_correct, Computation.emit]
      | none =>
        simp only [target_calls, source_calls, found, chosen, action, Computation.emit, emit_monad_bind,
          lower_frame_correct (source_calls program globals depth) (target_calls program globals depth) ih,
          lower_procedure_correct (source_calls program globals depth) (target_calls program globals depth) ih]

private def worker_result (value : Value) : TraceProgram :=
  match value with
  | .pointer result => .effect (.thread (.publish result)) fun _ => .jump 1
  | _ => .jump 0

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

private def lower_initialisers (globals : Globals) : List (Global ⊕ String) → Action Unit
  | [], next => next ()
  | .inr name :: rest, next => action (freeze_global globals name) fun _ => lower_initialisers globals rest next
  | .inl object :: rest, next =>
    if object.initialisers.isEmpty then lower_initialisers globals rest next
    else
      action (locate_global globals object.name) fun address =>
        lower_stores no_linked_calls ⟨[], globals, none, []⟩ address object.initialisers fun _ =>
          lower_initialisers globals rest next

private theorem lower_initialisers_correct (globals : Globals) (objects : List (Global ⊕ String))
    (next : Unit → TraceProgram) :
    lower_initialisers globals objects next = (initialise_globals globals objects).emit next := by
  induction objects generalizing next with
  | nil => rfl
  | cons object rest ih =>
    cases object with
    | inr name => simp only [lower_initialisers, initialise_globals, action, ih, emit_monad_bind]
    | inl object =>
      cases empty : object.initialisers.isEmpty <;>
        simp [lower_initialisers, initialise_globals, empty, action,
          lower_stores_correct no_calls no_linked_calls (fun _ _ _ => rfl), ih]
      rfl

private def Program.lower_storage (program : Program) (threadLocal : Bool) (inherited : Globals) : Action Globals :=
  fun next => lower_allocations (program.objects threadLocal) fun fresh =>
    let globals := install_globals fresh inherited
    lower_initialisers globals (program.initialisations threadLocal) fun _ => next globals

private theorem lower_storage_correct (program : Program) (threadLocal : Bool) (inherited : Globals)
    (next : Globals → TraceProgram) :
    program.lower_storage threadLocal inherited next = (program.storage threadLocal inherited).emit next := by
  simp only [Program.lower_storage, Program.storage, lower_allocations_correct, lower_initialisers_correct,
    emit_monad_bind, emit_pure]

def Program.worker (program : Program) (depth : Nat) (globals : List (String × Pointer)) (name : String)
    (argument : Pointer) : TraceProgram :=
  program.lower_storage true (globals.map fun (key, ptr) => (key, .pointer ptr)) fun environment =>
    target_calls program environment depth name [.pointer argument] worker_result

def Program.sourceWorker (program : Program) (depth : Nat) (globals : List (String × Pointer)) (name : String)
    (argument : Pointer) : TraceProgram :=
  (program.storage true (globals.map fun (key, ptr) => (key, .pointer ptr))).emit fun environment =>
    (source_calls program environment depth name [.pointer argument]).emit worker_result

theorem worker_correct (program : Program) (depth : Nat) : program.worker depth = program.sourceWorker depth := by
  funext globals name argument
  simp only [Program.worker, Program.sourceWorker, lower_storage_correct, calls_correct]

def Program.target (program : Program) (depth : Nat) (invocation : Invocation := {}) : TraceProgram :=
  program.lower_storage false [] fun shared =>
    action program.register_root fun _ =>
      program.lower_storage true shared fun globals =>
        action (argument_vector invocation) fun arguments =>
          target_calls program globals depth "main" (program.entry_arguments arguments) fun value => action (integer value) .finish

theorem lower_program_correct (program : Program) (depth : Nat) (invocation : Invocation) :
    program.target depth invocation = (program.source depth invocation).emit .finish := by
  simp only [Program.target, Program.source, Program.startup, lower_storage_correct,
    calls_correct, action, emit_monad_bind]

def blocks : Nat → Option TraceProgram
  | 1 => some (.jump 1)
  | _ => none

def Program.observation (program : Program) (fuel : Nat) (terminal : Bool) (invocation : Invocation := {}) :=
  (run_trace sparse_machine terminal blocks fuel (program.target fuel invocation) ⟨[], ⟨1, 4096⟩, [], [], { events := invocation.files }⟩
    ⟨[], [], 0, true⟩).snapshot.observation

def Program.source_observation (program : Program) (fuel : Nat) (terminal : Bool) (invocation : Invocation := {}) :=
  (run_trace abstract_machine terminal blocks fuel ((program.source fuel invocation).emit .finish)
    ⟨fun _ => none, ⟨1, 4096⟩, [], [], { events := invocation.files }⟩ ⟨[], [], true⟩).observation

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
  | output {outByte : List (List UInt8)} : Agrees fuel left right → Agrees (fuel + 1) (.output outByte left) (.output outByte right)
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
  | truncateReal _ _ ih => exact ih.bind fun _ => .refl _ _
  | compound slot width writes ih => exact (Agrees.refl fuel (clear_slot locals slot width)).bind fun _ => ih
  | compoundStore slot offsets ty value rest iv ir =>
    exact iv.bind fun v => (Agrees.refl fuel (write_slot locals slot offsets ty v)).bind fun _ => ir
  | compoundEnd => exact .refl _ _
  | functionAddress | floatingLiteral | byteLiteral | string | literal | sizeLiteral | nullPointer | slotAddress | arrayAddress | globalAddress | emptyArguments | aliasSize | argumentArea | self =>
    exact .refl _ _
  | load _ _ ih | cast _ _ ih | materialise _ _ ih | field _ _ ih | logicalNot _ ih | unary _ _ _ ih
  | library _ _ ih | put _ ih | release _ ih | exit _ ih | vaStart _ ih | vaArg _ _ ih | vaEnd _ ih | vaAvailable _ ih
  | arraySize _ _ _ ih =>
    exact ih.bind (fun _ => .refl _ _)
  | atomicTransfer _ _ _ _ target args => exact target.bind fun _ => args.bind fun _ => .refl _ _
  | compareWord _ _ _ _ _ _ _ target successOrder expected failureOrder desired =>
    exact target.bind fun _ => successOrder.bind fun _ => expected.bind fun _ =>
      failureOrder.bind fun _ => desired.bind fun _ => .refl _ _
  | atomic _ _ _ _ _ target order operand =>
    exact target.bind (fun _ => order.bind (fun _ => operand.bind (fun _ => .refl _ _)))
  | spawn _ _ _ il ir | join _ _ il ir | equal _ _ il ir
  | offset _ _ _ _ il ir | scalar _ _ _ _ il ir | vaCopy _ _ il ir =>
    exact il.bind (fun _ => ir.bind (fun _ => .refl _ _))
  | assign ty _ _ address value =>
    simp only [Expression.evaluate]
    split
    · exact address.bind (fun _ => value.bind (fun _ => .refl _ _))
    · exact value.bind (fun _ => address.bind (fun _ => .refl _ _))
  | pointerCompare _ _ _ il ir =>
    exact il.bind (fun _ => ir.bind (fun _ => .refl _ _))
  | shared _ _ _ _ common fallback =>
    apply common.bind
    intro value
    apply (Agrees.refl fuel (shared_cast _ value)).bind
    intro tested
    split
    · exact .refl _ _
    · exact fallback
  | logic _ _ _ il ir =>
    apply il.bind
    intro value
    split
    · exact ir.bind (fun _ => .refl _ _)
    · exact .refl _ _
  | conditional _ _ _ ic iy ino =>
    apply ic.bind
    intro value
    split
    · exact iy
    · exact ino
  | weakDesired _ _ il ir | comma _ _ il ir => exact il.bind (fun _ => ir)
  | update _ _ _ _ _ _ _ address value =>
    exact value.bind (fun _ => address.bind (fun _ => (Agrees.refl _ _).bind (fun _ => .refl _ _)))
  | allocate _ ih => exact ih.bind (fun _ => (Agrees.refl _ _).bind (fun _ => .refl _ _))
  | move _ _ _ _ idst isrc isize =>
    exact idst.bind (fun _ => isrc.bind (fun _ => isize.bind (fun _ => .refl _ _)))
  | indirect symbols _ _ _ callee args =>
    exact callee.bind (fun target => args.bind (fun values => (Agrees.refl fuel (argument_values values)).bind (fun actuals =>
      (Agrees.refl fuel (callable symbols target)).bind (fun name => (calls name actuals).bind (fun _ => .refl _ _)))))
  | call name _ _ ih =>
    exact ih.bind (fun _ => (Agrees.refl _ _).bind (fun actuals =>
      (calls name actuals).bind (fun _ => .refl _ _)))
  | argument _ _ _ iv ir =>
    exact iv.bind (fun _ => (Agrees.refl _ _).bind (fun _ =>
      ir.bind (fun _ => (Agrees.refl _ _).bind (fun _ => .refl _ _))))
  | dimension _ _ ib ir =>
    exact ib.bind (fun _ => ir.bind (fun _ => (Agrees.refl _ _).bind (fun _ => .refl _ _)))
  | arrayExtent _ _ ih => exact ih.bind (fun _ => .refl _ _)
  | arrayOffset _ _ _ _ _ _ il ir =>
    exact il.bind (fun _ => ir.bind (fun _ => .refl _ _))
  | arrayUpdate _ _ _ _ _ _ address value =>
    exact (Agrees.refl _ _).bind (fun _ =>
      value.bind (fun _ => address.bind (fun _ => (Agrees.refl _ _).bind (fun _ => .refl _ _))))

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
  | empty | skip | arrayProbe | stop | restart => exact .pure
  | assembly _ bounds | declareArray _ _ bounds _ =>
    exact (expression bounds).bind (fun _ => (Agrees.refl _ _).bind (fun _ => .pure))
  | arrayFromAlias => exact (Agrees.refl _ _).bind (fun _ => .pure)
  | uninitialised => exact (Agrees.refl _ _).bind (fun _ => .pure)
  | initialiseArrayPointer _ _ bounds initializer =>
    apply (Agrees.refl _ _).bind
    intro place
    apply (expression bounds).bind
    intro extents
    apply (Agrees.refl _ _).bind
    intro _
    cases initializer with
    | none => exact .pure
    | some value => exact (expression value).bind (fun _ => (Agrees.refl _ _).bind (fun _ => .pure))
  | gotoLabel | indirect | label | select | caseOf => exact .invalid
  | sequence first rest firstAgrees restAgrees => exact sequence_agrees firstAgrees restAgrees
  | declarations body agrees | block body agrees => exact agrees
  | initialiseAtomic slot ty value | initialise slot ty value =>
    exact (Agrees.refl _ _).bind (fun _ => (expression value).bind (fun _ =>
      (Agrees.refl _ _).bind (fun _ => .pure)))
  | initialiseAggregate slot width stores result =>
    exact (Agrees.refl _ _).bind (fun base => (Agrees.refl _ _).bind (fun _ =>
      (init_stores_agree first second fuel calls locals base stores).bind (fun _ => .refl _ _)))
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
  | loaded expr registry targets => exact (evaluate_agrees first second fuel calls locals expr).bind (fun _ => .refl _ _)
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

private theorem parameters_agree (first second : Calls) (fuel : Nat)
    (calls : ∀ name values, Agrees fuel (first name values) (second name values))
    (locals : Locals) (shapes : List ParameterShape) :
    Agrees fuel (capture_parameters first locals shapes) (capture_parameters second locals shapes) := by
  induction shapes with
  | nil => exact .pure
  | cons shape rest ih =>
    exact (Agrees.refl _ _).bind (fun _ =>
      (evaluate_agrees first second fuel calls locals shape.bounds).bind (fun _ =>
        (Agrees.refl _ _).bind (fun _ => ih)))

private theorem frame_agrees (first second : Calls) (fuel : Nat)
    (calls : ∀ name arguments, Agrees fuel (first name arguments) (second name arguments))
    (procedure : Procedure) (globals : Globals) (values : List Value) :
    Agrees fuel (procedure.frame first globals values) (procedure.frame second globals values) := by
  exact (Agrees.refl _ _).bind (fun _ => (Agrees.refl _ _).bind (fun area =>
    (Agrees.refl _ _).bind (fun arguments =>
      (parameters_agree first second fuel calls ⟨arguments.map some, globals, area, procedure.parameters⟩ procedure.shapes).bind
        (fun _ => .refl _ _))))

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
        | none => exact .refl _ _
        | some procedure =>
          cases chosen : procedure.kernel with
          | some kernel => simpa only [chosen] using (Agrees.refl fuel
              (kernel_value procedure.parameters.length (fun slots => source_eval slots kernel.expression) values))
          | none =>
            simp only [chosen]
            have later (callee : String) (arguments : List Value) :=
              ih depth larger callee arguments (by omega) (by omega)
            apply (frame_agrees _ _ fuel later procedure globals values).bind
            intro locals
            exact (procedure_agrees _ _ fuel later
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
  let memory : HeapImage := ⟨[], ⟨1, 4096⟩, [], [], { events := invocation.files }⟩
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
  let heap : HeapImage := ⟨[], ⟨1, 4096⟩, [], [], { events := invocation.files }⟩
  let stdout : StdoutBuffer := ⟨[], [], 0, true⟩
  have source (steps : Nat) : program.observation steps terminal invocation = program.source_observation steps terminal invocation :=
    prefix_refines program terminal steps invocation heap stdout rfl id (fun _ _ same => same)
  rw [source fuel, source larger]
  rw [source fuel] at paused
  unfold Program.source_observation at paused ⊢
  let memory : HeapState := ⟨fun _ => none, ⟨1, 4096⟩, [], [], { events := invocation.files }⟩
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

def quote_bytes (bytes : List UInt8) : String :=
  let escape (b : UInt8) : String :=
    match b.toNat with
    | 34 => "\\\""
    | 92 => "\\\\"
    | 10 => "\\n"
    | 13 => "\\r"
    | 9 => "\\t"
    | n => if n < 32 || 126 < n then "\\" ++ toString n ++ "\\&" else String.singleton (Char.ofNat n)
  "\"" ++ String.join (bytes.map escape) ++ "\""

private def quoted (s : String) : String := quote_bytes s.toUTF8.toList

private def slot_name (names : List String) (slot : Nat) : String :=
  quoted (names[slot]?.getD "")

private def invoke (name result : String) (arguments : List (TypeCode × String)) : String :=
  "invoke " ++ result ++ " (function " ++ quoted name ++ ") [" ++
  String.intercalate ", " (arguments.map fun (ty, expr) => par ("marshal " ++ ty.haskell ++ " <$> " ++ par expr)) ++ "]"

private def cast_code (ty : TypeCode) (body : String) : String :=
  if ty.floating then par (body ++ " >>= convert " ++ ty.haskell)
  else par ("cast " ++ ty.haskell ++ " <$> " ++ par body)

private def initialiser_code (offsets : List Nat) (ty : TypeCode) (value : Expression) (code : String) : String :=
  let address := offsets.foldl (fun base displacement => par ("offset " ++ toString displacement ++ " " ++ base)) "p"
  match value, ty with
  | .byteLiteral b, .byte => "void (store (IntegerType 8 False) " ++ address ++ " (Number " ++ toString b.toNat ++ "))"
  | _, _ => par (code ++ " >>= store " ++ ty.haskell ++ " " ++ address ++ " >> pure ()")

def Expression.haskell (names : List String) : Expression → String
  | .truncateReal ty operand => par (operand.haskell names ++ " >>= convert " ++ ty.haskell)
  | .compound slot width writes => "(do { p <- variable " ++ slot_name names slot ++ "; clear " ++ toString width ++
      " p; " ++ writes.haskell names ++ " })"
  | .compoundStore _ offsets ty value rest =>
    initialiser_code offsets ty value (value.haskell names) ++ "; " ++ rest.haskell names
  | .compoundEnd _ => "pure p"
  | .spawn worker destination arg => invoke "pthread_create" "(Just (IntegerType 32 True))"
      [(.pointer, destination.haskell names), (.pointer, "pure nullPointer"), (.pointer, "function " ++ quoted worker),
       (.pointer, arg.haskell names)]
  | .join handle destination => invoke "pthread_join" "(Just (IntegerType 32 True))"
      [(.pointer, handle.haskell names), (.pointer, destination.haskell names)]
  | .floatingLiteral ty spelling _ =>
    let infinity := spelling == "Inf" || spelling == "INF"
    let term := if infinity then "(1 / 0)" else spelling
    match ty with
    | .binary32 => "pure (Single " ++ term ++ ")"
    | .binary64 => "pure (DoublePrecision " ++ term ++ ")"
    | _ => if infinity then "pure (Extended 0x7fff8000000000000000)" else "pure (extendedLiteral " ++ term ++ ")"
  | .byteLiteral b => "pure (Number " ++ toString b.toNat ++ ")"
  | .string bytes => "literal " ++ quote_bytes bytes
  | .library function args =>
    let result := match function with
      | .hasCapability | .isReadonly => "(IntegerType 8 False)" | .strlen | .fread | .fwrite => "(IntegerType 64 False)"
      | .calloc | .memset | .upperBound | .lowerBound | .fopen => "PointerType" | _ => "(IntegerType 32 True)"
    "invoke (Just " ++ result ++ ") (function " ++ quoted function.name ++ ") [" ++ args.haskell names ++ "]"
  | .weakDesired weak value =>
    par (par ("boolean . truth <$> " ++ par (weak.haskell names))) ++ " >> " ++ par (value.haskell names)
  | .atomicTransfer op ty target args =>
    "atomicTransfer " ++ quoted op.name ++ " " ++ ty.atomic_haskell ++ " " ++ par (target.haskell names) ++
      " [" ++ args.haskell names ++ "]"
  | .compareWord ty target successOrder expected failureOrder desired byAddress =>
    "atomicCompare " ++ (if byAddress then "True " else "False ") ++ ty.atomic_haskell ++ " " ++
      String.intercalate " " [par (target.haskell names), par (successOrder.haskell names),
        par (expected.haskell names), par (failureOrder.haskell names), par (desired.haskell names)]
  | .atomic op ty target ordering operand =>
    let place := par (target.haskell names)
    let order := par (ordering.haskell names)
    let value := par (operand.haskell names)
    let access := fun name args => "atomicAccess " ++ quoted name ++ " " ++ ty.atomic_haskell ++ " " ++ place ++
      " [" ++ String.intercalate ", " args ++ "]"
    match op with
    | .load => access "load" [order]
    | .store => access "store" [order, value]
    | .initialise => access "init" [value]
    | .fetch .exchange true => access "exchange" [order, value]
    | .pointerStep operation stride oldResult =>
      let symbol := match operation with
        | .add => "+" | .sub => "-" | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^" | .exchange => "="
      "atomicPointerStep " ++ quoted symbol ++ " " ++ toString stride ++ " " ++
        (if oldResult then "True " else "False ") ++ place ++ " " ++ order ++ " " ++ value
    | .fetch operation returnOld =>
      let symbol := match operation with
        | .exchange => "=" | .add => "+" | .sub => "-" | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
      "atomicModify " ++ quoted symbol ++ " " ++ ty.haskell ++ " 1 " ++
        (if returnOld then "True " else "False ") ++ place ++ " " ++ order ++ " " ++ value
  | .self => invoke "pthread_self" "(Just PointerType)" []
  | .equal left right => invoke "pthread_equal" "(Just (IntegerType 32 True))"
      [(.pointer, left.haskell names), (.pointer, right.haskell names)]
  | .literal n => "pure (Number " ++ par (toString n) ++ ")"
  | .sizeLiteral n => "pure (Number " ++ toString n ++ ")"
  | .nullPointer => "pure nullPointer"
  | .slotAddress slot => "variable " ++ slot_name names slot
  | .arrayAddress slot => "variable " ++ slot_name names slot
  | .globalAddress name => "variable " ++ quoted name
  | .load ty address => par (address.haskell names ++ " >>= load " ++ ty.haskell)
  | .cast ty operand => cast_code ty (operand.haskell names)
  | .materialise ty operand => "materialise " ++ ty.haskell ++ " " ++ par (operand.haskell names)
  | .offset first second stride op =>
    let parameters := match op with
      | .add | .reversedAdd => "\"+\" 64 False "
      | .subtract => "\"-\" 64 False "
      | .difference => "\"-\" 64 True "
    "binary " ++ parameters ++ toString stride ++ " " ++
      par (first.haskell names) ++ " " ++ par (second.haskell names)
  | .field base displacement => par ("offset " ++ toString displacement ++ " <$> " ++ par (base.haskell names))
  | .logicalNot operand => "unary \"!\" (IntegerType 32 True) " ++ par (operand.haskell names)
  | .unary op ty operand => "unary " ++ quoted op.symbol ++ " " ++ ty.haskell ++ " " ++ par (operand.haskell names)
  | .logic conjunction lhs rhs => "logic " ++ (if conjunction then "True " else "False ") ++
    par (lhs.haskell names) ++ " " ++ par (rhs.haskell names)
  | .shared common fallback test result =>
    let bound := fun (types : List TypeCode) => par ("\\shared -> " ++ types.foldl
      (fun expr ty => cast_code ty expr) "pure shared")
    "conditional " ++ par (common.haskell names) ++ " " ++ bound test ++ " " ++ bound result ++ " " ++
      par (fallback.haskell names)
  | .conditional condition yes no => par (condition.haskell names ++ " >>= \\v -> if truth v then " ++
    par (yes.haskell names) ++ " else " ++ par (no.haskell names))
  | .comma left right => par (left.haskell names ++ " >> " ++ par (right.haskell names))
  | .pointerCompare op lhs rhs => "binary " ++ quoted op.symbol ++
    " 64 False 1 " ++ par (lhs.haskell names) ++ " " ++ par (rhs.haskell names)
  | .allocate size => invoke "malloc" "(Just PointerType)" [(.size, size.haskell names)]
  | .move function dst src size => invoke (match function with | .memcpy => "memcpy" | .memmove => "memmove") "(Just PointerType)"
    [(.pointer, dst.haskell names), (.pointer, src.haskell names), (.size, size.haskell names)]
  | .put value => invoke "putchar" "(Just (IntegerType 32 True))" [(.integer, value.haskell names)]
  | .release address => invoke "free" "Nothing" [(.pointer, address.haskell names)]
  | .exit status => invoke "exit" "Nothing" [(.integer, status.haskell names)]
  | .assign ty address value =>
    "assign " ++ ty.haskell ++ " " ++ par (address.haskell names) ++ " " ++ par (value.haskell names)
  | .update op storage arithmetic returnOld address value stride =>
    "update " ++ quoted op.symbol ++ " " ++ storage.haskell ++ " " ++ toString (8 * arithmetic.width) ++
      (if arithmetic.signed then " True " else " False ") ++ toString stride ++ " " ++
      (if returnOld then "True " else "False ") ++
      par (address.haskell names) ++ " " ++ par (value.haskell names)

  | .scalar op ty left right =>
    "binary " ++ quoted op.symbol ++ " " ++ toString (8 * ty.width) ++ (if ty.signed then " True 1 " else " False 1 ") ++
      par (left.haskell names) ++ " " ++ par (right.haskell names)
  | .functionAddress name _ => "function " ++ quoted name
  | .indirect _ ty callee arguments =>
    let result := (ty.map (fun ty => par ("Just " ++ ty.haskell))).getD "Nothing"
    "invoke " ++ result ++ " " ++ par (callee.haskell names) ++ " [" ++ arguments.haskell names ++ "]"
  | .call name ty arguments =>
    let result := (ty.map (fun ty => par ("Just " ++ ty.haskell))).getD "Nothing"
    "invoke " ++ result ++ " (function " ++ quoted name ++ ") [" ++ arguments.haskell names ++ "]"
  | .emptyArguments => ""
  | .argument ty value rest =>
    let tail := rest.haskell names
    par ("marshal " ++ ty.haskell ++ " <$> " ++ par (value.haskell names)) ++
      (if tail.isEmpty then "" else ", " ++ tail)
  | .dimension bound rest =>
    let tail := rest.haskell names
    par (bound.haskell names) ++ (if tail.isEmpty then "" else ", " ++ tail)
  | .arrayExtent width bounds => "vlaExtent " ++ toString width ++ " [" ++ bounds.haskell names ++ "]"
  | .arrayOffset op indexing slot rank left right =>
    let operator := match op with | .add | .reversedAdd => "+" | .subtract | .difference => "-"
    let prefixCode := if indexing then "vlaIndex " else "vlaBinary " ++ quoted operator ++ " "
    prefixCode ++ toString rank ++ " " ++ par ("variable " ++ slot_name names slot) ++ " " ++
      par (left.haskell names) ++ " " ++ par (right.haskell names)
  | .arrayUpdate op slot rank returnOld address value =>
    "vlaUpdate " ++ quoted op.symbol ++ " " ++ toString rank ++ " " ++ par ("variable " ++ slot_name names slot) ++
      (if returnOld then " True " else " False ") ++ par (address.haskell names) ++ " " ++ par (value.haskell names)
  | .arraySize slot rank place =>
    par (place.haskell names ++ " >> vlaSize " ++ toString rank ++ " " ++ par ("variable " ++ slot_name names slot))
  | .aliasSize slot => "vlaSize 0 " ++ par ("variable " ++ slot_name names slot)
  | .vaStart place => "vaStart callArea namedTypes " ++ par (place.haskell names)
  | .vaCopy destination source => "vaCopy " ++ par (destination.haskell names) ++ " " ++ par (source.haskell names)
  | .vaArg ty place => "vaArg " ++ ty.haskell ++ " " ++ par (place.haskell names)
  | .vaEnd place => par (place.haskell names ++ " >> pure (Number 0)")
  | .vaAvailable place => "vaAvailable " ++ par (place.haskell names)
  | .argumentArea => "pure callArea"

private def flow (body : String) : String := "atFlow \"@\" " ++ par body

private def return_code (expr : String) : String := "Return <$> " ++ par expr

private def Initialiser.haskell (names : List String) (init : Initialiser) : String :=
  initialiser_code init.offsets init.ty init.value (init.value.haskell names)

private def register_operands (names : List String) : Expression → List String
  | .dimension expr rest => par (expr.haskell names) :: register_operands names rest
  | _ => []

private def RegisterBlock.haskell (block : RegisterBlock) (values : List String) : String := Id.run do
  let list := fun parts => "[" ++ String.intercalate ", " parts ++ "]"
  let outputs := block.outputs.zipWith (fun (ty, readWrite) place =>
    par (ty.haskell ++ ", " ++ (if readWrite then "True" else "False") ++ ", " ++ place)) values
  let inputs := block.inputs.zipWith (fun key value =>
    par (toString key ++ ", " ++ value)) (values.drop outputs.length)
  let ops := block.instructions.map fun i =>
    let operand := match i.source with
      | .inl key => "Left " ++ toString key
      | .inr n => if [.clc, .stc, .cmc].contains i.op then "Right 0" else "Right " ++ par (toString n)
    par (quoted i.op.symbol ++ ", " ++ toString i.width ++ ", " ++ toString i.destination ++ ", " ++ operand)
  if outputs.isEmpty && inputs.isEmpty && ops.isEmpty then return "asmBarrier"
  return "asmRegisters " ++ list outputs ++ " " ++ list inputs ++ " " ++ list ops

def Statement.haskell (names : List String) (stmt : Statement) (grouped : Bool := false) : String :=
  let declaration := fun item => if grouped then item else flow ("chain [" ++ item ++ "]")
  match stmt with
  | .empty => ""
  | .sequence first rest =>
    let tail := rest.haskell names grouped
    (if grouped then first.haskell names true else par (first.haskell names)) ++ (if tail.isEmpty then "" else ", " ++ tail)
  | .declarations body => flow ("chain [" ++ body.haskell names true ++ "]")
  | .block body => flow ("chain [" ++ body.haskell names ++ "]")
  | .skip => flow "pure Next"
  | .arrayProbe => declaration "(pure Next)"
  | .assembly asm operands => flow (asm.haskell (register_operands names operands))
  | .declareArray slot width bounds typeOnly =>
    declaration ((if typeOnly then "vlaAlias " else "vlaDeclare ") ++ slot_name names slot ++
      " " ++ toString width ++ " [" ++ bounds.haskell names ++ "]")
  | .arrayFromAlias slot source =>
    declaration ("vlaFromAlias " ++ slot_name names slot ++ " " ++ par ("variable " ++ slot_name names source))
  | .uninitialised slot => declaration ("(do { p <- variable " ++ slot_name names slot ++ "; pure Next })")
  | .initialiseArrayPointer slot width bounds initializer =>
    let steps := ["p <- variable " ++ slot_name names slot,
      "vlaBind 0 p " ++ toString width ++ " [" ++ bounds.haskell names ++ "]"]
    let stores := initializer.toList.map fun value =>
      par (value.haskell names ++ " >>= store PointerType p >> pure ()")
    declaration ("(do { " ++ String.intercalate "; " (steps ++ stores ++ ["pure Next"]) ++ " })")
  | .initialiseAtomic slot ty expr =>
    declaration ("(do { p <- variable " ++ slot_name names slot ++ "; void (atomicAccess \"init\" " ++
      ty.atomic_haskell ++ " (pure p) [" ++ par (expr.haskell names) ++ "]); pure Next })")
  | .initialise slot ty expr =>
    declaration ("(do { p <- variable " ++ slot_name names slot ++ "; " ++
      par (expr.haskell names ++ " >>= store " ++ ty.haskell ++ " p >> pure ()") ++ "; pure Next })")
  | .initialiseAggregate slot width stores resultType =>
    let setup := ["p <- variable " ++ slot_name names slot, "clear " ++ toString width ++ " p"]
    let actions := setup ++ stores.map (Initialiser.haskell names)
    match resultType with
    | none => declaration ("(do { " ++ String.intercalate "; " (actions ++ ["pure Next"]) ++ " })")
    | some ty =>
      let place := "(do { " ++ String.intercalate "; " (actions ++ ["pure p"]) ++ " })"
      flow (return_code (par (place ++ " >>= load " ++ ty.haskell)))
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
  | .loaded expr _ _ => expr.haskell names
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
  let entry := if procedure.introspects then par ("callArguments@" ++ pattern) else pattern
  let area := if procedure.introspects then ["callArea <- argumentArea callArguments",
    "let { namedTypes = [" ++ String.intercalate ", " (procedure.parameters.map TypeCode.haskell) ++ "] }"] else []
  let parameters := procedure.parameters.zipIdx |>.map fun (ty, slot) =>
    "parameter " ++ slot_name procedure.slots slot ++ " " ++ ty.haskell ++ " a" ++ toString slot
  let shapes := procedure.shapes.map fun shape =>
    par ("variable " ++ slot_name procedure.slots shape.slot ++ " >>= \\p -> vlaBind " ++ toString shape.skip ++
      " p " ++ toString shape.elementWidth ++ " [" ++ shape.bounds.haskell procedure.slots ++ "]")
  let locals := procedure.locals.zipIdx |>.filterMap fun (width, slot) => width.map fun size =>
    "at \"@\" (void (declare " ++ slot_name procedure.slots (count + slot) ++ " " ++ toString size ++ "))"
  let body := match procedure.dispatch with
    | none => procedure.statements.haskell procedure.slots
    | some dispatch => dispatch.haskell procedure.slots
  let mismatch := if count = 0 then "" else
    symbol ++ " _ = panic " ++ quoted ("wrong argument count for " ++ procedure.name) ++ "\n"
  let frame := "frame (do { " ++ String.intercalate "; " (area ++ parameters ++ shapes ++ locals ++ [body]) ++ " })"
  let kernelName := binding "k" procedure.name
  let equations := procedure.kernel.elim "" fun kernel =>
    kernelName ++ " :: " ++ String.intercalate " -> " (List.replicate (count + 1) "Integer") ++ "\n" ++
    kernelName ++ " " ++ String.intercalate " " ((List.range count).map (fun i => "x" ++ toString i)) ++ " = " ++
      render_target (Heresy.lower kernel.expression) ++ "\n\n"
  let implementation := if procedure.kernel.isSome then
    "pure (Number (" ++ kernelName ++ " " ++ String.intercalate " " (arguments.map fun arg => par ("number " ++ arg)) ++ "))"
    else frame
  let result := match procedure.resultType with
    | none => implementation ++ " >> pure noValue"
    | some ty => "marshal " ++ ty.haskell ++ " <$> " ++ par implementation
  equations ++ symbol ++ " :: [Value] -> R Value\n" ++ symbol ++ " " ++ entry ++ " = at \"@\" " ++
    par result ++ "\n" ++ mismatch ++ "\n"

private def UnitBody.initialiser (unit : UnitBody) (phase : String) : String :=
  if unit.namespaceName.isEmpty then phase else phase ++ "_" ++ binding "unit" unit.namespaceName

private def UnitBody.haskell (unit : UnitBody) : String :=
  let alloc (threadLocal : Bool) := (unit.objects threadLocal).map fun object =>
    "  void (global " ++ quoted object.name ++ " " ++ toString object.width ++ ")\n"
  let stores (threadLocal : Bool) := (unit.objects threadLocal).filterMap fun object =>
    let actions := object.initialisers.map (Initialiser.haskell [])
    if actions.isEmpty then none else some <|
      "  do { p <- variable " ++ quoted object.name ++ "; " ++ String.intercalate "; " actions ++ " }\n"
  let initialise (threadLocal : Bool) := stores threadLocal ++
    ((unit.objects threadLocal).filter (·.readOnly)).map (fun object => "  freeze (variable " ++ quoted object.name ++ ")\n")
  let actions := [("allocateGlobals", alloc false), ("initialiseGlobals", initialise false),
    ("allocateThread", alloc true), ("initialiseThread", initialise true)]
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
    "] [" ++ String.intercalate ", " (labels.map quoted) ++ (if program.parallel then "] True " else "] False ") ++ program.phase "Globals" ++
    " " ++ program.phase "Thread" ++ "\n"

end Heresy.Ordinary

#print axioms Heresy.Ordinary.stored_function_resolves
#print axioms Heresy.Ordinary.changed_function_rejected
#print axioms Heresy.Ordinary.resolve_function_iff
#print axioms Heresy.Ordinary.strcmp_complete
#print axioms Heresy.Ordinary.string_comparison_correct
#print axioms Heresy.Ordinary.string_read_correct
#print axioms Heresy.Ordinary.literal_reuse
#print axioms Heresy.Ordinary.calls_correct
#print axioms Heresy.Ordinary.Procedure.control_correct
#print axioms Heresy.Ordinary.packed_layout_valid
#print axioms Heresy.Ordinary.loaded_label_iff
#print axioms Heresy.Ordinary.checked_computed_jump
#print axioms Heresy.Ordinary.lower_program_correct
#print axioms Heresy.Ordinary.prefix_refines
#print axioms Heresy.Ordinary.trace_depth_stable
#print axioms Heresy.Ordinary.scalar_bitwise_bits
#print axioms Heresy.Ordinary.pointer_distance_exact
#print axioms Heresy.Ordinary.array_extent_exact
#print axioms Heresy.Ordinary.array_extent_rejects
#print axioms Heresy.Ordinary.captured_span_exact
#print axioms Heresy.Ordinary.captured_array_extent_readback
#print axioms Heresy.Ordinary.observation_output_prefix
#print axioms Heresy.Ordinary.Invocation.decode_encoding
