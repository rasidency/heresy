import Std

set_option warningAsError true

namespace Heresy

def modulus (width : Nat) : Int := 2 ^ width

def unsigned (width : Nat) (value : Int) : Int := value % modulus width

def signed (width : Nat) (value : Int) : Int :=
  let bits := unsigned width value
  if bits ≥ modulus width / 2 then bits - modulus width else bits

theorem modulus_positive (width : Nat) : 0 < modulus width := by
  exact Int.pow_pos (by decide : (0 : Int) < 2)

theorem unsigned_bounds (width : Nat) (value : Int) :
    0 ≤ unsigned width value ∧ unsigned width value < modulus width := by
  exact ⟨Int.emod_nonneg _ (Int.ne_of_gt (modulus_positive width)),
    Int.emod_lt_of_pos _ (modulus_positive width)⟩

theorem unsigned_idempotent (width : Nat) (value : Int) :
    unsigned width (unsigned width value) = unsigned width value := by
  exact Int.emod_emod _ _

theorem unsigned_preserves_bits (width : Nat) (value : Int)
    (lower : 0 ≤ value) (upper : value < modulus width) :
    unsigned width value = value := by
  exact Int.emod_eq_of_lt lower upper

theorem signed_preserves_bits (width : Nat) (value : Int) :
    unsigned width (signed width value) = unsigned width value := by
  unfold signed unsigned
  dsimp only
  split
  · simp
  · exact Int.emod_emod _ _

theorem scalar_roundtrip (width : Nat) (value : Int) :
    signed width (unsigned width value) = signed width value := by
  simp only [signed, unsigned_idempotent]

theorem signed_bounds (width : Nat) (value : Int) :
    -modulus width ≤ signed (width + 1) value ∧ signed (width + 1) value < modulus width := by
  have expansion : modulus (width + 1) = modulus width * 2 := by
    exact Int.pow_succ 2 width
  have half : modulus (width + 1) / 2 = modulus width := by
    rw [expansion]
    omega
  have bounds := unsigned_bounds (width + 1) value
  unfold signed
  dsimp only
  rw [half]
  split <;> omega

inductive Operator where
  | add | sub | mul | band | bor | bxor
  deriving DecidableEq

def operate : Operator → Int → Int → Int
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .mul, left, right => left * right
  | .band, left, right => Int.ofNat (left.toNat &&& right.toNat)
  | .bor, left, right => Int.ofNat (left.toNat ||| right.toNat)
  | .bxor, left, right => Int.ofNat (left.toNat ^^^ right.toNat)

inductive Source where
  | constant (value : Int)
  | parameter (index : Nat)
  | binary (operator : Operator) (left right : Source)

inductive Target where
  | constant (value : Int)
  | parameter (index : Nat)
  | binary (operator : Operator) (left right : Target)
  | wrap (width : Nat) (body : Target)

def source_eval (parameters : Nat → Int) : Source → Int
  | .constant value => value
  | .parameter index => parameters index
  | .binary operator left right =>
    unsigned 64 (operate operator (source_eval parameters left) (source_eval parameters right))

def target_eval (parameters : Nat → Int) : Target → Int
  | .constant value => value
  | .parameter index => parameters index
  | .binary operator left right => operate operator (target_eval parameters left) (target_eval parameters right)
  | .wrap width body => unsigned width (target_eval parameters body)

def lower : Source → Target
  | .constant value => .constant value
  | .parameter index => .parameter index
  | .binary operator left right => .wrap 64 (.binary operator (lower left) (lower right))

def admissible : Source → Prop
  | .constant value => 0 ≤ value ∧ value < modulus 64
  | .parameter _ => True
  | .binary _ left right => admissible left ∧ admissible right

theorem source_eval_bounds (expression : Source) (parameters : Nat → Int)
    (valid : admissible expression)
    (bounded : ∀ index, 0 ≤ parameters index ∧ parameters index < modulus 64) :
    0 ≤ source_eval parameters expression ∧ source_eval parameters expression < modulus 64 := by
  cases expression with
  | constant value => exact valid
  | parameter index => exact bounded index
  | binary operator left right => exact unsigned_bounds 64 _

theorem lower_correct (expression : Source) (parameters : Nat → Int) :
    target_eval parameters (lower expression) = source_eval parameters expression := by
  induction expression with
  | constant value => rfl
  | parameter index => rfl
  | binary operator left right left_correct right_correct =>
    simp only [lower, target_eval, source_eval, left_correct, right_correct]

theorem lowered_bounds (expression : Source) (parameters : Nat → Int)
    (valid : admissible expression)
    (bounded : ∀ index, 0 ≤ parameters index ∧ parameters index < modulus 64) :
    0 ≤ target_eval parameters (lower expression) ∧
      target_eval parameters (lower expression) < modulus 64 := by
  rw [lower_correct]
  exact source_eval_bounds expression parameters valid bounded

structure Object where
  base : Int
  size : Nat
  live : Bool
  readonly : Bool
  bytes : Nat → Int
  shadow : Nat → Option Nat

structure Pointer where
  capability : Nat
  address : Int

abbrev Memory := Nat → Option Object

def accessible (object : Object) (address : Int) (count : Nat) : Prop :=
  object.live = true ∧ object.base ≤ address ∧ address ≤ object.base + object.size ∧
    (count : Int) ≤ object.base + object.size - address

instance (object : Object) (address : Int) (count : Nat) :
    Decidable (accessible object address count) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def checked (memory : Memory) (pointer : Pointer) (count : Nat) : Option Object :=
  match memory pointer.capability with
  | none => none
  | some object => if accessible object pointer.address count then some object else none

theorem checked_sound (memory : Memory) (pointer : Pointer) (count : Nat) (object : Object)
    (success : checked memory pointer count = some object) :
    memory pointer.capability = some object ∧ accessible object pointer.address count := by
  unfold checked at success
  split at success
  · contradiction
  · rename_i found lookup
    split at success
    · rename_i valid
      cases success
      exact ⟨lookup, valid⟩
    · contradiction

theorem checked_span (memory : Memory) (pointer : Pointer) (count : Nat) (object : Object)
    (success : checked memory pointer count = some object) :
    object.live = true ∧ object.base ≤ pointer.address ∧
      pointer.address + count ≤ object.base + object.size := by
  have valid := (checked_sound memory pointer count object success).2
  unfold accessible at valid
  exact ⟨valid.1, valid.2.1, by omega⟩

def invalidate (memory : Memory) (capability : Nat) : Memory := fun ident =>
  if ident = capability then
    (memory ident).map fun object => { object with live := false, bytes := fun _ => 0, shadow := fun _ => none }
  else memory ident

theorem invalidation_rejects_aliases (memory : Memory) (capability : Nat)
    (pointer : Pointer) (count : Nat) (alias : pointer.capability = capability) :
    checked (invalidate memory capability) pointer count = none := by
  simp only [checked, invalidate, alias, ↓reduceIte]
  cases memory capability <;> simp [accessible]

theorem invalidation_preserves_other (memory : Memory) (capability ident : Nat)
    (different : ident ≠ capability) : invalidate memory capability ident = memory ident := by
  simp only [invalidate, different, ↓reduceIte]

def integer_store (object : Object) (offset width : Nat) (value : Int) : Object :=
  { object with bytes := fun index =>
      if offset ≤ index ∧ index < offset + width then
        (value / 2 ^ (8 * (index - offset))) % 256
      else object.bytes index }

theorem integer_store_preserves_shadow (object : Object) (offset width : Nat) (value : Int) :
    (integer_store object offset width value).shadow = object.shadow := by
  rfl

theorem integer_store_preserves_metadata (object : Object) (offset width : Nat) (value : Int) :
    let updated := integer_store object offset width value
    updated.base = object.base ∧ updated.size = object.size ∧
      updated.live = object.live ∧ updated.readonly = object.readonly := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem integer_store_preserves_other (object : Object) (offset width index : Nat) (value : Int)
    (outside : index < offset ∨ offset + width ≤ index) :
    (integer_store object offset width value).bytes index = object.bytes index := by
  simp only [integer_store]
  split
  · omega
  · rfl

def guarded_store (object : Object) (address : Int) (width : Nat) (value : Int) : Option Object :=
  if accessible object address width ∧ object.readonly = false then
    some (integer_store object (address - object.base).toNat width value)
  else none

theorem readonly_rejects_store (object : Object) (address : Int) (width : Nat) (value : Int)
    (readonly : object.readonly = true) : guarded_store object address width value = none := by
  simp [guarded_store, readonly]

theorem dead_rejects_store (object : Object) (address : Int) (width : Nat) (value : Int)
    (dead : object.live = false) : guarded_store object address width value = none := by
  simp [guarded_store, accessible, dead]

theorem guarded_store_sound (object updated : Object) (address : Int) (width : Nat) (value : Int)
    (success : guarded_store object address width value = some updated) :
    accessible object address width ∧ object.readonly = false ∧ updated.shadow = object.shadow := by
  unfold guarded_store at success
  split at success
  · rename_i valid
    cases success
    exact ⟨valid.1, valid.2, rfl⟩
  · contradiction

structure Snapshot where
  size : Nat
  bytes : Nat → Int
  shadow : Nat → Option Nat

def capture (object : Object) (start size : Nat) : Snapshot :=
  ⟨size, fun i => object.bytes (start + i), fun i => object.shadow (start + i)⟩

def restore (object : Object) (start : Nat) (value : Snapshot) : Object :=
  { object with
    bytes := fun i => if start ≤ i ∧ i < start + value.size then value.bytes (i - start) else object.bytes i
    shadow := fun i => if start ≤ i ∧ i + 8 ≤ start + value.size then value.shadow (i - start) else object.shadow i }

theorem restore_bytes (source destination : Object) (sourceOffset targetOffset size i : Nat) (inside : i < size) :
    (restore destination targetOffset (capture source sourceOffset size)).bytes (targetOffset + i) = source.bytes (sourceOffset + i) := by
  have span : targetOffset ≤ targetOffset + i ∧ targetOffset + i < targetOffset + size := by omega
  simp [restore, capture, span]

theorem restore_shadow (source destination : Object) (sourceOffset targetOffset size i : Nat) (inside : i + 8 ≤ size) :
    (restore destination targetOffset (capture source sourceOffset size)).shadow (targetOffset + i) = source.shadow (sourceOffset + i) := by
  have span : targetOffset ≤ targetOffset + i ∧ targetOffset + i + 8 ≤ targetOffset + size := by omega
  simp [restore, capture, span]

theorem restore_unaffected_byte (destination : Object) (start i : Nat) (value : Snapshot)
    (outside : i < start ∨ start + value.size ≤ i) :
    (restore destination start value).bytes i = destination.bytes i := by
  have span : ¬ (start ≤ i ∧ i < start + value.size) := by omega
  simp only [restore, span, ↓reduceIte]

theorem copied_alias_rejected (memory : Memory) (source destination : Object)
    (sourceOffset targetOffset size i capability count : Nat) (address : Int)
    (inside : i + 8 ≤ size) (stored : source.shadow (sourceOffset + i) = some capability) :
    ((restore destination targetOffset (capture source sourceOffset size)).shadow (targetOffset + i)).bind
      (fun ident => checked (invalidate memory capability) ⟨ident, address⟩ count) = none := by
  rw [restore_shadow source destination sourceOffset targetOffset size i inside, stored]
  exact invalidation_rejects_aliases memory capability ⟨capability, address⟩ count rfl

inductive Transfer (state result : Type) where
  | jump (target : Nat) (next : state)
  | stop (value : result) (final : state)

abbrev Blocks (state result : Type) := Nat → state → Option (Transfer state result)

inductive Terminates (blocks : Blocks state result) : Nat → state → result → state → Prop where
  | stop {entry initial value final} :
      blocks entry initial = some (.stop value final) →
      Terminates blocks entry initial value final
  | jump {entry initial target next value final} :
      blocks entry initial = some (.jump target next) →
      Terminates blocks target next value final →
      Terminates blocks entry initial value final

def run_blocks (blocks : Blocks state result) : Nat → Nat → state → Option (result × state)
  | 0, _, _ => none
  | fuel + 1, entry, initial =>
    match blocks entry initial with
    | none => none
    | some (.stop value final) => some (value, final)
    | some (.jump target next) => run_blocks blocks fuel target next

theorem run_blocks_correct (blocks : Blocks state result) (entry : Nat)
    (initial final : state) (value : result) :
    (∃ fuel, run_blocks blocks fuel entry initial = some (value, final)) ↔
      Terminates blocks entry initial value final := by
  constructor
  · rintro ⟨fuel, success⟩
    induction fuel generalizing entry initial with
    | zero => simp [run_blocks] at success
    | succ fuel recurse =>
      cases edge : blocks entry initial with
      | none => simp [run_blocks, edge] at success
      | some transfer =>
        cases transfer with
        | stop observed terminal =>
          simp only [run_blocks, edge, Option.some.injEq, Prod.mk.injEq] at success
          obtain ⟨rfl, rfl⟩ := success
          exact .stop edge
        | jump target next =>
          exact .jump edge (recurse target next (by simpa only [run_blocks, edge] using success))
  · intro proof
    induction proof with
    | stop edge => exact ⟨1, by simp only [run_blocks, edge]⟩
    | jump edge _ recurse =>
      obtain ⟨fuel, success⟩ := recurse
      exact ⟨fuel + 1, by simpa only [run_blocks, edge] using success⟩

def slot_size (width : Nat) : Nat := ((width + 7) / 8) * 8

def argument_size (widths : List Nat) : Nat :=
  (widths.map slot_size).sum

theorem slot_covers_payload (width : Nat) : width ≤ slot_size width := by
  unfold slot_size
  omega

theorem slot_padding (width : Nat) : slot_size width < width + 8 := by
  unfold slot_size
  omega

theorem slot_aligned (width : Nat) : slot_size width % 8 = 0 := by
  simp [slot_size]

theorem named_prefix_leaves_variadic_suffix (named extras : List Nat) :
    argument_size (named ++ extras) - argument_size named = argument_size extras := by
  simp [argument_size]

theorem next_variadic_span (named rest : List Nat) (width : Nat) :
    argument_size named + width ≤ argument_size (named ++ width :: rest) := by
  have fits := slot_covers_payload width
  simp [argument_size]
  omega

def argument_extent (widths : List Nat) : Nat :=
  ((argument_size widths + 15) / 16) * 16

theorem argument_extent_covers_slots (widths : List Nat) :
    argument_size widths ≤ argument_extent widths := by
  unfold argument_extent
  omega

theorem argument_extent_padding (widths : List Nat) :
    argument_extent widths < argument_size widths + 16 := by
  unfold argument_extent
  omega

def aligned_slot (cursor width alignment : Nat) : Nat × Nat :=
  let start := ((cursor + alignment - 1) / alignment) * alignment
  (start, start + slot_size width)

theorem aligned_slot_valid (cursor width alignment : Nat) (positive : 0 < alignment) :
    let (start, finish) := aligned_slot cursor width alignment
    cursor ≤ start ∧ start < cursor + alignment ∧ start % alignment = 0 ∧
      start + width ≤ finish := by
  have covers := slot_covers_payload width
  have split := Nat.mod_add_div (cursor + alignment - 1) alignment
  have remainder := Nat.mod_lt (cursor + alignment - 1) positive
  have aligned : (cursor + alignment - 1) / alignment * alignment % alignment = 0 := by
    simp
  simp only [aligned_slot]
  rw [Nat.mul_comm alignment] at split
  exact ⟨by omega, by omega, aligned, Nat.add_le_add_left covers _⟩

def array_extent (width : Nat) : List Nat → Nat
  | [] => width
  | count :: rest => count * array_extent width rest

def array_spans (width : Nat) : List Nat → List Nat
  | [] => [width]
  | count :: rest => (count * array_extent width rest) :: array_spans width rest

theorem array_span_at (width : Nat) (dimensions : List Nat) (rank : Nat)
    (inside : rank ≤ dimensions.length) :
    (array_spans width dimensions)[rank]? = some (array_extent width (dimensions.drop rank)) := by
  induction dimensions generalizing rank with
  | nil =>
    have zero : rank = 0 := by simpa using inside
    simp [array_spans, array_extent, zero]
  | cons count rest step =>
    cases rank with
    | zero => simp [array_spans, array_extent]
    | succ rank =>
      simpa [array_spans] using step rank (by simpa using inside)

def array_offset (width : Nat) : List Nat → List Nat → Option Nat
  | [], [] => some 0
  | count :: rest, index :: indices =>
    if index < count then
      (array_offset width rest indices).map (fun inner => index * array_extent width rest + inner)
    else none
  | _, _ => none

theorem array_index_in_bounds (width : Nat) (dimensions indices : List Nat) (offset : Nat)
    (resolved : array_offset width dimensions indices = some offset) :
    offset + width ≤ array_extent width dimensions := by
  induction dimensions generalizing indices offset with
  | nil =>
    cases indices with
    | nil =>
      simp [array_offset] at resolved
      subst offset
      simp [array_extent]
    | cons index rest => simp [array_offset] at resolved
  | cons count rest step =>
    cases indices with
    | nil => simp [array_offset] at resolved
    | cons index indices =>
      by_cases inside : index < count
      · cases inner : array_offset width rest indices with
        | none => simp [array_offset, inside, inner] at resolved
        | some inner_offset =>
          simp only [array_offset, if_pos inside, inner, Option.map_some, Option.some.injEq] at resolved
          subst offset
          let stride := array_extent width rest
          have fits : inner_offset + width ≤ stride := step indices inner_offset inner
          calc
            index * stride + inner_offset + width ≤ index * stride + stride := by omega
            _ = (index + 1) * stride := by simp [Nat.add_mul]
            _ ≤ count * stride := Nat.mul_le_mul_right stride inside
            _ = array_extent width (count :: rest) := rfl
      · simp [array_offset, inside] at resolved

def field_store (position width previous value : Nat) : Nat :=
  let low_mask := 2 ^ width - 1
  let mask := low_mask <<< position
  (previous ^^^ (previous &&& mask)) ||| ((value &&& low_mask) <<< position)

theorem field_store_bit (position width previous value index : Nat) :
    (field_store position width previous value).testBit index =
      if position ≤ index ∧ index - position < width then value.testBit (index - position)
      else previous.testBit index := by
  simp only [field_store, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  by_cases after_start : position ≤ index <;> by_cases before_end : index - position < width <;>
    cases previous.testBit index <;> cases value.testBit (index - position) <;>
    simp [after_start, before_end]

def promoted_atomic_compare (width : Nat) (observed expected : Int) : Bool :=
  observed == unsigned width expected

theorem promoted_atomic_rejects_nonzero_padding (width : Nat) (observed expected : Int)
    (has_padding : modulus width ≤ observed) :
    promoted_atomic_compare width observed expected = false := by
  have expected_bound := (unsigned_bounds width expected).2
  simp only [promoted_atomic_compare, beq_eq_false_iff_ne]
  omega

theorem promoted_atomic_compares_payload (width : Nat) (observed expected : Int)
    (nonnegative : 0 ≤ observed) (unpadded : observed < modulus width) :
    promoted_atomic_compare width observed expected = true ↔
      unsigned width observed = unsigned width expected := by
  rw [unsigned_preserves_bits width observed nonnegative unpadded]
  simp [promoted_atomic_compare]

structure PointerWord where
  address : Int
  capability : Option Nat
  deriving DecidableEq

inductive ShadowWord where
  | ordinary (capability : Option Nat)
  | atomic (value : PointerWord)
  deriving DecidableEq

structure AtomicWord where
  payload : Int
  shadow : ShadowWord
  deriving DecidableEq

def ordinary_pointer_read (word : AtomicWord) : PointerWord :=
  let capability := match word.shadow with
    | .ordinary capability => capability
    | .atomic value => value.capability
  ⟨word.payload, capability⟩

def atomic_pointer_read (word : AtomicWord) : PointerWord :=
  match word.shadow with
  | .ordinary capability => ⟨word.payload, capability⟩
  | .atomic value => value

def atomic_pointer_write (value : PointerWord) : AtomicWord :=
  ⟨value.address, .atomic value⟩

def atomic_payload_write (word : AtomicWord) (payload : Int) : AtomicWord :=
  { word with payload }

def atomic_pointer_compare (word : AtomicWord) (expected desired : PointerWord) :
    Bool × PointerWord × AtomicWord :=
  let observed := atomic_pointer_read word
  if observed.address = expected.address then (true, observed, atomic_pointer_write desired)
  else (false, observed, word)

theorem atomic_pointer_snapshot (value : PointerWord) (payload : Int) :
    atomic_pointer_read (atomic_payload_write (atomic_pointer_write value) payload) = value ∧
      ordinary_pointer_read (atomic_payload_write (atomic_pointer_write value) payload) =
        ⟨payload, value.capability⟩ := by
  exact ⟨rfl, rfl⟩

theorem atomic_pointer_compare_accepts (word : AtomicWord) (expected desired : PointerWord)
    (address : (atomic_pointer_read word).address = expected.address) :
    atomic_pointer_compare word expected desired =
      (true, atomic_pointer_read word, atomic_pointer_write desired) := by
  simp [atomic_pointer_compare, address]

theorem atomic_pointer_compare_rejects (word : AtomicWord) (expected desired : PointerWord)
    (address : (atomic_pointer_read word).address ≠ expected.address) :
    atomic_pointer_compare word expected desired =
      (false, atomic_pointer_read word, word) := by
  simp [atomic_pointer_compare, address]

structure DispatchGraph where
  entry : Nat
  successors : List (List Nat)

def valid_dispatch (graph : DispatchGraph) : Bool :=
  decide (graph.entry < graph.successors.length) &&
    graph.successors.all (fun row => row.all (fun target => decide (target < graph.successors.length)))

inductive Reaches (graph : DispatchGraph) : Nat → Prop where
  | entry : Reaches graph graph.entry
  | jump {block target : Nat} {row : List Nat} :
      Reaches graph block → graph.successors[block]? = some row → target ∈ row → Reaches graph target

theorem dispatch_targets_exist (graph : DispatchGraph) (accepted : valid_dispatch graph = true)
    (target : Nat) (reachable : Reaches graph target) :
    target < graph.successors.length := by
  simp [valid_dispatch, List.all_eq_true] at accepted
  cases reachable with
  | entry => exact accepted.1
  | jump _ row_at member =>
    exact accepted.2 _ (List.mem_of_getElem? row_at) _ member

def intmap_shadow_copy (source destination : Int → Option α)
    (source_offset destination_offset count slot : Int) : Option α :=
  if count = 0 then destination slot
  else
    let copied :=
      if (destination_offset ≤ slot ∧ slot < destination_offset + max 0 (count - 7)) ∧
          source_offset % 8 = destination_offset % 8 then
        source (source_offset + (slot - destination_offset))
      else none
    copied.or (if slot ≤ destination_offset - 8 ∨ destination_offset + count ≤ slot then
      destination slot else none)

def capability_shadow_copy (source destination : Int → Option α)
    (source_offset destination_offset count slot : Int) : Option α :=
  if count = 0 ∨ slot + 8 ≤ destination_offset ∨ destination_offset + count ≤ slot then
    destination slot
  else if (destination_offset ≤ slot ∧ slot + 8 ≤ destination_offset + count) ∧
      source_offset % 8 = destination_offset % 8 then
    source (source_offset + (slot - destination_offset))
  else none

theorem shadow_copy_refines (source destination : Int → Option α)
    (source_offset destination_offset count slot : Int) (nonnegative : 0 ≤ count) :
    intmap_shadow_copy source destination source_offset destination_offset count slot =
      capability_shadow_copy source destination source_offset destination_offset count slot := by
  by_cases empty : count = 0
  · simp [intmap_shadow_copy, capability_shadow_copy, empty]
  have outside : (slot ≤ destination_offset - 8 ∨ destination_offset + count ≤ slot) ↔
      (slot + 8 ≤ destination_offset ∨ destination_offset + count ≤ slot) := by omega
  have contained : (destination_offset ≤ slot ∧ slot < destination_offset + max 0 (count - 7)) ↔
      (destination_offset ≤ slot ∧ slot + 8 ≤ destination_offset + count) := by omega
  simp only [intmap_shadow_copy, capability_shadow_copy, empty, false_or, ↓reduceIte, outside, contained]
  by_cases copied : (destination_offset ≤ slot ∧ slot + 8 ≤ destination_offset + count) ∧
      source_offset % 8 = destination_offset % 8
  · have span := copied.1
    have intersects : ¬ (slot + 8 ≤ destination_offset ∨ destination_offset + count ≤ slot) := by
      omega
    simp [copied, intersects]
  · simp [copied]

end Heresy

#print axioms Heresy.lower_correct
#print axioms Heresy.checked_span
#print axioms Heresy.invalidation_rejects_aliases
#print axioms Heresy.integer_store_preserves_shadow
#print axioms Heresy.readonly_rejects_store
#print axioms Heresy.signed_bounds
#print axioms Heresy.lowered_bounds
#print axioms Heresy.guarded_store_sound
#print axioms Heresy.restore_bytes
#print axioms Heresy.copied_alias_rejected
#print axioms Heresy.run_blocks_correct
#print axioms Heresy.named_prefix_leaves_variadic_suffix
#print axioms Heresy.next_variadic_span
#print axioms Heresy.argument_extent_covers_slots
#print axioms Heresy.aligned_slot_valid
#print axioms Heresy.array_span_at
#print axioms Heresy.array_index_in_bounds
#print axioms Heresy.field_store_bit
#print axioms Heresy.promoted_atomic_rejects_nonzero_padding
#print axioms Heresy.atomic_pointer_snapshot
#print axioms Heresy.atomic_pointer_compare_rejects
#print axioms Heresy.dispatch_targets_exist
#print axioms Heresy.shadow_copy_refines
