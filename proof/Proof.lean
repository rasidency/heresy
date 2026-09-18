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
  | conditional (condition yes no : Source)

inductive Target where
  | constant (value : Int)
  | parameter (index : Nat)
  | binary (operator : Operator) (left right : Target)
  | wrap (width : Nat) (body : Target)
  | conditional (condition yes no : Target)

def source_eval (parameters : Nat → Int) : Source → Int
  | .constant value => value
  | .parameter index => parameters index
  | .binary operator left right =>
    unsigned 64 (operate operator (source_eval parameters left) (source_eval parameters right))
  | .conditional condition yes no =>
    if source_eval parameters condition = 0 then source_eval parameters no else source_eval parameters yes

def target_eval (parameters : Nat → Int) : Target → Int
  | .constant value => value
  | .parameter index => parameters index
  | .binary operator left right => operate operator (target_eval parameters left) (target_eval parameters right)
  | .wrap width body => unsigned width (target_eval parameters body)
  | .conditional condition yes no =>
    if target_eval parameters condition = 0 then target_eval parameters no else target_eval parameters yes

def lower : Source → Target
  | .constant value => .constant value
  | .parameter index => .parameter index
  | .binary operator left right => .wrap 64 (.binary operator (lower left) (lower right))
  | .conditional condition yes no => .conditional (lower condition) (lower yes) (lower no)

def admissible : Source → Prop
  | .constant value => 0 ≤ value ∧ value < modulus 64
  | .parameter _ => True
  | .binary _ left right => admissible left ∧ admissible right
  | .conditional condition yes no => admissible condition ∧ admissible yes ∧ admissible no

theorem source_eval_bounds (expression : Source) (parameters : Nat → Int)
    (valid : admissible expression)
    (bounded : ∀ index, 0 ≤ parameters index ∧ parameters index < modulus 64) :
    0 ≤ source_eval parameters expression ∧ source_eval parameters expression < modulus 64 := by
  induction expression with
  | constant value => exact valid
  | parameter index => exact bounded index
  | binary _ _ _ _ _ => exact unsigned_bounds 64 _
  | conditional _ _ _ _ yes_bounded no_bounded =>
    simp only [source_eval]
    split
    · exact no_bounded valid.2.2
    · exact yes_bounded valid.2.1

theorem lower_correct (expression : Source) (parameters : Nat → Int) :
    target_eval parameters (lower expression) = source_eval parameters expression := by
  induction expression with
  | constant value => rfl
  | parameter index => rfl
  | binary operator left right left_correct right_correct =>
    simp only [lower, target_eval, source_eval, left_correct, right_correct]
  | conditional condition yes no condition_correct yes_correct no_correct =>
    simp only [lower, target_eval, source_eval, condition_correct, yes_correct, no_correct]

theorem lowered_bounds (expression : Source) (parameters : Nat → Int)
    (valid : admissible expression)
    (bounded : ∀ index, 0 ≤ parameters index ∧ parameters index < modulus 64) :
    0 ≤ target_eval parameters (lower expression) ∧
      target_eval parameters (lower expression) < modulus 64 := by
  rw [lower_correct]
  exact source_eval_bounds expression parameters valid bounded

def source_status (body : Source) : Int := unsigned 8 (signed 32 (source_eval (fun _ => 0) body))

def target_status (body : Target) : Int := unsigned 8 (target_eval (fun _ => 0) body)

private theorem exit_status_truncation (value : Int) : unsigned 8 (signed 32 value) = unsigned 8 value := by
  have divides : modulus 8 ∣ modulus 32 := ⟨16777216, by decide⟩
  have wrap : unsigned 8 (unsigned 32 value) = unsigned 8 value := Int.emod_emod_of_dvd value divides
  unfold signed
  dsimp only
  split
  · change (unsigned 32 value - modulus 32) % modulus 8 = value % modulus 8
    rw [Int.sub_emod, Int.emod_eq_zero_of_dvd divides, Int.sub_zero, Int.emod_emod]
    exact wrap
  · exact wrap

theorem lower_program_correct (body : Source) : target_status (lower body) = source_status body := by
  simp only [target_status, lower_correct, source_status, exit_status_truncation]

abbrev Locals := Nat → Int

inductive Command (expr : Type) where
  | skip
  | store (slot : Nat) (value : expr)
  | sequence (first second : Command expr)
  | select (guard : expr) (yes no : Command expr)
  | result (value : expr)

def Command.map (transform : α → β) : Command α → Command β
  | .skip => .skip
  | .store slot value => .store slot (transform value)
  | .sequence first second => .sequence (first.map transform) (second.map transform)
  | .select guard yes no => .select (transform guard) (yes.map transform) (no.map transform)
  | .result value => .result (transform value)

inductive CommandOutcome where
  | next (locals : Locals)
  | returned (value : Int)

def write_local (locals : Locals) (slot : Nat) (value : Int) : Locals :=
  fun index => if index = slot then value else locals index

inductive Executes : Command (Locals → Int) → Locals → CommandOutcome → Prop where
  | skip : Executes .skip locals (.next locals)
  | store : Executes (.store slot expression) locals (.next (write_local locals slot (expression locals)))
  | result : Executes (.result expression) locals (.returned (expression locals))
  | sequence_next : Executes first locals (.next updated) → Executes second updated outcome →
      Executes (.sequence first second) locals outcome
  | sequence_returned : Executes first locals (.returned value) →
      Executes (.sequence first second) locals (.returned value)
  | select_yes {condition : Locals → Int} : condition locals ≠ 0 → Executes yes locals outcome →
      Executes (.select condition yes no) locals outcome
  | select_no {condition : Locals → Int} : condition locals = 0 → Executes no locals outcome →
      Executes (.select condition yes no) locals outcome

def source_commands (body : Command Source) : Command (Locals → Int) := body.map (fun expr locals => source_eval locals expr)

def target_commands (body : Command Target) : Command (Locals → Int) := body.map (fun expr locals => target_eval locals expr)

theorem lower_commands_preserves_operations (body : Command Source) :
    target_commands (body.map lower) = source_commands body := by
  have expression (expr : Source) : (fun locals => target_eval locals (lower expr)) = (fun locals => source_eval locals expr) :=
    funext (lower_correct expr)
  induction body <;> simp only [source_commands, target_commands, Command.map, expression] at * <;> simp_all

def CommandOutcome.value : CommandOutcome → Int
  | .next _ => 0
  | .returned value => value

def source_observes (body : Command Source) (status : Int) : Prop :=
  ∃ outcome, Executes (source_commands body) (fun _ => 0) outcome ∧ status = unsigned 8 (signed 32 outcome.value)

def target_observes (body : Command Target) (status : Int) : Prop :=
  ∃ outcome, Executes (target_commands body) (fun _ => 0) outcome ∧ status = unsigned 8 outcome.value

theorem lower_commands_correct (body : Command Source) (status : Int) :
    target_observes (body.map lower) status ↔ source_observes body status := by
  simp only [target_observes, source_observes, lower_commands_preserves_operations, exit_status_truncation]

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

inductive AccessFault where
  | notPointer | noCapability | dead | bounds
  deriving DecidableEq

def runtime_checked (memory : Memory) (address : Option Pointer) (count : Int) :
    Except AccessFault (Object × Nat) :=
  match address with
  | none => .error .notPointer
  | some pointer =>
    match memory pointer.capability with
    | none => .error .noCapability
    | some object =>
      if object.live = false then .error .dead
      else
        let offset := pointer.address - object.base
        if count < 0 ∨ offset < 0 ∨ (object.size : Int) < offset ∨
            (object.size : Int) - offset < count then .error .bounds
        else .ok (object, offset.toNat)

theorem checked_refines (memory : Memory) (pointer : Pointer) (count offset : Nat) (object : Object) :
    runtime_checked memory (some pointer) (count : Int) = .ok (object, offset) ↔
      checked memory pointer count = some object ∧ offset = (pointer.address - object.base).toNat := by
  cases found : memory pointer.capability with
  | none => simp [runtime_checked, checked, found]
  | some entry =>
    have accept : ¬ ((count : Int) < 0 ∨ pointer.address - entry.base < 0 ∨
        (entry.size : Int) < pointer.address - entry.base ∨
        (entry.size : Int) - (pointer.address - entry.base) < (count : Int)) ↔
        entry.base ≤ pointer.address ∧ pointer.address ≤ entry.base + entry.size ∧
          (count : Int) ≤ entry.base + entry.size - pointer.address := by omega
    cases liveness : entry.live with
    | false => simp [runtime_checked, checked, accessible, found, liveness]
    | true =>
      by_cases valid : entry.base ≤ pointer.address ∧ pointer.address ≤ entry.base + entry.size ∧
          (count : Int) ≤ entry.base + entry.size - pointer.address
      · simp [runtime_checked, checked, accessible, found, liveness, accept.mpr valid, valid, eq_comm]
        rintro rfl
        rfl
      · have rejected : (count : Int) < 0 ∨ pointer.address - entry.base < 0 ∨
            (entry.size : Int) < pointer.address - entry.base ∨
            (entry.size : Int) - (pointer.address - entry.base) < (count : Int) := by
          exact Classical.not_not.mp (fun admissible => valid (accept.mp admissible))
        simp [runtime_checked, checked, accessible, found, liveness, rejected, valid]

theorem checked_offset_fits (memory : Memory) (pointer : Pointer) (count offset host_max : Nat)
    (object : Object) (extent_fits : object.size ≤ host_max)
    (success : runtime_checked memory (some pointer) (count : Int) = .ok (object, offset)) :
    (offset : Int) = pointer.address - object.base ∧ offset + count ≤ host_max := by
  obtain ⟨checked_access, displacement⟩ := (checked_refines memory pointer count offset object).mp success
  obtain ⟨_, lower, upper⟩ := checked_span memory pointer count object checked_access
  rw [displacement, Int.toNat_of_nonneg (by omega)]
  omega

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

inductive ReleaseAddress where
  | null | data (pointer : Pointer) | other

inductive ReleaseFault where
  | access (fault : AccessFault) | notHeapBase | notPointer
  deriving DecidableEq

def runtime_release (memory : Memory) (heap : Nat → Bool) (address : ReleaseAddress) :
    Except ReleaseFault Memory :=
  match address with
  | .null => .ok memory
  | .other => .error .notPointer
  | .data pointer =>
    match runtime_checked memory (some pointer) 0 with
    | .error fault => .error (.access fault)
    | .ok (_, offset) =>
      if heap pointer.capability = true ∧ offset = 0 then .ok (invalidate memory pointer.capability)
      else .error .notHeapBase

theorem release_data_sound (memory next : Memory) (heap : Nat → Bool) (pointer : Pointer)
    (success : runtime_release memory heap (.data pointer) = .ok next) :
    ∃ object, checked memory pointer 0 = some object ∧ heap pointer.capability = true ∧
      pointer.address = object.base ∧ next = invalidate memory pointer.capability := by
  cases access : runtime_checked memory (some pointer) 0 with
  | error fault => simp [runtime_release, access] at success
  | ok entry =>
    obtain ⟨object, offset⟩ := entry
    by_cases owner : heap pointer.capability = true ∧ offset = 0
    · simp only [runtime_release, access, if_pos owner, Except.ok.injEq] at success
      obtain ⟨valid, displacement⟩ := (checked_refines memory pointer 0 offset object).mp access
      have lower := (checked_span memory pointer 0 object valid).2.1
      have zero := owner.2
      have base : pointer.address = object.base := by omega
      exact ⟨object, valid, owner.1, base, success.symm⟩
    · simp [runtime_release, access, owner] at success

theorem release_data_complete (memory : Memory) (heap : Nat → Bool) (pointer : Pointer) (object : Object)
    (valid : checked memory pointer 0 = some object) (owner : heap pointer.capability = true)
    (base : pointer.address = object.base) :
    runtime_release memory heap (.data pointer) = .ok (invalidate memory pointer.capability) := by
  have access : runtime_checked memory (some pointer) 0 = .ok (object, 0) :=
    (checked_refines memory pointer 0 0 object).mpr ⟨valid, by simp [base]⟩
  simp [runtime_release, access, owner]

theorem release_alias_fault (memory next : Memory) (heap : Nat → Bool) (pointer alias : Pointer)
    (count : Int) (same_capability : alias.capability = pointer.capability)
    (success : runtime_release memory heap (.data pointer) = .ok next) :
    runtime_checked next (some alias) count = .error .dead := by
  obtain ⟨object, accessed, _, _, rfl⟩ := release_data_sound memory next heap pointer success
  have found := (checked_sound memory pointer 0 object accessed).1
  simp [runtime_checked, invalidate, same_capability, found]

theorem release_preserves_other (memory next : Memory) (heap : Nat → Bool) (pointer : Pointer)
    (ident : Nat) (different : ident ≠ pointer.capability)
    (success : runtime_release memory heap (.data pointer) = .ok next) : next ident = memory ident := by
  obtain ⟨_, _, _, _, rfl⟩ := release_data_sound memory next heap pointer success
  exact invalidation_preserves_other memory pointer.capability ident different

def little_endian_byte (value : Int) (index : Nat) : Int := value / (256 ^ index) % 256

def little_endian_read (width : Nat) (payload : Nat → Int) : Int :=
  ((List.range width).map fun index => payload index * 256 ^ index).sum

private theorem little_endian_read_succ (width : Nat) (payload : Nat → Int) :
    little_endian_read (width + 1) payload =
      payload 0 + little_endian_read width (fun index => payload (index + 1)) * 256 := by
  have weight (indices : List Nat) :
      (indices.map fun index => payload (index + 1) * (256 : Int) ^ (index + 1)).sum =
        (indices.map fun index => payload (index + 1) * (256 : Int) ^ index).sum * 256 := by
    induction indices with
    | nil => simp
    | cons _ _ rest =>
      simp only [List.map_cons, List.sum_cons]
      rw [rest, Int.pow_succ, ← Int.mul_assoc, Int.add_mul]
  simp [little_endian_read, List.range_succ_eq_map, List.map_map, Function.comp_def, weight]

private theorem byte_radix (value place : Int) (positive : 0 < place) :
    value % 256 + ((value / 256) % place) * 256 = value % (place * 256) := by
  have byte_lo := Int.emod_nonneg value (by decide : (256 : Int) ≠ 0)
  have byte_hi := Int.emod_lt_of_pos value (by decide : (0 : Int) < 256)
  have upper_lo := Int.emod_nonneg (value / 256) (Int.ne_of_gt positive)
  have upper_hi := Int.emod_lt_of_pos (value / 256) positive
  have division : value % 256 + ((value / 256) % place) * 256 +
      (place * 256) * ((value / 256) / place) = value := by
    calc
      _ = value % 256 + 256 * ((value / 256) % place + place * ((value / 256) / place)) := by
        rw [Int.mul_add, ← Int.mul_assoc, ← Int.add_assoc, Int.mul_comm 256 place,
          Int.mul_comm 256 ((value / 256) % place)]
      _ = value := by rw [Int.emod_add_mul_ediv, Int.emod_add_mul_ediv]
  exact ((Int.ediv_emod_unique (b := place * 256) (by omega)).mpr ⟨division, by omega, by omega⟩).2.symm

theorem little_endian_roundtrip (value : Int) (width : Nat) :
    little_endian_read width (little_endian_byte value) = value % (256 : Int) ^ width := by
  induction width generalizing value with
  | zero => simp [little_endian_read]
  | succ width rest =>
    have suffix : (fun index => little_endian_byte value (index + 1)) = little_endian_byte (value / 256) := by
      funext index
      simp only [little_endian_byte, Int.pow_succ]
      rw [Int.ediv_ediv (by decide : (0 : Int) ≤ 256), Int.mul_comm 256]
    rw [little_endian_read_succ, suffix, rest, Int.pow_succ]
    simpa [little_endian_byte] using byte_radix value (256 ^ width) (Int.pow_pos (by decide))

private theorem byte_modulus (width : Nat) : (256 : Int) ^ width = modulus (8 * width) := by
  induction width with
  | zero => rfl
  | succ width rest =>
    rw [Int.pow_succ, rest, Nat.mul_succ]
    simp [modulus, Int.pow_add]

def integer_store (object : Object) (offset width : Nat) (value : Int) : Object :=
  { object with bytes := fun index =>
      if offset ≤ index ∧ index < offset + width then
        little_endian_byte value (index - offset)
      else object.bytes index }

theorem integer_store_load_roundtrip (object : Object) (offset width : Nat) (value : Int) :
    little_endian_read width (fun index => (integer_store object offset width value).bytes (offset + index)) =
      unsigned (8 * width) value := by
  rw [unsigned, ← byte_modulus, ← little_endian_roundtrip]
  unfold little_endian_read
  congr 1
  apply List.map_congr_left
  intro index member
  have within := List.mem_range.mp member
  have stored : offset ≤ offset + index ∧ offset + index < offset + width := by omega
  simp [integer_store, stored]

def write_scalar_indices (offset : Nat) (value : Int) (indices : List Nat) (payload : Nat → Int) : Nat → Int :=
  indices.foldl (fun bytes digit index => if index = offset + digit then little_endian_byte value digit else bytes index) payload

private theorem write_scalar_indices_at (offset : Nat) (value : Int) (indices : List Nat)
    (payload : Nat → Int) (index : Nat) :
    write_scalar_indices offset value indices payload index =
      if index ∈ indices.map (offset + ·) then little_endian_byte value (index - offset) else payload index := by
  induction indices generalizing payload with
  | nil => simp [write_scalar_indices]
  | cons digit rest tail =>
    simp only [write_scalar_indices, List.foldl_cons] at tail ⊢
    rw [tail]
    by_cases written : index ∈ rest.map (offset + ·)
    · simp [written]
    · by_cases first : index = offset + digit
      · subst index
        simp [written]
      · simp [written, first]

theorem scalar_write_refines (object : Object) (offset width : Nat) (value : Int) (index : Nat) :
    write_scalar_indices offset value (List.range width) object.bytes index =
      (integer_store object offset width value).bytes index := by
  have keys : (index ∈ (List.range width).map (offset + ·)) ↔ offset ≤ index ∧ index < offset + width := by
    constructor
    · intro present
      obtain ⟨digit, inside, rfl⟩ := List.mem_map.mp present
      have valid := List.mem_range.mp inside
      omega
    · intro inside
      exact List.mem_map.mpr ⟨index - offset, List.mem_range.mpr (by omega), by omega⟩
  simp only [write_scalar_indices_at, keys, integer_store]

theorem signed_store_load_roundtrip (object : Object) (offset width : Nat) (value : Int) :
    signed (8 * width)
      (little_endian_read width (fun index => (integer_store object offset width value).bytes (offset + index))) =
      signed (8 * width) value := by
  rw [integer_store_load_roundtrip]
  simp only [signed, unsigned_idempotent]

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

def runtime_freeze (memory : Memory) (address : Option Pointer) : Except AccessFault Memory :=
  match address with
  | none => .error .notPointer
  | some pointer =>
    match memory pointer.capability with
    | none => .error .noCapability
    | some object => .ok (fun ident => if ident = pointer.capability then
        some { object with readonly := true } else memory ident)

theorem freeze_alias_reads (memory next : Memory) (owner alias : Pointer) (count : Nat) (object : Object)
    (frozen : runtime_freeze memory (some owner) = .ok next)
    (same_capability : alias.capability = owner.capability)
    (access : checked memory alias count = some object) :
    checked next alias count = some { object with readonly := true } := by
  obtain ⟨lookup, valid⟩ := checked_sound memory alias count object access
  have owned : memory owner.capability = some object := same_capability ▸ lookup
  simp only [runtime_freeze, owned, Except.ok.injEq] at frozen
  rw [← frozen]
  simp only [checked, same_capability, ↓reduceIte]
  exact if_pos valid

theorem freeze_alias_rejects_store (memory next : Memory) (owner alias : Pointer) (count : Nat)
    (object : Object) (value : Int)
    (frozen : runtime_freeze memory (some owner) = .ok next)
    (same_capability : alias.capability = owner.capability)
    (access : checked memory alias count = some object) :
    ∃ updated, checked next alias count = some updated ∧ updated.bytes = object.bytes ∧
      guarded_store updated alias.address count value = none := by
  refine ⟨{ object with readonly := true }, freeze_alias_reads memory next owner alias count object frozen same_capability access,
    rfl, ?_⟩
  exact readonly_rejects_store _ _ _ _ rfl

theorem freeze_preserves_other (memory next : Memory) (owner : Pointer) (ident : Nat)
    (frozen : runtime_freeze memory (some owner) = .ok next) (different : ident ≠ owner.capability) :
    next ident = memory ident := by
  cases found : memory owner.capability with
  | none => simp [runtime_freeze, found] at frozen
  | some object =>
    simp only [runtime_freeze, found, Except.ok.injEq] at frozen
    rw [← frozen]
    exact if_neg different

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

structure AllocationCounter where
  ident : Nat
  cursor : Nat

structure AllocationPlan where
  ident : Nat
  address : Nat
  extent : Nat
  next : AllocationCounter

def allocation_alignment (global : Bool) : Nat := if global then 8 else 16

def allocation_candidate (counter : AllocationCounter) (global : Bool) (size : Nat) : AllocationPlan :=
  let address := (aligned_slot counter.cursor 0 16).1
  let extent := (aligned_slot size 0 (allocation_alignment global)).1
  ⟨counter.ident, address, extent, ⟨counter.ident + 1, address + max extent 1 + 16⟩⟩

def plan_allocation (counter : AllocationCounter) (global : Bool) (size : Int) (host_max : Nat) :
    Option AllocationPlan :=
  if size < 0 ∨ host_max < size.toNat + (allocation_alignment global - 1) then none
  else
    let candidate := allocation_candidate counter global size.toNat
    if counter.ident = host_max ∨ 4611686018427387904 ≤ candidate.address + candidate.extent then none
    else some candidate

theorem allocation_plan_sound (counter : AllocationCounter) (global : Bool) (size : Int) (host_max : Nat)
    (plan : AllocationPlan) (counter_fits : counter.ident ≤ host_max)
    (success : plan_allocation counter global size host_max = some plan) :
    let alignment := allocation_alignment global
    0 ≤ size ∧ size.toNat + (alignment - 1) ≤ host_max ∧
      size.toNat ≤ plan.extent ∧ plan.extent ≤ host_max ∧ plan.extent % alignment = 0 ∧
      counter.cursor ≤ plan.address ∧ plan.address % 16 = 0 ∧
      plan.address + plan.extent < 4611686018427387904 ∧
      plan.ident = counter.ident ∧ plan.ident < plan.next.ident ∧ plan.next.ident ≤ host_max ∧
      plan.address + plan.extent < plan.next.cursor := by
  unfold plan_allocation at success
  split at success
  · contradiction
  · rename_i admissible
    dsimp only at success
    split at success
    · contradiction
    · rename_i available
      cases success
      have align_positive : 0 < allocation_alignment global := by cases global <;> decide
      have extent_valid := aligned_slot_valid size.toNat 0 _ align_positive
      have padding : (aligned_slot size.toNat 0 (allocation_alignment global)).1 <
          size.toNat + allocation_alignment global := extent_valid.2.1
      obtain ⟨start, _, address_aligned, _⟩ := aligned_slot_valid counter.cursor 0 16 (by decide)
      simp only [allocation_candidate] at available ⊢
      have below_ceiling := Nat.lt_of_not_ge (fun exceeds => available (Or.inr exceeds))
      have fresh := Nat.lt_of_le_of_ne counter_fits (fun exhausted => available (Or.inl exhausted))
      refine ⟨by omega, by omega, extent_valid.1, ?_, extent_valid.2.2.1, start, address_aligned,
        below_ceiling, True.intro, by omega, fresh, ?_⟩
      · omega
      · omega

theorem allocation_plans_disjoint (counter : AllocationCounter) (first_global second_global : Bool)
    (first_size second_size : Int) (host_max : Nat) (first second : AllocationPlan)
    (counter_fits : counter.ident ≤ host_max)
    (allocated_first : plan_allocation counter first_global first_size host_max = some first)
    (allocated_second : plan_allocation first.next second_global second_size host_max = some second) :
    first.ident < second.ident ∧ first.address + first.extent < second.address := by
  obtain ⟨_, _, _, _, _, _, _, _, _, distinct, next_fits, separated⟩ :=
    allocation_plan_sound counter first_global first_size host_max first counter_fits allocated_first
  obtain ⟨_, _, _, _, _, beyond, _, _, new_ident, _, _, _⟩ :=
    allocation_plan_sound first.next second_global second_size host_max second next_fits allocated_second
  exact ⟨new_ident ▸ distinct, Nat.lt_of_lt_of_le separated beyond⟩

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

def guarded_blocks (graph : DispatchGraph) (actions : List (state → Option (Transfer state result))) :
    Blocks state result := fun index initial =>
  if graph.successors.length = actions.length then do
    let (row, action) ← (graph.successors.zip actions)[index]?
    let transfer ← action initial
    match transfer with
    | .jump next _ => if next ∈ row then some transfer else none
    | .stop _ _ => some transfer
  else none

theorem guarded_jump_listed (graph : DispatchGraph) (actions : List (state → Option (Transfer state result)))
    (index next : Nat) (initial after : state)
    (jumped : guarded_blocks graph actions index initial = some (.jump next after)) :
    ∃ row, graph.successors[index]? = some row ∧ next ∈ row := by
  by_cases shape : graph.successors.length = actions.length
  · cases table : (graph.successors.zip actions)[index]? with
    | none => simp [guarded_blocks, shape, table] at jumped
    | some entry =>
      obtain ⟨row, action⟩ := entry
      cases response : action initial with
      | none => simp [guarded_blocks, shape, table, response] at jumped
      | some transfer =>
        cases transfer with
        | stop value final => simp [guarded_blocks, shape, table, response] at jumped
        | jump target updated =>
          by_cases listed : target ∈ row
          · simp [guarded_blocks, shape, table, response, listed] at jumped
            obtain ⟨rfl, rfl⟩ := jumped
            exact ⟨row, (List.getElem?_zip_eq_some.mp table).1, listed⟩
          · simp [guarded_blocks, shape, table, response, listed] at jumped
  · simp [guarded_blocks, shape] at jumped

inductive DispatchVisits (blocks : Blocks state result) (entry : Nat) (initial : state) : Nat → state → Prop where
  | entry : DispatchVisits blocks entry initial entry initial
  | jump {index next : Nat} {before after : state} :
    DispatchVisits blocks entry initial index before → blocks index before = some (.jump next after) →
      DispatchVisits blocks entry initial next after

theorem guarded_dispatch_reaches (graph : DispatchGraph) (actions : List (state → Option (Transfer state result)))
    (initial final : state) (index : Nat)
    (visited : DispatchVisits (guarded_blocks graph actions) graph.entry initial index final) : Reaches graph index := by
  induction visited with
  | entry => exact .entry
  | jump _ transfer reached =>
    obtain ⟨_, row, listed⟩ := guarded_jump_listed graph actions _ _ _ _ transfer
    exact .jump reached row listed

theorem guarded_dispatch_has_action (graph : DispatchGraph) (actions : List (state → Option (Transfer state result)))
    (initial final : state) (index : Nat) (accepted : valid_dispatch graph = true)
    (shape : graph.successors.length = actions.length)
    (visited : DispatchVisits (guarded_blocks graph actions) graph.entry initial index final) :
    ∃ action, actions[index]? = some action := by
  have reached := guarded_dispatch_reaches graph actions initial final index visited
  have within := dispatch_targets_exist graph accepted index reached
  have valid : index < actions.length := shape ▸ within
  exact ⟨actions[index], List.getElem?_eq_some_iff.mpr ⟨valid, rfl⟩⟩

def computed_jump (symbols : String → Option Int) (targets : String → Option Nat)
    (candidate : Option (Int × String)) : Option Nat :=
  match candidate with
  | none => none
  | some (raw, name) => if symbols name = some raw then targets name else none

theorem computed_jump_matches_symbol (symbols : String → Option Int) (targets : String → Option Nat)
    (raw : Int) (name : String) (next : Nat) :
    computed_jump symbols targets (some (raw, name)) = some next ↔
      symbols name = some raw ∧ targets name = some next := by
  by_cases authentic : symbols name = some raw <;> simp [computed_jump, authentic]

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

def intmap_payload_copy (source destination : Int → Option α)
    (source_offset destination_offset count index : Int) : Option α :=
  let payload := if destination_offset ≤ index ∧ index < destination_offset + count then
    source (source_offset + (index - destination_offset)) else none
  let untouched := if index < destination_offset ∨ destination_offset + count ≤ index then
    destination index else none
  payload.or untouched

theorem payload_copy_refines (source destination : Int → Option α)
    (source_offset destination_offset count index : Int) :
    intmap_payload_copy source destination source_offset destination_offset count index =
      if destination_offset ≤ index ∧ index < destination_offset + count then
        source (source_offset + (index - destination_offset)) else destination index := by
  by_cases inside : destination_offset ≤ index ∧ index < destination_offset + count
  · have untouched : ¬ (index < destination_offset ∨ destination_offset + count ≤ index) := by omega
    simp [intmap_payload_copy, inside, untouched]
  · have untouched : index < destination_offset ∨ destination_offset + count ≤ index := by omega
    simp [intmap_payload_copy, inside, untouched]

def intset_atomic_copy (destination : Int → Bool) (destination_offset count slot : Int) : Bool :=
  if count = 0 then destination slot
  else decide (slot ≤ destination_offset - 8 ∨ destination_offset + count ≤ slot) && destination slot

theorem atomic_copy_refines (destination : Int → Bool) (destination_offset count slot : Int) :
    intset_atomic_copy destination destination_offset count slot = true ↔
      destination slot = true ∧ (count = 0 ∨ slot + 8 ≤ destination_offset ∨ destination_offset + count ≤ slot) := by
  by_cases empty : count = 0
  · simp [intset_atomic_copy, empty]
  · have untouched : (slot ≤ destination_offset - 8 ∨ destination_offset + count ≤ slot) ↔
        slot + 8 ≤ destination_offset ∨ destination_offset + count ≤ slot := by omega
    simp only [intset_atomic_copy, empty, if_false, Bool.and_eq_true, decide_eq_true_eq, false_or,
      untouched, and_comm]

inductive CopyFault where
  | source (fault : AccessFault) | destination (fault : AccessFault) | readonly
  deriving DecidableEq

def runtime_copy_offsets (memory : Memory) (source destination : Pointer) (count : Nat) :
    Except CopyFault (Option (Nat × Nat)) :=
  if count = 0 then .ok none
  else
    match runtime_checked memory (some source) count with
    | .error fault => .error (.source fault)
    | .ok (_, source_offset) =>
      match runtime_checked memory (some destination) count with
      | .error fault => .error (.destination fault)
      | .ok (object, destination_offset) =>
        if object.readonly then .error .readonly else .ok (some (source_offset, destination_offset))

theorem freeze_alias_rejects_copy (memory next : Memory) (owner source destination : Pointer) (count : Nat)
    (src dst : Object) (nonempty : count ≠ 0)
    (frozen : runtime_freeze memory (some owner) = .ok next)
    (same_capability : destination.capability = owner.capability)
    (readable : checked next source count = some src) (destination_access : checked memory destination count = some dst) :
    runtime_copy_offsets next source destination count = .error .readonly := by
  have destination_frozen := freeze_alias_reads memory next owner destination count dst frozen same_capability destination_access
  let so := (source.address - src.base).toNat
  let doff := (destination.address - dst.base).toNat
  have read_source := (checked_refines next source count so src).mpr ⟨readable, rfl⟩
  have read_destination := (checked_refines next destination count doff { dst with readonly := true }).mpr
    ⟨destination_frozen, rfl⟩
  simp [runtime_copy_offsets, nonempty, read_source, read_destination]

theorem copy_offsets_sound (memory : Memory) (source destination : Pointer) (count s d : Nat)
    (copied : runtime_copy_offsets memory source destination count = .ok (some (s, d))) :
    ∃ src dst, memory source.capability = some src ∧ memory destination.capability = some dst ∧
      accessible src source.address count ∧ accessible dst destination.address count ∧
      dst.readonly = false ∧ s = (source.address - src.base).toNat ∧ d = (destination.address - dst.base).toNat := by
  by_cases empty : count = 0
  · simp [runtime_copy_offsets, empty] at copied
  cases source_access : runtime_checked memory (some source) (count : Int) with
  | error fault => simp [runtime_copy_offsets, empty, source_access] at copied
  | ok source_entry =>
    obtain ⟨src, s_offset⟩ := source_entry
    cases dest_access : runtime_checked memory (some destination) (count : Int) with
    | error fault => simp [runtime_copy_offsets, empty, source_access, dest_access] at copied
    | ok dest_entry =>
      obtain ⟨dst, d_offset⟩ := dest_entry
      cases readonly : dst.readonly
      · simp [runtime_copy_offsets, empty, source_access, dest_access, readonly] at copied
        obtain ⟨rfl, rfl⟩ := copied
        obtain ⟨source_checked, s_offset_eq⟩ := (checked_refines memory source count _ src).mp source_access
        obtain ⟨dest_checked, d_offset_eq⟩ := (checked_refines memory destination count _ dst).mp dest_access
        exact ⟨src, dst, (checked_sound memory source count src source_checked).1,
          (checked_sound memory destination count dst dest_checked).1,
          (checked_sound memory source count src source_checked).2,
          (checked_sound memory destination count dst dest_checked).2, readonly, s_offset_eq, d_offset_eq⟩
      · simp [runtime_copy_offsets, empty, source_access, dest_access, readonly] at copied

structure CopyPlanes (α : Type) where
  payload : Int → Option Int
  shadow : Int → Option α
  atomic : Int → Bool

def copy_snapshot (source destination : CopyPlanes α) (source_offset destination_offset count : Int) : CopyPlanes α :=
  ⟨intmap_payload_copy source.payload destination.payload source_offset destination_offset count,
    intmap_shadow_copy source.shadow destination.shadow source_offset destination_offset count,
    intset_atomic_copy destination.atomic destination_offset count⟩

theorem copy_snapshot_refines (source destination : CopyPlanes α) (source_offset destination_offset : Int)
    (count : Nat) (index : Int) :
    let result := copy_snapshot source destination source_offset destination_offset count
    result.payload index = (if destination_offset ≤ index ∧ index < destination_offset + count then
      source.payload (source_offset + (index - destination_offset)) else destination.payload index) ∧
    result.shadow index = capability_shadow_copy source.shadow destination.shadow source_offset destination_offset count index ∧
    (result.atomic index = true ↔ destination.atomic index = true ∧
      (count = 0 ∨ index + 8 ≤ destination_offset ∨ destination_offset + count ≤ index)) := by
  refine ⟨payload_copy_refines _ _ _ _ _ _, shadow_copy_refines _ _ _ _ _ _ (by omega), ?_⟩
  simpa using atomic_copy_refines destination.atomic destination_offset (count : Int) index

def runtime_copy (memory : Memory) (planes : Nat → CopyPlanes α) (source destination : Pointer) (count : Nat) :
    Except CopyFault (Nat → CopyPlanes α) :=
  match runtime_copy_offsets memory source destination count with
  | .error fault => .error fault
  | .ok none => .ok planes
  | .ok (some (s, d)) =>
    .ok (fun key => if key = destination.capability then
      copy_snapshot (planes source.capability) (planes destination.capability) s d count else planes key)

theorem runtime_copy_snapshot (memory : Memory) (planes : Nat → CopyPlanes α) (source destination : Pointer)
    (count s d : Nat) (offsets : runtime_copy_offsets memory source destination count = .ok (some (s, d))) :
    runtime_copy memory planes source destination count = .ok (fun key => if key = destination.capability then
      copy_snapshot (planes source.capability) (planes destination.capability) s d count else planes key) := by
  simp [runtime_copy, offsets]

end Heresy

#print axioms Heresy.lower_correct
#print axioms Heresy.checked_span
#print axioms Heresy.checked_refines
#print axioms Heresy.checked_offset_fits
#print axioms Heresy.invalidation_rejects_aliases
#print axioms Heresy.release_data_sound
#print axioms Heresy.release_data_complete
#print axioms Heresy.release_alias_fault
#print axioms Heresy.release_preserves_other
#print axioms Heresy.integer_store_preserves_shadow
#print axioms Heresy.little_endian_roundtrip
#print axioms Heresy.integer_store_load_roundtrip
#print axioms Heresy.signed_store_load_roundtrip
#print axioms Heresy.scalar_write_refines
#print axioms Heresy.readonly_rejects_store
#print axioms Heresy.freeze_alias_reads
#print axioms Heresy.freeze_alias_rejects_store
#print axioms Heresy.freeze_preserves_other
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
#print axioms Heresy.allocation_plan_sound
#print axioms Heresy.allocation_plans_disjoint
#print axioms Heresy.array_span_at
#print axioms Heresy.array_index_in_bounds
#print axioms Heresy.field_store_bit
#print axioms Heresy.promoted_atomic_rejects_nonzero_padding
#print axioms Heresy.atomic_pointer_snapshot
#print axioms Heresy.atomic_pointer_compare_rejects
#print axioms Heresy.dispatch_targets_exist
#print axioms Heresy.guarded_dispatch_reaches
#print axioms Heresy.guarded_dispatch_has_action
#print axioms Heresy.computed_jump_matches_symbol
#print axioms Heresy.shadow_copy_refines
#print axioms Heresy.payload_copy_refines
#print axioms Heresy.atomic_copy_refines
#print axioms Heresy.copy_offsets_sound
#print axioms Heresy.freeze_alias_rejects_copy
#print axioms Heresy.copy_snapshot_refines
#print axioms Heresy.runtime_copy_snapshot
#print axioms Heresy.lower_program_correct
#print axioms Heresy.lower_commands_correct
