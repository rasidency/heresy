import Proof

set_option warningAsError true

namespace Heresy

abbrev ArrayFrames := List (List (Nat × Pointer))

abbrev LiteralPool := List (List UInt8 × Pointer)

inductive FileEvent where
  | opened (path mode : List UInt8) (success : Bool)
  | input (handle count : Nat) (payload : Option (List UInt8))
  | output (handle : Nat) (payload : List UInt8) (success : Bool)
  | closed (handle : Nat) (success : Bool)
  deriving Repr

structure FileWorld where
  events : List FileEvent := []
  handles : List (Nat × Bool) := []
  next : Nat := 1
  deriving Repr

structure HeapState where
  objects : Memory
  counter : AllocationCounter
  arrayFrames : ArrayFrames := []
  literals : LiteralPool := []
  files : FileWorld := {}

def HeapState.allocated (state : HeapState) : Prop :=
  ∀ ident object, state.objects ident = some object → ident < state.counter.ident

def dead_at (memory : Memory) (ident : Nat) : Prop :=
  ∃ object, memory ident = some object ∧ object.live = false

def replace_object (memory : Memory) (ident : Nat) (object : Object) : Memory :=
  fun key => if key = ident then some object else memory key

def new_object (heap : Bool) (plan : AllocationPlan) : Object :=
  ⟨plan.address, plan.extent, true, false, fun _ => 0, fun _ => none, heap, [], fun _ => none⟩

inductive AllocationContent where
  | empty (heap : Bool)
  | literal (bytes : List UInt8)

def AllocationContent.object (plan : AllocationPlan) : AllocationContent → Object
  | .empty heap => new_object heap plan
  | .literal text => { new_object false plan with readonly := true, bytes := fun i => (text[i]?.getD 0).toNat }

def AllocationContent.pool (before : LiteralPool) (plan : AllocationPlan) : AllocationContent → LiteralPool
  | .empty _ => before
  | .literal text => (text, ⟨plan.ident, plan.address⟩) :: before

def AllocationContent.fresh (before : LiteralPool) : AllocationContent → Prop
  | .empty _ => True
  | .literal text => before.lookup text = none

inductive HeapTransition : HeapState → HeapState → Prop where
  | observe : HeapTransition state state
  | files (next : FileWorld) : HeapTransition state { state with files := next }
  | frames (next : ArrayFrames) : HeapTransition state { state with arrayFrames := next }
  | replace {ident : Nat} {old new : Object} : state.objects ident = some old → new.live = old.live →
      HeapTransition state { state with objects := replace_object state.objects ident new }
  | release {ident : Nat} {object : Object} : state.objects ident = some object →
      HeapTransition state { state with objects := invalidate state.objects ident }
  | initialise (content : AllocationContent) : content.fresh state.literals → state.counter.ident ≤ host_max →
      plan_allocation state.counter global size host_max = some plan →
      HeapTransition state ⟨replace_object state.objects plan.ident (content.object plan), plan.next, state.arrayFrames, content.pool state.literals plan, state.files⟩

theorem HeapTransition.allocate (heap : Bool) (fitted : state.counter.ident ≤ host_max)
    (allocation : plan_allocation state.counter global size host_max = some plan) :
    HeapTransition state ⟨replace_object state.objects plan.ident (new_object heap plan), plan.next, state.arrayFrames, state.literals, state.files⟩ :=
  .initialise (.empty heap) trivial fitted allocation

theorem heap_transition_preserves_literal (step : HeapTransition before after)
    (found : before.literals.lookup text = some ptr) : after.literals.lookup text = some ptr := by
  cases step with
  | observe | files | frames | replace | release => exact found
  | initialise content fresh _ _ =>
    cases content with
    | empty => exact found
    | literal bytes =>
      have different : text ≠ bytes := fun same => by
        subst bytes
        exact Option.noConfusion (found.symm.trans fresh)
      simpa [AllocationContent.pool, List.lookup_cons, beq_eq_false_iff_ne.mpr different] using found

theorem heap_transition_allocated (before after : HeapState) (step : HeapTransition before after)
    (allocated : before.allocated) : after.allocated := by
  intro ident object found
  cases step with
  | observe | files _ | frames _ => exact allocated ident object found
  | replace previous preserved =>
    rename_i slot _ _
    by_cases same : ident = slot
    · subst ident
      exact allocated _ _ previous
    · exact allocated _ _ (by simpa [replace_object, same] using found)
  | release previous =>
    rename_i slot _
    by_cases same : ident = slot
    · subst ident
      exact allocated _ _ previous
    · exact allocated _ _ (by simpa [invalidate, same] using found)
  | initialise content fresh counter_fits planned =>
    rename_i _ _ _ plan
    obtain ⟨_, _, _, _, _, _, _, _, identity, grows, _, _⟩ :=
      allocation_plan_sound _ _ _ _ plan counter_fits planned
    by_cases same : ident = plan.ident
    · exact same ▸ grows
    · have previous := allocated ident object (by simpa [replace_object, same] using found)
      exact Nat.lt_trans (identity.symm ▸ previous) grows

theorem heap_transition_preserves_dead (before after : HeapState) (step : HeapTransition before after)
    (allocated : before.allocated) (ident : Nat) (dead : dead_at before.objects ident) :
    dead_at after.objects ident := by
  obtain ⟨object, found, liveness⟩ := dead
  cases step with
  | observe | files _ | frames _ => exact ⟨object, found, liveness⟩
  | replace previous preserved =>
    rename_i slot old new
    by_cases same : ident = slot
    · subst ident
      have equal : old = object := Option.some.inj (previous.symm.trans found)
      exact ⟨new, by simp [replace_object], preserved.trans (equal ▸ liveness)⟩
    · exact ⟨object, by simp [replace_object, same, found], liveness⟩
  | release previous =>
    rename_i slot _
    by_cases same : ident = slot
    · subst ident
      exact ⟨{ object with live := false, bytes := fun _ => 0, shadow := fun _ => none, atomicAddress := fun _ => none }, by simp [invalidate, found], rfl⟩
    · exact ⟨object, by simp [invalidate, same, found], liveness⟩
  | initialise content fresh counter_fits planned =>
    rename_i _ _ _ plan
    obtain ⟨_, _, _, _, _, _, _, _, identity, _, _, _⟩ :=
      allocation_plan_sound _ _ _ _ plan counter_fits planned
    have earlier := allocated ident object found
    have distinct : ident ≠ plan.ident := by omega
    exact ⟨object, by simp [replace_object, distinct, found], liveness⟩

inductive HeapTrace : HeapState → HeapState → Prop where
  | start : HeapTrace state state
  | step : HeapTrace before middle → HeapTransition middle after → HeapTrace before after

theorem heap_trace_prepend {before middle after : HeapState} (first : HeapTransition before middle)
    (rest : HeapTrace middle after) : HeapTrace before after := by
  induction rest with
  | start => exact .step .start first
  | step _ transition earlier => exact .step earlier transition

theorem heap_trace_allocated (before after : HeapState) (trace : HeapTrace before after)
    (allocated : before.allocated) : after.allocated := by
  induction trace with
  | start => exact allocated
  | step _ transition earlier => exact heap_transition_allocated _ _ transition earlier

def HeapState.null_reserved (state : HeapState) : Prop := state.objects 0 = none ∧ 0 < state.counter.ident

theorem heap_transition_reserves_null (before after : HeapState) (step : HeapTransition before after)
    (reserved : before.null_reserved) : after.null_reserved := by
  obtain ⟨empty, positive⟩ := reserved
  cases step with
  | observe | files _ | frames _ => exact ⟨empty, positive⟩
  | replace previous preserved =>
    rename_i ident _ _
    have different : 0 ≠ ident := by
      intro equal
      cases equal
      simp [empty] at previous
    exact ⟨by simp [replace_object, different, empty], positive⟩
  | release previous =>
    rename_i ident _
    have different : 0 ≠ ident := by
      intro equal
      cases equal
      simp [empty] at previous
    exact ⟨by simp [invalidate, different, empty], positive⟩
  | initialise content fresh fitted planned =>
    rename_i _ _ _ plan
    obtain ⟨_, _, _, _, _, _, _, _, identity, grows, _, _⟩ :=
      allocation_plan_sound _ _ _ _ plan fitted planned
    have different : 0 ≠ plan.ident := by omega
    exact ⟨by simp [replace_object, different, empty], Nat.lt_trans (identity.symm ▸ positive) grows⟩

theorem heap_trace_reserves_null (before after : HeapState) (trace : HeapTrace before after)
    (reserved : before.null_reserved) : after.null_reserved := by
  induction trace with
  | start => exact reserved
  | step _ transition earlier => exact heap_transition_reserves_null _ _ transition earlier

theorem heap_trace_preserves_dead (before after : HeapState) (trace : HeapTrace before after)
    (allocated : before.allocated) (ident : Nat) (dead : dead_at before.objects ident) :
    dead_at after.objects ident := by
  induction trace with
  | start => exact dead
  | step earlier transition preserved =>
    exact heap_transition_preserves_dead _ _ transition (heap_trace_allocated _ _ earlier allocated) ident preserved

theorem released_identity_stays_dead (before after : HeapState) (released : Pointer)
    (allocated : before.allocated)
    (heap : Nat → Bool) (next : Memory)
    (success : runtime_release before.objects heap (.data released) = .ok next)
    (trace : HeapTrace { before with objects := next } after) : dead_at after.objects released.capability := by
  obtain ⟨object, access, _, _, rfl⟩ := release_data_sound before.objects next heap released success
  have found := (checked_sound before.objects released 0 object access).1
  have released_step : HeapTransition before { before with objects := invalidate before.objects released.capability } :=
    .release found
  have dead : dead_at (invalidate before.objects released.capability) released.capability :=
    ⟨{ object with live := false, bytes := fun _ => 0, shadow := fun _ => none, atomicAddress := fun _ => none }, by simp [invalidate, found], rfl⟩
  exact heap_trace_preserves_dead _ _ trace (heap_transition_allocated before _ released_step allocated) released.capability dead

theorem released_alias_stays_dead (before after : HeapState) (released : Pointer) (alias : Pointer)
    (allocated : before.allocated) (same : alias.capability = released.capability)
    (heap : Nat → Bool) (next : Memory)
    (success : runtime_release before.objects heap (.data released) = .ok next)
    (trace : HeapTrace { before with objects := next } after) (displacement count : Int) :
    runtime_checked after.objects (some (offset_pointer alias displacement)) count = .error .dead := by
  obtain ⟨last, last_lookup, last_live⟩ := released_identity_stays_dead before after released allocated heap next success trace
  simp [runtime_checked, offset_pointer, same, last_lookup, last_live]

theorem guarded_store_transition (state : HeapState) (pointer : Pointer) (width : Nat) (value : Int)
    (before after : Object) (read : checked state.objects pointer width = some before)
    (stored : guarded_store before pointer.address width value = some after) :
    HeapTransition state { state with objects := replace_object state.objects pointer.capability after } := by
  have found := (checked_sound state.objects pointer width before read).1
  apply HeapTransition.replace found
  unfold guarded_store at stored
  split at stored
  · cases stored
    rfl
  · contradiction

theorem freeze_transition (state : HeapState) (pointer : Pointer) (next : Memory)
    (success : runtime_freeze state.objects (some pointer) = .ok next) :
    HeapTransition state { state with objects := next } := by
  cases found : state.objects pointer.capability with
  | none => simp [runtime_freeze, found] at success
  | some object =>
    simp only [runtime_freeze, found, Except.ok.injEq] at success
    rw [← success]
    exact .replace found (new := {object with readonly := true}) rfl

def object_planes (object : Object) : CopyPlanes Nat :=
  ⟨fun index => some (object.bytes index.toNat), fun slot => object.shadow slot.toNat, fun slot => (object.atomicAddress slot.toNat).isSome⟩

def copied_object (source destination : Object) (s d count : Nat) : Object :=
  let result := copy_snapshot (object_planes source) (object_planes destination) s d count
  { destination with
    bytes := fun index => (result.payload index).getD 0,
    shadow := fun slot => result.shadow slot
    atomicAddress := fun slot => if result.atomic slot then destination.atomicAddress slot else none }

theorem copy_transition (state : HeapState) (source destination : Pointer) (count s d : Nat)
    (offsets : runtime_copy_offsets state.objects source destination count = .ok (some (s, d))) :
    ∃ src dst, state.objects source.capability = some src ∧ state.objects destination.capability = some dst ∧
      HeapTransition state { state with objects := replace_object state.objects destination.capability (copied_object src dst s d count) } := by
  obtain ⟨src, dst, read, write, _, _, _, _, _⟩ := copy_offsets_sound state.objects source destination count s d offsets
  exact ⟨src, dst, read, write, .replace write rfl⟩

def run_heap (step : HeapState → instruction → Except fault HeapState) :
    HeapState → List instruction → Except (HeapState × fault) HeapState
  | state, [] => .ok state
  | state, instruction :: rest =>
    match step state instruction with
    | .ok next => run_heap step next rest
    | .error why => .error (state, why)

def stopped_heap : Except (HeapState × fault) HeapState → HeapState
  | .ok state => state
  | .error (state, _) => state

theorem run_heap_trace (step : HeapState → instruction → Except fault HeapState)
    (sound : ∀ state instruction after, step state instruction = .ok after → HeapTransition state after)
    (state : HeapState) (instructions : List instruction) :
    HeapTrace state (stopped_heap (run_heap step state instructions)) := by
  have follows (start middle after : HeapState) (first : HeapTransition start middle) (rest : HeapTrace middle after) :
      HeapTrace start after := by
    induction rest with
    | start => exact .step .start first
    | step _ next earlier => exact .step earlier next
  induction instructions generalizing state with
  | nil => exact .start
  | cons instruction rest remainder =>
    cases observed : step state instruction with
    | error why => simp [run_heap, observed, stopped_heap]; exact .start
    | ok next =>
      simp only [run_heap, observed]
      exact follows state next _ (sound state instruction next observed) (remainder next)

theorem run_heap_failure_stops (step : HeapState → instruction → Except fault HeapState)
    (state : HeapState) (op : instruction) (rest : List instruction) (why : fault)
    (failed : step state op = .error why) :
    run_heap step state (op :: rest) = .error (state, why) := by
  simp [run_heap, failed]

structure AggregateImage (α : Type) where
  payload : Int → Option Int
  shadow : Int → Option α

def aggregate_slice (plane : Int → Option α) (start count index : Int) : Option α :=
  if 0 ≤ index ∧ index < count then plane (start + index) else none

def read_aggregate (planes : CopyPlanes α) (start count : Int) : AggregateImage α :=
  ⟨aggregate_slice planes.payload start count, aggregate_slice planes.shadow start (max 0 (count - 7))⟩

def write_aggregate (image : AggregateImage α) (destination : CopyPlanes α) (start count : Int) : CopyPlanes α :=
  let first := ((start + 7) / 8) * 8
  let past := max first (start + count - 7)
  let caps := fun index => (image.shadow (index - start)).or
    (if index < first ∨ past ≤ index then destination.shadow index else none)
  ⟨intmap_payload_copy image.payload destination.payload 0 start count, caps,
    fun index => decide (index < first ∨ past ≤ index) && destination.atomic index⟩

theorem aggregate_reads_complete_words (planes : CopyPlanes α) (start count slot : Int) :
    (read_aggregate planes start count).shadow slot =
      if 0 ≤ slot ∧ slot + 8 ≤ count then planes.shadow (start + slot) else none := by
  have slot_fits : (0 ≤ slot ∧ slot < max 0 (count - 7)) ↔ (0 ≤ slot ∧ slot + 8 ≤ count) := by omega
  simp [read_aggregate, aggregate_slice, slot_fits]

theorem aggregate_store_preserves_other_words (source destination : CopyPlanes α) (s d count index : Int)
    (outside : index < d ∨ d + count < index + 8) (aligned : index % 8 = 0) :
    let result := write_aggregate (read_aggregate source s count) destination d count
    result.shadow index = destination.shadow index ∧ result.atomic index = destination.atomic index := by
  have outside_rounded : index < ((d + 7) / 8) * 8 ∨ max (((d + 7) / 8) * 8) (d + count - 7) ≤ index := by omega
  have no_shadow : ¬ (0 ≤ index - d ∧ index - d + 8 ≤ count) := by omega
  dsimp only [write_aggregate]
  rw [aggregate_reads_complete_words, if_neg no_shadow]
  simp [outside_rounded]

theorem aggregate_store_replaces_complete_words (source destination : CopyPlanes α) (s d count index : Int)
    (inside : d ≤ index ∧ index + 8 ≤ d + count) (aligned : index % 8 = 0) :
    let result := write_aggregate (read_aggregate source s count) destination d count
    result.shadow index = source.shadow (s + (index - d)) ∧ result.atomic index = false := by
  have inside_rounded : ¬ (index < ((d + 7) / 8) * 8 ∨ max (((d + 7) / 8) * 8) (d + count - 7) ≤ index) := by omega
  have shadow_fits : 0 ≤ index - d ∧ index - d + 8 ≤ count := by omega
  dsimp only [write_aggregate]
  rw [aggregate_reads_complete_words, if_pos shadow_fits]
  simp [inside_rounded]

theorem aggregate_store_copies_payload (source destination : CopyPlanes α) (s d count index : Int) :
    (write_aggregate (read_aggregate source s count) destination d count).payload index =
      if d ≤ index ∧ index < d + count then source.payload (s + (index - d)) else destination.payload index := by
  by_cases inside : d ≤ index ∧ index < d + count
  · have relative : 0 ≤ index - d ∧ index - d < count := by omega
    simp [write_aggregate, payload_copy_refines, read_aggregate, aggregate_slice, inside, relative]
  · simp [write_aggregate, payload_copy_refines, inside]

inductive TransferMode where
  | load (target destination : Pointer)
  | store (target source : Pointer)
  | exchange (target source destination : Pointer)

def atomic_transfer (read : HeapState → Bool → Pointer → Except fault α)
    (write : HeapState → Bool → Pointer → α → Except fault HeapState)
    (state : HeapState) : TransferMode → Except (HeapState × fault) HeapState :=
  let observed := fun atomic pointer next => match read state atomic pointer with
    | .ok value => next value
    | .error why => .error (state, why)
  let commit := fun heap (atomic, pointer, value) => write heap atomic pointer value
  fun mode => match mode with
  | .load target destination => observed true target fun old =>
    run_heap commit state [(false, destination, old)]
  | .store target source => observed false source fun desired =>
    run_heap commit state [(true, target, desired)]
  | .exchange target source destination => observed false source fun desired =>
    observed true target fun old =>
      run_heap commit state [(true, target, desired), (false, destination, old)]

theorem atomic_transfer_heap_trace (read : HeapState → Bool → Pointer → Except fault α)
    (write : HeapState → Bool → Pointer → α → Except fault HeapState)
    (sound : ∀ heap atomic pointer value after, write heap atomic pointer value = .ok after → HeapTransition heap after)
    (state : HeapState) (mode : TransferMode) :
    HeapTrace state (stopped_heap (atomic_transfer read write state mode)) := by
  let commit (heap : HeapState) (op : Bool × Pointer × α) := write heap op.1 op.2.1 op.2.2
  have valid (ops : List (Bool × Pointer × α)) :=
    run_heap_trace commit (fun heap op after applied => sound heap op.1 op.2.1 op.2.2 after applied) state ops
  cases mode with
  | load target destination =>
    cases seen : read state true target with
    | error why => simpa [atomic_transfer, seen, stopped_heap] using (HeapTrace.start (state := state))
    | ok old => simpa [atomic_transfer, seen] using valid [(false, destination, old)]
  | store target source =>
    cases seen : read state false source with
    | error why => simpa [atomic_transfer, seen, stopped_heap] using (HeapTrace.start (state := state))
    | ok desired => simpa [atomic_transfer, seen] using valid [(true, target, desired)]
  | exchange target source destination =>
    cases seen : read state false source with
    | error why => simpa [atomic_transfer, seen, stopped_heap] using (HeapTrace.start (state := state))
    | ok desired =>
      cases previous : read state true target with
      | error why => simpa [atomic_transfer, seen, previous, stopped_heap] using (HeapTrace.start (state := state))
      | ok old =>
        simpa [atomic_transfer, seen, previous] using valid [(true, target, desired), (false, destination, old)]

theorem exchange_retains_first_write_on_fault (read : HeapState → Bool → Pointer → Except fault α)
    (write : HeapState → Bool → Pointer → α → Except fault HeapState)
    (before middle : HeapState) (source target destination : Pointer) (old desired : α) (why : fault)
    (read_source : read before false source = .ok desired) (read_target : read before true target = .ok old)
    (stored : write before true target desired = .ok middle) (failed : write middle false destination old = .error why) :
    atomic_transfer read write before (.exchange target source destination) = .error (middle, why) := by
  simp [atomic_transfer, read_source, read_target, run_heap, stored, failed]

inductive CompareMode where
  | scalar
  | copy
  | bytes (width ordinary : Nat)

structure CompareValues (α : Type) where
  observed : α
  replacement : α
  observed_bits : Int
  expected_bits : Int
  promoted_bits : Int
  payloads_equal : Bool

inductive CompareWrite (α : Type) where
  | target (value : α)
  | expected (value : α)
  | expected_bits (width : Nat) (value : Int)

def compare_matches (mode : CompareMode) (values : CompareValues α) : Bool :=
  match mode with
  | .scalar => values.observed_bits == values.expected_bits
  | .copy => values.payloads_equal
  | .bytes width ordinary =>
    (if width = ordinary then values.observed_bits else values.promoted_bits) == values.expected_bits

def compare_write (mode : CompareMode) (values : CompareValues α) (equal : Bool) : Option (CompareWrite α) :=
  if equal then some (.target values.replacement)
  else match mode with
  | .bytes width ordinary => if width = ordinary then some (.expected_bits width values.observed_bits) else none
  | _ => some (.expected values.observed)

def atomic_compare_exchange (check : HeapState → Except fault (CompareValues α))
    (commit : HeapState → CompareWrite α → Except fault HeapState) (state : HeapState) (mode : CompareMode) :
    Except fault (Bool × HeapState) :=
  match check state with
  | .error why => .error why
  | .ok values =>
    let equal := compare_matches mode values
    match compare_write mode values equal with
    | none => .ok (equal, state)
    | some operation =>
      match commit state operation with
      | .error why => .error why
      | .ok after => .ok (equal, after)

theorem compare_exchange_transition (check : HeapState → Except fault (CompareValues α))
    (commit : HeapState → CompareWrite α → Except fault HeapState)
    (sound : ∀ state operation after, commit state operation = .ok after → HeapTransition state after)
    (state after : HeapState) (mode : CompareMode) (result : Bool)
    (success : atomic_compare_exchange check commit state mode = .ok (result, after)) : HeapTransition state after := by
  cases observed : check state with
  | error why => simp [atomic_compare_exchange, observed] at success
  | ok values =>
    cases chosen : compare_write mode values (compare_matches mode values) with
    | none =>
      simp [atomic_compare_exchange, observed, chosen] at success
      exact success.2 ▸ .observe
    | some operation =>
      cases stored : commit state operation with
      | error why => simp [atomic_compare_exchange, observed, chosen, stored] at success
      | ok committed =>
        simp [atomic_compare_exchange, observed, chosen, stored] at success
        exact success.2 ▸ sound _ _ _ stored

theorem promoted_compare_rejection_skips_write (check : HeapState → Except fault (CompareValues α))
    (commit : HeapState → CompareWrite α → Except fault HeapState) (state : HeapState)
    (values : CompareValues α) (width ordinary : Nat) (promoted : width ≠ ordinary)
    (observed : check state = .ok values) (canonical : unsigned (8 * ordinary) values.expected_bits = values.expected_bits)
    (padding : modulus (8 * ordinary) ≤ values.promoted_bits) :
    atomic_compare_exchange check commit state (.bytes width ordinary) = .ok (false, state) := by
  have different := promoted_atomic_rejects_nonzero_padding (8 * ordinary) values.promoted_bits values.expected_bits padding
  unfold promoted_atomic_compare at different
  rw [canonical] at different
  simp [atomic_compare_exchange, observed, compare_matches, compare_write, promoted, different]

theorem compare_exchange_commits_observed_on_scalar_mismatch (check : HeapState → Except fault (CompareValues α))
    (commit : HeapState → CompareWrite α → Except fault HeapState) (state next : HeapState)
    (values : CompareValues α) (observed : check state = .ok values)
    (different : values.observed_bits ≠ values.expected_bits) (stored : commit state (.expected values.observed) = .ok next) :
    atomic_compare_exchange check commit state .scalar = .ok (false, next) := by
  simp [atomic_compare_exchange, observed, compare_matches, compare_write, beq_eq_false_iff_ne.mpr different, stored]

inductive PointerWordFault where
  | access (fault : AccessFault)
  | unaligned
  | readonly

def data_pointer_word (object : Object) (slot : Nat) : Option Nat × Int :=
  (object.shadow slot, little_endian_read 8 (fun i => object.bytes (slot + i)))

def atomic_data_pointer (object : Object) (slot : Nat) : Option Nat × Int :=
  let (cap, raw) := data_pointer_word object slot
  (cap, (object.atomicAddress slot).getD raw)

def write_pointer_word (object : Object) (slot : Nat) (value : Pointer) (atomic : Bool := false) : Object :=
  { integer_store object slot 8 value.address with
    shadow := fun index => if index = slot then some value.capability else object.shadow index
    atomicAddress := fun index => if index = slot then (if atomic then some value.address else none)
      else object.atomicAddress index }

theorem atomic_pointer_payload_store (object : Object) (slot offset width : Nat) (pointer : Pointer) (word : Int) :
    atomic_data_pointer (integer_store (write_pointer_word object slot pointer true) offset width word) slot =
      (some pointer.capability, pointer.address) := by
  simp [atomic_data_pointer, data_pointer_word, integer_store, write_pointer_word]

theorem ordinary_pointer_clears_atomic (object : Object) (slot : Nat) (pointer : Pointer) :
    atomic_data_pointer (write_pointer_word object slot pointer) slot =
      data_pointer_word (write_pointer_word object slot pointer) slot := by
  simp [atomic_data_pointer, write_pointer_word]

theorem pointer_byte_observes_address (object : Object) (slot index : Nat) (value : Pointer) (inside : index < 8) :
    (write_pointer_word object slot value).bytes (slot + index) = little_endian_byte value.address index := by
  have span : slot ≤ slot + index ∧ slot + index < slot + 8 := by omega
  simp [write_pointer_word, integer_store, span]

theorem pointer_bytes_distinguish_layouts (object : Object) (slot index : Nat) (left right : Pointer)
    (inside : index < 8) (different : little_endian_byte left.address index ≠ little_endian_byte right.address index) :
    (write_pointer_word object slot left).bytes (slot + index) ≠
      (write_pointer_word object slot right).bytes (slot + index) := by
  simpa only [pointer_byte_observes_address object slot index _ inside] using different

theorem data_pointer_word_roundtrip (object : Object) (slot : Nat) (value : Pointer) :
    data_pointer_word (write_pointer_word object slot value) slot =
      (some value.capability, unsigned 64 value.address) := by
  simp [data_pointer_word, write_pointer_word, integer_store_load_roundtrip]

theorem data_pointer_word_preserves_disjoint (object : Object) (stored observed : Nat) (value : Pointer)
    (disjoint : stored + 8 ≤ observed ∨ observed + 8 ≤ stored) :
    data_pointer_word (write_pointer_word object stored value) observed = data_pointer_word object observed := by
  have different : observed ≠ stored := by omega
  apply Prod.ext
  · simp [data_pointer_word, write_pointer_word, different]
  · unfold data_pointer_word little_endian_read
    apply congrArg List.sum
    apply List.map_congr_left
    intro i present
    have inside := List.mem_range.mp present
    change (integer_store object stored 8 value.address).bytes (observed + i) * 256 ^ i =
      object.bytes (observed + i) * 256 ^ i
    rw [integer_store_preserves_other _ _ _ _ _ (by omega)]

theorem copied_variadic_cursor_keeps_position (object : Object) (original copied : Nat) (cursor : Pointer)
    (slot : ArgumentSlot) (wide : Bool) (disjoint : original + 8 ≤ copied ∨ copied + 8 ≤ original) :
    let next := (variadic_access cursor.address.toNat slot wide).2
    let snapshot := write_pointer_word object copied cursor
    let advanced := write_pointer_word snapshot original (offset_pointer cursor ((next : Int) - cursor.address))
    data_pointer_word advanced copied = (some cursor.capability, unsigned 64 cursor.address) := by
  dsimp only
  rw [data_pointer_word_preserves_disjoint _ _ _ _ disjoint, data_pointer_word_roundtrip]

def read_data_pointer_word (memory : Memory) (pointer : Pointer) : Except PointerWordFault (Option Nat × Int) :=
  match runtime_checked memory (some pointer) 8 with
  | .error why => .error (.access why)
  | .ok (object, slot) =>
    if pointer.address % 8 = 0 then .ok (data_pointer_word object slot) else .error .unaligned

def store_data_pointer_word (state : HeapState) (pointer value : Pointer) : Except PointerWordFault HeapState :=
  match runtime_checked state.objects (some pointer) 8 with
  | .error why => .error (.access why)
  | .ok (object, slot) =>
    if object.readonly then .error .readonly
    else if pointer.address % 8 = 0 then
      .ok { state with objects := replace_object state.objects pointer.capability (write_pointer_word object slot value) }
    else .error .unaligned

theorem data_pointer_store_refines (state next : HeapState) (pointer value : Pointer)
    (stored : store_data_pointer_word state pointer value = .ok next) :
    HeapTransition state next ∧ read_data_pointer_word next.objects pointer =
      .ok (some value.capability, unsigned 64 value.address) := by
  cases access : runtime_checked state.objects (some pointer) 8 with
  | error why => simp [store_data_pointer_word, access] at stored
  | ok word =>
    obtain ⟨object, slot⟩ := word
    by_cases readonly : object.readonly = true
    · simp [store_data_pointer_word, access, readonly] at stored
    by_cases aligned : pointer.address % 8 = 0
    · simp [store_data_pointer_word, access, readonly, aligned] at stored
      subst next
      have ⟨checked_word, displacement⟩ := (checked_refines state.objects pointer 8 slot object).mp access
      have ⟨found, valid⟩ := checked_sound state.objects pointer 8 object checked_word
      let updated := write_pointer_word object slot value
      have found_updated : replace_object state.objects pointer.capability updated pointer.capability = some updated := by
        simp [replace_object]
      have checked_updated : runtime_checked (replace_object state.objects pointer.capability updated) (some pointer) 8 =
          .ok (updated, slot) := by
        apply (checked_refines _ pointer 8 slot updated).mpr
        exact ⟨by simp only [checked, found_updated, if_pos (show accessible updated pointer.address 8 from valid)], displacement⟩
      refine ⟨.replace found rfl, ?_⟩
      change read_data_pointer_word (replace_object state.objects pointer.capability updated) pointer = _
      simp [read_data_pointer_word, checked_updated, aligned, updated, data_pointer_word_roundtrip]
    · simp [store_data_pointer_word, access, readonly, aligned] at stored

inductive FileReadFault where
  | access (fault : AccessFault)
  | readonly

structure FileReadRequest where
  destination : Pointer
  element_size : Nat
  element_count : Nat

def FileReadRequest.total (request : FileReadRequest) : Nat :=
  request.element_size * request.element_count

def file_read_destination (memory : Memory) (request : FileReadRequest) : Except FileReadFault (Object × Nat) :=
  match runtime_checked memory (some request.destination) request.total with
  | .error fault => .error (.access fault)
  | .ok (object, displacement) =>
    if object.readonly then .error .readonly else .ok (object, displacement)

def file_read_begin (memory : Memory) (request : FileReadRequest) : Except FileReadFault (Option Nat) :=
  if request.total = 0 then .ok none
  else
    match file_read_destination memory request with
    | .error fault => .error fault
    | .ok _ => .ok (some request.total)

theorem file_read_requests_positive_span (memory : Memory) (request : FileReadRequest) (total : Nat)
    (started : file_read_begin memory request = .ok (some total)) :
    total = request.total ∧ 0 < total ∧ ∃ object displacement,
      file_read_destination memory request = .ok (object, displacement) := by
  by_cases empty : request.total = 0
  · simp [file_read_begin, empty] at started
  cases checked_word : file_read_destination memory request with
  | error why => simp [file_read_begin, empty, checked_word] at started
  | ok pair =>
    obtain ⟨object, displacement⟩ := pair
    have same : request.total = total := by simpa [file_read_begin, empty, checked_word] using started
    exact ⟨same.symm, by omega, object, displacement, rfl⟩

private def file_read_insert (state : Nat × (Nat → Int)) (byte : Int) : Nat × (Nat → Int) :=
  (state.1 + 1, fun index => if index = state.1 then byte else state.2 index)

def file_read_bytes (object : Object) (displacement : Nat) (payload : List Int) : Object :=
  { object with bytes := (payload.foldl file_read_insert (displacement, object.bytes)).2 }

private theorem file_read_payload (payload : List Int) (bytes : Nat → Int) (displacement index : Nat) :
    (payload.foldl file_read_insert (displacement, bytes)).2 index =
      if displacement ≤ index then payload[index - displacement]?.getD (bytes index) else bytes index := by
  induction payload generalizing displacement bytes with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldl_cons, file_read_insert, ih]
    by_cases before : index < displacement
    · have different : index ≠ displacement := by omega
      simp [Nat.not_le.mpr before, different, show ¬displacement + 1 ≤ index by omega]
    by_cases at_start : index = displacement
    · subst index
      simp [show ¬displacement + 1 ≤ displacement by omega]
    have later : displacement + 1 ≤ index := by omega
    have difference : index - displacement = (index - (displacement + 1)) + 1 := by omega
    simp [later, Nat.le_of_lt (show displacement < index by omega), at_start, difference]

structure FileReadResult where
  heap : HeapState
  consumed : Nat
  result : Except FileReadFault Nat

def file_read_finish (state : HeapState) (request : FileReadRequest) (payload : List Int) : FileReadResult :=
  match file_read_destination state.objects request with
  | .error fault => ⟨state, payload.length, .error fault⟩
  | .ok (object, displacement) =>
    let updated := file_read_bytes object displacement payload
    ⟨{ state with objects := replace_object state.objects request.destination.capability updated },
      payload.length, .ok (payload.length / request.element_size)⟩

theorem file_read_finish_transition (state : HeapState) (request : FileReadRequest) (payload : List Int) :
    HeapTransition state (file_read_finish state request payload).heap := by
  cases access : runtime_checked state.objects (some request.destination) (request.total : Int) with
  | error why => simpa [file_read_finish, file_read_destination, access] using (HeapTransition.observe (state := state))
  | ok pair =>
    obtain ⟨object, displacement⟩ := pair
    by_cases readonly : object.readonly = true
    · simpa [file_read_finish, file_read_destination, access, readonly] using (HeapTransition.observe (state := state))
    · have checked_word := ((checked_refines state.objects request.destination request.total displacement object).mp access).1
      have found := (checked_sound state.objects request.destination request.total object checked_word).1
      simp only [file_read_finish, file_read_destination, access, readonly]
      exact .replace found rfl

theorem file_read_copies_partial_element (object : Object) (displacement : Nat) (payload : List Int) (index : Nat)
    (inside : index < payload.length) :
    (file_read_bytes object displacement payload).bytes (displacement + index) = payload[index] := by
  simp [file_read_bytes, file_read_payload, List.getElem?_eq_getElem inside]

theorem file_read_preserves_outside (object : Object) (displacement : Nat) (payload : List Int) (index : Nat)
    (outside : index < displacement ∨ displacement + payload.length ≤ index) :
    (file_read_bytes object displacement payload).bytes index = object.bytes index := by
  by_cases after_start : displacement ≤ index
  · have past : payload.length ≤ index - displacement := by omega
    simp [file_read_bytes, file_read_payload, after_start, List.getElem?_eq_none past]
  · simp [file_read_bytes, file_read_payload, after_start]

theorem file_read_writes_within_allocation (state : HeapState) (request : FileReadRequest)
    (object : Object) (displacement : Nat) (payload : List Int) (index : Nat)
    (access : runtime_checked state.objects (some request.destination) request.total = .ok (object, displacement))
    (fits : payload.length ≤ request.total) (outside : object.size ≤ index) :
    (file_read_bytes object displacement payload).bytes index = object.bytes index := by
  have ⟨checked_word, offset⟩ := (checked_refines state.objects request.destination request.total displacement object).mp access
  have ⟨_, lower, upper⟩ := checked_span state.objects request.destination request.total object checked_word
  apply file_read_preserves_outside
  omega

theorem file_read_short_count (state : HeapState) (request : FileReadRequest) (payload : List Int)
    (fits : payload.length ≤ request.total)
    (elements : Nat) (success : (file_read_finish state request payload).result = .ok elements) :
    elements = payload.length / request.element_size ∧ elements ≤ request.element_count := by
  cases checked_word : file_read_destination state.objects request with
  | error why => simp [file_read_finish, checked_word] at success
  | ok pair =>
    obtain ⟨object, displacement⟩ := pair
    have same : payload.length / request.element_size = elements := by simpa [file_read_finish, checked_word] using success
    refine ⟨same.symm, ?_⟩
    rw [← same]
    apply Nat.div_le_of_le_mul
    simpa [FileReadRequest.total, Nat.mul_comm] using fits

theorem file_read_after_release (before after : HeapState) (request : FileReadRequest) (released : Pointer)
    (allocated : before.allocated) (same : request.destination.capability = released.capability)
    (owned : Nat → Bool) (next : Memory) (released_ok : runtime_release before.objects owned (.data released) = .ok next)
    (trace : HeapTrace { before with objects := next } after) (payload : List Int) :
    let result := file_read_finish after request payload
    result.heap = after ∧ result.consumed = payload.length ∧ result.result = .error (.access .dead) := by
  obtain ⟨last, found_last, liveness⟩ :=
    released_identity_stays_dead before after released allocated owned next released_ok trace
  simp [file_read_finish, file_read_destination, runtime_checked, same, found_last, liveness]

def file_write_payload (memory : Memory) (source : Option Pointer) (size count : Nat) :
    Except AccessFault (List Int) :=
  if size * count = 0 then .ok []
  else
    match runtime_checked memory source (size * count : Nat) with
    | .error why => .error why
    | .ok (object, offset) => .ok ((List.range (size * count)).map (fun index => object.bytes (offset + index)))

def FileWriteSnapshot (memory : Memory) (pointer : Pointer) (size count : Nat) (payload : List Int) : Prop :=
  ∃ object, checked memory pointer (size * count) = some object ∧
    payload.length = size * count ∧ ∀ (index : Nat) (inside : index < payload.length),
      payload[index] = object.bytes ((pointer.address - object.base).toNat + index)

theorem file_write_snapshot_correct (memory : Memory) (pointer : Pointer) (size count : Nat)
    (nonempty : size * count ≠ 0) (payload : List Int) :
    file_write_payload memory (some pointer) size count = .ok payload ↔
      FileWriteSnapshot memory pointer size count payload := by
  constructor
  · intro returned
    cases access : runtime_checked memory (some pointer) (size * count : Nat) with
    | error why => simp only [file_write_payload, nonempty, if_false, access, reduceCtorEq] at returned
    | ok pair =>
      obtain ⟨object, offset⟩ := pair
      obtain ⟨valid, displacement⟩ := (checked_refines memory pointer _ offset object).mp access
      simp only [file_write_payload, nonempty, if_false, access, Except.ok.injEq] at returned
      subst payload
      exact ⟨object, valid, by simp, fun index inside => by simp [displacement]⟩
  · rintro ⟨object, valid, length, bytes⟩
    have access := (checked_refines memory pointer _ _ object).mpr ⟨valid, rfl⟩
    simp only [file_write_payload, nonempty, if_false, access]
    apply congrArg Except.ok
    apply List.ext_getElem
    · simpa using length.symm
    · intro index _ inside
      simpa using (bytes index inside).symm

theorem file_read_write_roundtrip (object : Object) (offset : Nat) (payload : List Int) :
    (List.range payload.length).map (fun index =>
      (file_read_bytes object offset payload).bytes (offset + index)) = payload := by
  apply List.ext_getElem
  · simp
  · intro index _ inside
    simpa using file_read_copies_partial_element object offset payload index inside

end Heresy

#print axioms Heresy.heap_trace_allocated
#print axioms Heresy.released_alias_stays_dead
#print axioms Heresy.guarded_store_transition
#print axioms Heresy.freeze_transition
#print axioms Heresy.copy_transition
#print axioms Heresy.run_heap_trace
#print axioms Heresy.aggregate_reads_complete_words
#print axioms Heresy.aggregate_store_preserves_other_words
#print axioms Heresy.aggregate_store_replaces_complete_words
#print axioms Heresy.aggregate_store_copies_payload
#print axioms Heresy.atomic_transfer_heap_trace
#print axioms Heresy.exchange_retains_first_write_on_fault
#print axioms Heresy.compare_exchange_transition
#print axioms Heresy.promoted_compare_rejection_skips_write
#print axioms Heresy.compare_exchange_commits_observed_on_scalar_mismatch
#print axioms Heresy.data_pointer_store_refines
#print axioms Heresy.data_pointer_word_preserves_disjoint
#print axioms Heresy.copied_variadic_cursor_keeps_position
#print axioms Heresy.file_read_finish_transition
#print axioms Heresy.file_read_requests_positive_span
#print axioms Heresy.file_read_copies_partial_element
#print axioms Heresy.file_read_preserves_outside
#print axioms Heresy.file_read_writes_within_allocation
#print axioms Heresy.file_read_after_release
#print axioms Heresy.file_write_snapshot_correct
#print axioms Heresy.file_read_write_roundtrip
