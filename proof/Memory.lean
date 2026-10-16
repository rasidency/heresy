import Proof

set_option warningAsError true

namespace Heresy

structure HeapState where
  objects : Memory
  counter : AllocationCounter

def HeapState.allocated (state : HeapState) : Prop :=
  ∀ ident object, state.objects ident = some object → ident < state.counter.ident

def dead_at (memory : Memory) (ident : Nat) : Prop :=
  ∃ object, memory ident = some object ∧ object.live = false

def replace_object (memory : Memory) (ident : Nat) (object : Object) : Memory :=
  fun key => if key = ident then some object else memory key

def new_object (plan : AllocationPlan) : Object :=
  ⟨plan.address, plan.extent, true, false, fun _ => 0, fun _ => none⟩

inductive HeapTransition : HeapState → HeapState → Prop where
  | observe : HeapTransition state state
  | replace {ident : Nat} {old new : Object} : state.objects ident = some old → new.live = old.live →
      HeapTransition state { state with objects := replace_object state.objects ident new }
  | release {ident : Nat} {object : Object} : state.objects ident = some object →
      HeapTransition state { state with objects := invalidate state.objects ident }
  | allocate : state.counter.ident ≤ host_max →
      plan_allocation state.counter global size host_max = some plan →
      HeapTransition state ⟨replace_object state.objects plan.ident (new_object plan), plan.next⟩

theorem heap_transition_allocated (before after : HeapState) (step : HeapTransition before after)
    (allocated : before.allocated) : after.allocated := by
  intro ident object found
  cases step with
  | observe => exact allocated ident object found
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
  | allocate counter_fits planned =>
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
  | observe => exact ⟨object, found, liveness⟩
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
      exact ⟨{ object with live := false, bytes := fun _ => 0, shadow := fun _ => none }, by simp [invalidate, found], rfl⟩
    · exact ⟨object, by simp [invalidate, same, found], liveness⟩
  | allocate counter_fits planned =>
    rename_i _ _ _ plan
    obtain ⟨_, _, _, _, _, _, _, _, identity, _, _, _⟩ :=
      allocation_plan_sound _ _ _ _ plan counter_fits planned
    have earlier := allocated ident object found
    have distinct : ident ≠ plan.ident := by omega
    exact ⟨object, by simp [replace_object, distinct, found], liveness⟩

inductive HeapTrace : HeapState → HeapState → Prop where
  | start : HeapTrace state state
  | step : HeapTrace before middle → HeapTransition middle after → HeapTrace before after

theorem heap_trace_allocated (before after : HeapState) (trace : HeapTrace before after)
    (allocated : before.allocated) : after.allocated := by
  induction trace with
  | start => exact allocated
  | step _ transition earlier => exact heap_transition_allocated _ _ transition earlier

theorem heap_trace_preserves_dead (before after : HeapState) (trace : HeapTrace before after)
    (allocated : before.allocated) (ident : Nat) (dead : dead_at before.objects ident) :
    dead_at after.objects ident := by
  induction trace with
  | start => exact dead
  | step earlier transition preserved =>
    exact heap_transition_preserves_dead _ _ transition (heap_trace_allocated _ _ earlier allocated) ident preserved

theorem released_alias_stays_dead (before after : HeapState) (released : Pointer) (alias : Pointer)
    (allocated : before.allocated) (same : alias.capability = released.capability)
    (heap : Nat → Bool) (next : Memory)
    (success : runtime_release before.objects heap (.data released) = .ok next)
    (trace : HeapTrace { before with objects := next } after) (displacement count : Int) :
    runtime_checked after.objects (some (offset_pointer alias displacement)) count = .error .dead := by
  obtain ⟨object, access, _, _, rfl⟩ := release_data_sound before.objects next heap released success
  have found := (checked_sound before.objects released 0 object access).1
  have released_step : HeapTransition before { before with objects := invalidate before.objects released.capability } :=
    .release found
  have dead : dead_at (invalidate before.objects released.capability) released.capability :=
    ⟨{ object with live := false, bytes := fun _ => 0, shadow := fun _ => none }, by simp [invalidate, found], rfl⟩
  obtain ⟨last, last_lookup, last_live⟩ := heap_trace_preserves_dead _ _ trace
    (heap_transition_allocated before _ released_step allocated) released.capability dead
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
  ⟨fun index => some (object.bytes index.toNat), fun slot => object.shadow slot.toNat, fun _ => false⟩

def copied_object (source destination : Object) (s d count : Nat) : Object :=
  let result := copy_snapshot (object_planes source) (object_planes destination) s d count
  { destination with
    bytes := fun index => (result.payload index).getD 0,
    shadow := fun slot => result.shadow slot }

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
