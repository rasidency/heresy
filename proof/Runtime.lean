import Memory
import Semantics

set_option warningAsError true

namespace Heresy

inductive HeapEffect where
  | allocate (size : Nat) (heap : Bool := true)
  | allocateGlobal (size : Nat)
  | loadByte (address : Pointer)
  | storeByte (address : Pointer) (value : UInt8)
  | loadWord (address : Pointer) (width : Nat)
  | storeWord (address : Pointer) (width : Nat) (value : Int)
  | storeBits (address : Pointer) (shift width : Nat) (value : Int)
  | loadPointer (address : Pointer)
  | storePointer (address value : Pointer)
  | clear (address : Pointer) (count : Nat)
  | copyAggregate (source destination : Pointer) (count : Nat)
  | copy (source destination : Pointer) (count : Nat)
  | release (address : Pointer)

inductive HeapReply where
  | done
  | byte (value : UInt8)
  | word (value : Int)
  | pointer (value : Pointer)

inductive HeapFault where
  | access (fault : AccessFault)
  | copy (fault : CopyFault)
  | space
  | hostSize
  | signedOverflow
  | readonly
  | unaligned
  | nonHeapRelease
  | interiorRelease
  | missingBlock
  deriving DecidableEq

structure HeapEdit where
  reply : HeapReply := .done
  object : Option (Nat × Object) := none
  counter : Option AllocationCounter := none

private def write_image (object : Object) (image : AggregateImage Nat) (offset count : Nat) : Object :=
  let updated := write_aggregate image (object_planes object) offset count
  { object with
      bytes := fun index => (updated.payload index).getD 0
      shadow := fun index => updated.shadow index }

def cleared_object (object : Object) (offset count : Nat) : Object :=
  write_image object ⟨fun _ => none, fun _ => none⟩ offset count

theorem clear_zeroes_bytes (object : Object) (offset count index : Nat) (inside : offset ≤ index ∧ index < offset + count) :
    (cleared_object object offset count).bytes index = 0 := by
  have range : (offset : Int) ≤ (index : Int) ∧ (index : Int) < (offset : Int) + (count : Int) := by omega
  simp [cleared_object, write_image, write_aggregate, payload_copy_refines, range, inside.1]

theorem clear_preserves_bytes (object : Object) (offset count index : Nat) (outside : index < offset ∨ offset + count ≤ index) :
    (cleared_object object offset count).bytes index = object.bytes index := by
  have away : ¬(offset ≤ index ∧ (index : Int) < (offset : Int) + (count : Int)) := by omega
  simp [cleared_object, write_image, write_aggregate, payload_copy_refines, object_planes, away]

private def aggregate_unaligned (destination : Pointer) (count : Nat) (saved : AggregateImage Nat) : Bool :=
  decide (destination.address % 8 ≠ 0) && (List.range (count - 7)).any (fun index => (saved.shadow index).isSome)

def bitfield_bytes (shift width : Nat) : Nat := (shift + width + 7) / 8

def bitfield_update (object : Object) (offset shift width : Nat) (value : Int) : Object :=
  let count := bitfield_bytes shift width
  let raw := little_endian_read count (fun index => object.bytes (offset + index))
  let updated := field_store shift width raw.toNat (unsigned width value).toNat
  integer_store object offset count updated

theorem bitfield_update_bit (object : Object) (offset shift width index : Nat) (value : Int)
    (covered : index < 8 * bitfield_bytes shift width) :
    let count := bitfield_bytes shift width
    let previous := little_endian_read count (fun byte => object.bytes (offset + byte))
    let updated := bitfield_update object offset shift width value
    (little_endian_read count (fun byte => updated.bytes (offset + byte))).toNat.testBit index =
      if shift ≤ index ∧ index - shift < width then (unsigned width value).toNat.testBit (index - shift)
      else previous.toNat.testBit index := by
  dsimp only [bitfield_update]
  rw [integer_store_load_roundtrip]
  have truncation (raw bits : Nat) : (unsigned bits (raw : Int)).toNat = raw % 2 ^ bits := by
    rw [unsigned, modulus]
    have cast : (2 : Int) ^ bits = ((2 ^ bits : Nat) : Int) := by simp
    rw [cast, ← Int.natCast_emod]
    rfl
  rw [truncation, Nat.testBit_mod_two_pow, field_store_bit]
  simp [covered]

def heap_effect (state : HeapState) : HeapEffect → Except HeapFault HeapEdit
  | .allocate size heap =>
    match plan_allocation state.counter false size 9223372036854775807 with
    | none => .error .space
    | some plan => .ok ⟨.pointer ⟨plan.ident, plan.address⟩,
        some (plan.ident, new_object heap plan), some plan.next⟩
  | .allocateGlobal size =>
    match plan_allocation state.counter true size 9223372036854775807 with
    | none => .error .space
    | some plan => .ok ⟨.pointer ⟨plan.ident, plan.address⟩,
        some (plan.ident, new_object false plan), some plan.next⟩
  | .loadByte address => do
    let (object, slot) ← (runtime_checked state.objects (some address) 1).mapError .access
    return { reply := .byte (UInt8.ofNat (object.bytes slot).toNat) }
  | .storeByte address value => do
    let (object, slot) ← (runtime_checked state.objects (some address) 1).mapError .access
    if object.readonly then throw .readonly
    return { object := some (address.capability, integer_store object slot 1 value.toNat) }
  | .loadWord address width => do
    let (object, slot) ← (runtime_checked state.objects (some address) width).mapError .access
    return { reply := .word (little_endian_read width (fun index => object.bytes (slot + index))) }
  | .storeWord address width value => do
    let (object, slot) ← (runtime_checked state.objects (some address) width).mapError .access
    if object.readonly then throw .readonly
    return { object := some (address.capability, integer_store object slot width value) }
  | .storeBits address shift width value => do
    let (object, slot) ← (runtime_checked state.objects (some address) (bitfield_bytes shift width)).mapError .access
    if object.readonly then throw .readonly
    return { object := some (address.capability, bitfield_update object slot shift width value) }
  | .loadPointer address => do
    let (object, slot) ← (runtime_checked state.objects (some address) 8).mapError .access
    if address.address % 8 ≠ 0 then throw .unaligned
    let (capability, number) := data_pointer_word object slot
    return { reply := .pointer ⟨capability.getD 0, number⟩ }
  | .storePointer address value => do
    let (object, slot) ← (runtime_checked state.objects (some address) 8).mapError .access
    if object.readonly then throw .readonly
    if address.address % 8 ≠ 0 then throw .unaligned
    return { object := some (address.capability, write_pointer_word object slot value) }
  | .clear address count => do
    let (object, slot) ← (runtime_checked state.objects (some address) count).mapError .access
    if object.readonly then throw .readonly
    return { object := some (address.capability, cleared_object object slot count) }
  | .copyAggregate source destination count => do
    let (fromObject, fromOffset) ← (runtime_checked state.objects (some source) count).mapError .access
    let (toObject, toOffset) ← (runtime_checked state.objects (some destination) count).mapError .access
    if toObject.readonly then throw .readonly
    let saved := read_aggregate (object_planes fromObject) fromOffset count
    if aggregate_unaligned destination count saved then
      throw .unaligned
    return { object := some (destination.capability, write_image toObject saved toOffset count) }
  | .copy source destination count => do
    let offsets ← (runtime_copy_offsets state.objects source destination count).mapError .copy
    let some (s, d) := offsets | return {}
    match state.objects source.capability, state.objects destination.capability with
    | some src, some dst =>
      return { object := some (destination.capability, copied_object src dst s d count) }
    | _, _ => throw (.access .noCapability)
  | .release address =>
    if address.capability == 0 && address.address == 0 then .ok {}
    else do
      let (object, slot) ← (runtime_checked state.objects (some address) 0).mapError .access
      if !object.heap then .error .nonHeapRelease
      else if slot ≠ 0 then .error .interiorRelease
      else return { object := some (address.capability,
        { object with live := false, bytes := fun _ => 0, shadow := fun _ => none }) }

def apply_heap_edit (state : HeapState) (edit : HeapEdit) : HeapState :=
  ⟨match edit.object with
    | none => state.objects
    | some (ident, object) => replace_object state.objects ident object,
   edit.counter.getD state.counter⟩

private theorem checked_object (state : HeapState) (address : Pointer) (width slot : Nat)
    (object : Object) (access : runtime_checked state.objects (some address) width = .ok (object, slot)) :
    state.objects address.capability = some object :=
  (checked_sound _ _ _ _ ((checked_refines _ _ _ _ _).mp access).1).1

theorem heap_effect_transition (state : HeapState) (operation : HeapEffect) (edit : HeapEdit)
    (counter_fits : state.counter.ident ≤ 9223372036854775807)
    (performed : heap_effect state operation = .ok edit) :
    HeapTransition state (apply_heap_edit state edit) ∧
      (apply_heap_edit state edit).counter.ident ≤ 9223372036854775807 := by
  cases operation with
  | allocate size heap =>
    cases allocation : plan_allocation state.counter false size 9223372036854775807 with
    | none => simp [heap_effect, allocation] at performed
    | some plan =>
      simp [heap_effect, allocation] at performed
      subst edit
      obtain ⟨_, _, _, _, _, _, _, _, _, _, fitted, _⟩ :=
        allocation_plan_sound _ _ _ _ plan counter_fits allocation
      exact ⟨.allocate heap counter_fits allocation, fitted⟩
  | allocateGlobal size =>
    cases allocation : plan_allocation state.counter true size 9223372036854775807 with
    | none => simp [heap_effect, allocation] at performed
    | some plan =>
      simp [heap_effect, allocation] at performed
      subst edit
      obtain ⟨_, _, _, _, _, _, _, _, _, _, fitted, _⟩ :=
        allocation_plan_sound _ _ _ _ plan counter_fits allocation
      exact ⟨.allocate false counter_fits allocation, fitted⟩
  | loadByte address =>
    cases access : runtime_checked state.objects (some address) 1 with
    | error why => simp [heap_effect, access, Except.mapError, bind, Except.bind] at performed
    | ok result =>
      obtain ⟨object, slot⟩ := result
      simp [heap_effect, access, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
      subst edit
      exact ⟨.observe, counter_fits⟩
  | storeByte address value =>
    cases access : runtime_checked state.objects (some address) 1 with
    | error why => simp [heap_effect, access, Except.mapError, bind, Except.bind] at performed
    | ok result =>
      obtain ⟨object, slot⟩ := result
      cases readonly : object.readonly
      · simp [heap_effect, access, readonly, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
        subst edit
        exact ⟨.replace (checked_object _ _ 1 _ _ access) rfl, counter_fits⟩
      · simp [heap_effect, access, readonly, Except.mapError, bind, Except.bind] at performed
  | loadWord address width =>
    cases access : runtime_checked state.objects (some address) width with
    | error why => simp [heap_effect, access, Except.mapError, bind, Except.bind] at performed
    | ok result =>
      obtain ⟨object, slot⟩ := result
      simp [heap_effect, access, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
      subst edit
      exact ⟨.observe, counter_fits⟩
  | storeWord address width value =>
    cases access : runtime_checked state.objects (some address) width with
    | error why => simp [heap_effect, access, Except.mapError, bind, Except.bind] at performed
    | ok result =>
      obtain ⟨object, slot⟩ := result
      cases readonly : object.readonly
      · simp [heap_effect, access, readonly, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
        subst edit
        exact ⟨.replace (checked_object _ _ _ _ _ access) rfl, counter_fits⟩
      · simp [heap_effect, access, readonly, Except.mapError, bind, Except.bind] at performed
  | storeBits address shift width value =>
    cases access : runtime_checked state.objects (some address) (bitfield_bytes shift width) with
    | error why => simp [heap_effect, access, Except.mapError, bind, Except.bind] at performed
    | ok result =>
      obtain ⟨object, slot⟩ := result
      cases readonly : object.readonly
      · simp [heap_effect, access, readonly, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
        subst edit
        exact ⟨.replace (checked_object _ _ _ _ _ access) rfl, counter_fits⟩
      · simp [heap_effect, access, readonly, Except.mapError, bind, Except.bind] at performed
  | loadPointer address =>
    cases access : runtime_checked state.objects (some address) 8 with
    | error why => simp [heap_effect, access, Except.mapError, bind, Except.bind] at performed
    | ok result =>
      obtain ⟨object, slot⟩ := result
      by_cases aligned : address.address % 8 = 0
      · simp [heap_effect, access, aligned, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
        subst edit
        exact ⟨.observe, counter_fits⟩
      · simp [heap_effect, access, aligned, Except.mapError, bind, Except.bind] at performed
  | storePointer address value =>
    cases access : runtime_checked state.objects (some address) 8 with
    | error why => simp [heap_effect, access, Except.mapError, bind, Except.bind] at performed
    | ok result =>
      obtain ⟨object, slot⟩ := result
      cases readonly : object.readonly
      · by_cases aligned : address.address % 8 = 0
        · simp [heap_effect, access, readonly, aligned, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
          subst edit
          exact ⟨.replace (checked_object _ _ 8 _ _ access) rfl, counter_fits⟩
        · simp [heap_effect, access, readonly, aligned, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
      · simp [heap_effect, access, readonly, Except.mapError, bind, Except.bind] at performed
  | clear address count =>
    cases access : runtime_checked state.objects (some address) count with
    | error why => simp [heap_effect, access, Except.mapError, bind, Except.bind] at performed
    | ok result =>
      obtain ⟨object, slot⟩ := result
      cases readonly : object.readonly
      · simp [heap_effect, access, readonly, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
        subst edit
        exact ⟨.replace (checked_object _ _ _ _ _ access) rfl, counter_fits⟩
      · simp [heap_effect, access, readonly, Except.mapError, bind, Except.bind] at performed
  | copyAggregate source destination count =>
    cases read : runtime_checked state.objects (some source) count with
    | error why => simp [heap_effect, read, Except.mapError, bind, Except.bind] at performed
    | ok input =>
      obtain ⟨fromObject, fromOffset⟩ := input
      cases write : runtime_checked state.objects (some destination) count with
      | error why => simp [heap_effect, read, write, Except.mapError, bind, Except.bind] at performed
      | ok output =>
        obtain ⟨toObject, toOffset⟩ := output
        cases readonly : toObject.readonly
        · cases alignment : aggregate_unaligned destination count (read_aggregate (object_planes fromObject) fromOffset count)
          · simp [heap_effect, read, write, readonly, alignment, Except.mapError, bind, Except.bind,
              pure, Except.pure] at performed
            subst edit
            exact ⟨.replace (checked_object _ _ _ _ _ write) rfl, counter_fits⟩
          · simp [heap_effect, read, write, readonly, alignment, Except.mapError, bind, Except.bind,
              pure, Except.pure] at performed
        · simp [heap_effect, read, write, readonly, Except.mapError, bind, Except.bind] at performed
  | copy source destination count =>
    cases access : runtime_copy_offsets state.objects source destination count with
    | error why => simp [heap_effect, access, Except.mapError, bind, Except.bind] at performed
    | ok offsets =>
      cases offsets with
      | none =>
        simp [heap_effect, access, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
        subst edit
        exact ⟨.observe, counter_fits⟩
      | some offsets =>
        obtain ⟨s, d⟩ := offsets
        obtain ⟨src, dst, read, write, _, _, _, _, _⟩ :=
          copy_offsets_sound state.objects source destination count s d access
        simp [heap_effect, access, read, write, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
        subst edit
        exact ⟨.replace write rfl, counter_fits⟩
  | release address =>
    let isNull := address.capability == 0 && address.address == 0
    cases null : isNull
    · have nonnull : (address.capability == 0 && address.address == 0) = false := null
      cases access : runtime_checked state.objects (some address) 0 with
      | error why => simp [heap_effect, nonnull, access, Except.mapError, bind, Except.bind] at performed
      | ok result =>
        obtain ⟨object, slot⟩ := result
        cases heap : object.heap
        · simp [heap_effect, nonnull, access, heap, Except.mapError, bind, Except.bind] at performed
        by_cases base : slot = 0
        · simp [heap_effect, nonnull, access, heap, base, Except.mapError, bind, Except.bind, pure, Except.pure] at performed
          subst edit
          have found := checked_object _ _ 0 _ _ access
          have equal : invalidate state.objects address.capability =
              replace_object state.objects address.capability
                { object with live := false, bytes := fun _ => 0, shadow := fun _ => none } := by
            funext ident
            by_cases same : ident = address.capability
            · simp [invalidate, replace_object, same, found]
            · simp [invalidate, replace_object, same]
          refine ⟨?_, counter_fits⟩
          simpa [apply_heap_edit, equal, heap] using (HeapTransition.release (state := state) found)
        · simp [heap_effect, nonnull, access, heap, base, Except.mapError, bind, Except.bind] at performed
    · have is_null : (address.capability == 0 && address.address == 0) = true := null
      simp [heap_effect, is_null] at performed
      subst edit
      exact ⟨.observe, counter_fits⟩

theorem nonheap_release_rejected (state : HeapState) (address : Pointer) (object : Object) (slot : Nat)
    (access : runtime_checked state.objects (some address) 0 = .ok (object, slot))
    (nonheap : object.heap = false) (allocated : address.capability ≠ 0) :
    heap_effect state (.release address) = .error .nonHeapRelease := by
  simp [heap_effect, allocated, access, nonheap, Except.mapError, bind, Except.bind]

theorem release_null_noop (state : HeapState) : heap_effect state (.release ⟨0, 0⟩) = .ok {} := rfl

theorem scalar_slot_refines (state : HeapState) (address : Pointer) (width slot : Nat) (value : Int)
    (before : Object) (access : runtime_checked state.objects (some address) width = .ok (before, slot))
    (writable : before.readonly = false) :
    let written := integer_store before slot width value
    let edit : HeapEdit := { object := some (address.capability, written) }
    heap_effect state (.storeWord address width value) = .ok edit ∧
      heap_effect (apply_heap_edit state edit) (.loadWord address width) =
        .ok { reply := .word (unsigned (8 * width) value) } := by
  dsimp only
  constructor
  · simp [heap_effect, access, writable, Except.mapError, bind, Except.bind, pure, Except.pure]
  · obtain ⟨checkedBefore, displacement⟩ := (checked_refines state.objects address width slot before).mp access
    have span := (checked_sound state.objects address width before checkedBefore).2
    let written := integer_store before slot width value
    let edit : HeapEdit := { object := some (address.capability, written) }
    let after := apply_heap_edit state edit
    have sameSpan : accessible written address.address width := span
    have checkedAfter : checked after.objects address width = some written := by
      change checked (replace_object state.objects address.capability written) address width = some written
      simp [checked, replace_object, sameSpan]
    have readBack : runtime_checked after.objects (some address) width = .ok (written, slot) :=
      (checked_refines after.objects address width slot written).mpr ⟨checkedAfter, displacement⟩
    change heap_effect after (.loadWord address width) = _
    simp only [heap_effect, readBack, Except.mapError, bind, Except.bind, pure, Except.pure,
      integer_store_load_roundtrip, written]

structure HeapImage where
  cells : List (Nat × Object)
  counter : AllocationCounter

def HeapImage.snapshot (image : HeapImage) (reference : Nat → Nat := id) : HeapState :=
  ⟨fun key => List.lookup (reference key) image.cells, image.counter⟩

def HeapImage.apply (image : HeapImage) (edit : HeapEdit) (reference : Nat → Nat := id) : HeapImage :=
  ⟨match edit.object with
    | none => image.cells
    | some (ident, object) =>
      (reference ident, object) :: image.cells.filter (fun cell => cell.1 != reference ident),
   edit.counter.getD image.counter⟩

private theorem lookup_filter_other (cells : List (Nat × Object)) (removed key : Nat)
    (different : key ≠ removed) :
    (cells.filter (fun cell => cell.1 != removed)).lookup key = cells.lookup key := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    obtain ⟨ident, object⟩ := cell
    by_cases same : ident = removed
    · subst ident
      simp [List.lookup_cons, beq_eq_false_iff_ne.mpr different, ih]
    · simp [List.lookup_cons, same, ih]

theorem heap_image_edit (image : HeapImage) (edit : HeapEdit) (reference : Nat → Nat)
    (distinct : Function.Injective reference) :
    (image.apply edit reference).snapshot reference = apply_heap_edit (image.snapshot reference) edit := by
  cases edit with
  | mk reply object counter =>
    cases object with
    | none => rfl
    | some write =>
      obtain ⟨ident, object⟩ := write
      unfold HeapImage.apply HeapImage.snapshot apply_heap_edit
      dsimp only
      congr 1
      funext key
      by_cases same : key = ident
      · simp [same, replace_object]
      · have separate : reference key ≠ reference ident := fun equal => same (distinct equal)
        simp [List.lookup_cons, replace_object, same, beq_eq_false_iff_ne.mpr separate,
          lookup_filter_other _ _ _ separate]

inductive TraceProgram where
  | finish (status : Int)
  | fail (reason : HeapFault)
  | jump (block : Nat)
  | tick (next : TraceProgram)
  | output (bytes : List UInt8) (next : TraceProgram)
  | effect (operation : HeapEffect) (next : HeapReply → TraceProgram)

inductive TraceOutcome where
  | paused
  | returned (status : Int)
  | fault (reason : HeapFault)
  deriving DecidableEq

structure TraceMachine (heap buffer : Type) where
  heap_view : heap → HeapState
  edit : heap → HeapEdit → heap
  output_view : buffer → StdoutState
  output : Bool → buffer → List UInt8 → buffer

structure TraceResult (heap buffer : Type) where
  outcome : TraceOutcome
  heap : heap
  stdout : buffer

def run_trace (machine : TraceMachine heap buffer) (terminal : Bool)
    (blocks : Nat → Option TraceProgram) :
    Nat → TraceProgram → heap → buffer → TraceResult heap buffer
  | 0, _, memory, stdout => ⟨.paused, memory, stdout⟩
  | _ + 1, .finish status, memory, stdout => ⟨.returned (unsigned 8 status), memory, stdout⟩
  | _ + 1, .fail reason, memory, stdout => ⟨.fault reason, memory, stdout⟩
  | fuel + 1, .jump slot, memory, stdout =>
    match blocks slot with
    | none => ⟨.fault .missingBlock, memory, stdout⟩
    | some next => run_trace machine terminal blocks fuel next memory stdout
  | fuel + 1, .tick next, memory, stdout => run_trace machine terminal blocks fuel next memory stdout
  | fuel + 1, .output bytes next, memory, stdout =>
    run_trace machine terminal blocks fuel next memory (machine.output terminal stdout bytes)
  | fuel + 1, .effect operation next, memory, stdout =>
    match heap_effect (machine.heap_view memory) operation with
    | .error why => ⟨.fault why, memory, stdout⟩
    | .ok edit => run_trace machine terminal blocks fuel (next edit.reply) (machine.edit memory edit) stdout

theorem run_trace_completed (machine : TraceMachine heap buffer) (terminal : Bool)
    (blocks : Nat → Option TraceProgram) (fuel larger : Nat) (program : TraceProgram) (memory : heap) (stdout : buffer)
    (enough : fuel ≤ larger) (completed : (run_trace machine terminal blocks fuel program memory stdout).outcome ≠ .paused) :
    run_trace machine terminal blocks larger program memory stdout = run_trace machine terminal blocks fuel program memory stdout := by
  induction fuel generalizing larger program memory stdout with
  | zero => exact (completed rfl).elim
  | succ fuel ih =>
    cases larger with
    | zero => omega
    | succ larger =>
      have within : fuel ≤ larger := Nat.le_of_succ_le_succ enough
      cases program with
      | finish | fail => rfl
      | tick next => exact ih larger next memory stdout within completed
      | output bytes next => exact ih larger next memory (machine.output terminal stdout bytes) within completed
      | jump slot =>
        cases dest : blocks slot with
        | none => simp [run_trace, dest]
        | some next =>
          simp only [run_trace, dest] at completed ⊢
          exact ih larger next memory stdout within completed
      | effect operation next =>
        cases applied : heap_effect (machine.heap_view memory) operation with
        | error reason => simp [run_trace, applied]
        | ok edit =>
          simp only [run_trace, applied] at completed ⊢
          exact ih larger (next edit.reply) (machine.edit memory edit) stdout within completed

def abstract_machine : TraceMachine HeapState StdoutState :=
  ⟨id, apply_heap_edit, id, stdout_write⟩

def sparse_machine (reference : Nat → Nat := id) : TraceMachine HeapImage StdoutBuffer :=
  ⟨(·.snapshot reference), (·.apply · reference), StdoutBuffer.snapshot, stdout_buffer_write⟩

def TraceResult.snapshot (result : TraceResult HeapImage StdoutBuffer) (reference : Nat → Nat := id) :
    TraceResult HeapState StdoutState :=
  ⟨result.outcome, result.heap.snapshot reference, result.stdout.snapshot⟩

theorem trace_machine_refines (terminal : Bool) (blocks : Nat → Option TraceProgram)
    (fuel : Nat) (program : TraceProgram) (memory : HeapImage) (stdout : StdoutBuffer)
    (valid : stdout.size = stdout.snapshot.pending.length) (reference : Nat → Nat)
    (distinct : Function.Injective reference) :
    (run_trace (sparse_machine reference) terminal blocks fuel program memory stdout).snapshot reference =
      run_trace abstract_machine terminal blocks fuel program (memory.snapshot reference) stdout.snapshot := by
  induction fuel generalizing program memory stdout with
  | zero => rfl
  | succ fuel ih =>
    cases program with
    | finish _ | fail _ => rfl
    | jump slot =>
      cases found : blocks slot with
      | none => simp [run_trace, found, TraceResult.snapshot]
      | some next => simpa [run_trace, found] using (ih next memory stdout valid)
    | tick next => exact ih next memory stdout valid
    | output bytes next =>
      obtain ⟨view, next_valid⟩ := stdout_write_correct terminal stdout bytes valid
      simpa only [run_trace, sparse_machine, abstract_machine, view] using
        (ih next memory (stdout_buffer_write terminal stdout bytes) next_valid)
    | effect operation next =>
      cases observed : heap_effect (memory.snapshot reference) operation with
      | error fault => simp [run_trace, sparse_machine, abstract_machine, observed, TraceResult.snapshot]
      | ok edit =>
        simpa only [run_trace, sparse_machine, abstract_machine, id_eq, observed, heap_image_edit _ _ _ distinct] using
          (ih (next edit.reply) (memory.apply edit reference) stdout valid)

theorem trace_heap_preserves_allocations (terminal : Bool) (blocks : Nat → Option TraceProgram)
    (fuel : Nat) (program : TraceProgram) (heap : HeapState) (stdout : StdoutState)
    (counter_fits : heap.counter.ident ≤ 9223372036854775807) :
    HeapTrace heap (run_trace abstract_machine terminal blocks fuel program heap stdout).heap := by
  induction fuel generalizing program heap stdout with
  | zero => exact .start
  | succ fuel ih =>
    cases program with
    | finish _ | fail _ => exact .start
    | jump slot =>
      cases found : blocks slot with
      | none => simpa [run_trace, found] using (HeapTrace.start (state := heap))
      | some next => simpa [run_trace, found] using ih next heap stdout counter_fits
    | tick next => exact ih next heap stdout counter_fits
    | output bytes next =>
      exact ih next heap (stdout_write terminal stdout bytes) counter_fits
    | effect operation next =>
      cases performed : heap_effect heap operation with
      | error why => simpa [run_trace, abstract_machine, performed] using (HeapTrace.start (state := heap))
      | ok edit =>
        have ⟨step, fitted⟩ := heap_effect_transition _ _ _ counter_fits performed
        have execution := ih (next edit.reply) (apply_heap_edit heap edit) stdout fitted
        exact (by
          simpa [run_trace, abstract_machine, performed] using heap_trace_prepend step execution)

theorem trace_reserves_null (terminal : Bool) (blocks : Nat → Option TraceProgram)
    (fuel : Nat) (program : TraceProgram) (heap : HeapState) (stdout : StdoutState)
    (counter_fits : heap.counter.ident ≤ 9223372036854775807) (reserved : heap.null_reserved) :
    (run_trace abstract_machine terminal blocks fuel program heap stdout).heap.null_reserved :=
  heap_trace_reserves_null _ _ (trace_heap_preserves_allocations terminal blocks fuel program heap stdout counter_fits) reserved

theorem trace_visible_extends (terminal : Bool) (blocks : Nat → Option TraceProgram)
    (fuel : Nat) (program : TraceProgram) (heap : HeapState) (stdout : StdoutState) :
    stdout.visible <+: (run_trace abstract_machine terminal blocks fuel program heap stdout).stdout.visible := by
  induction fuel generalizing program heap stdout with
  | zero => exact ⟨[], List.append_nil _⟩
  | succ fuel ih =>
    cases program with
    | finish _ | fail _ => exact ⟨[], List.append_nil _⟩
    | jump slot =>
      cases found : blocks slot with
      | none =>
        simp only [run_trace, found]
        exact ⟨[], List.append_nil _⟩
      | some next => simpa [run_trace, found] using ih next heap stdout
    | tick next => exact ih next heap stdout
    | output bytes next =>
      obtain ⟨emitted, same⟩ := stdout_visible_extends terminal stdout [bytes]
      have earlier : stdout.visible <+: (stdout_write terminal stdout bytes).visible :=
        ⟨emitted, same.symm⟩
      exact earlier.trans (ih next heap (stdout_write terminal stdout bytes))
    | effect operation next =>
      cases performed : heap_effect heap operation with
      | error why =>
        simp only [run_trace, abstract_machine, id_eq, performed]
        exact ⟨[], List.append_nil _⟩
      | ok edit =>
        simpa only [run_trace, abstract_machine, id_eq, performed] using
          ih (next edit.reply) (apply_heap_edit heap edit) stdout

theorem trace_visible_monotone (terminal : Bool) (blocks : Nat → Option TraceProgram)
    (fuel more : Nat) (program : TraceProgram) (heap : HeapState) (stdout : StdoutState) :
    (run_trace abstract_machine terminal blocks fuel program heap stdout).stdout.visible <+:
      (run_trace abstract_machine terminal blocks (fuel + more) program heap stdout).stdout.visible := by
  induction fuel generalizing program heap stdout with
  | zero => simpa [run_trace] using trace_visible_extends terminal blocks more program heap stdout
  | succ fuel ih =>
    cases program with
    | finish _ | fail _ => simp [Nat.succ_add, run_trace]
    | jump slot =>
      cases found : blocks slot with
      | none => simp [Nat.succ_add, run_trace, found]
      | some next => simpa [Nat.succ_add, run_trace, found] using ih next heap stdout
    | tick next => simpa only [Nat.succ_add, run_trace] using ih next heap stdout
    | output bytes next =>
      simpa only [Nat.succ_add, run_trace, abstract_machine] using
        ih next heap (stdout_write terminal stdout bytes)
    | effect operation next =>
      cases performed : heap_effect heap operation with
      | error why => simp [Nat.succ_add, run_trace, abstract_machine, performed]
      | ok edit =>
        simpa only [Nat.succ_add, run_trace, abstract_machine, id_eq, performed] using
          ih (next edit.reply) (apply_heap_edit heap edit) stdout

def TraceResult.observation (result : TraceResult HeapState StdoutState) :
    TraceOutcome × List UInt8 :=
  (result.outcome, match result.outcome with
    | .returned _ => result.stdout.visible ++ result.stdout.pending
    | .paused | .fault _ => result.stdout.visible)

theorem trace_observations_refine (terminal : Bool) (blocks : Nat → Option TraceProgram)
    (fuel : Nat) (program : TraceProgram) (memory : HeapImage) (stdout : StdoutBuffer)
    (valid : stdout.size = stdout.snapshot.pending.length) (reference : Nat → Nat)
    (distinct : Function.Injective reference) :
    ((run_trace (sparse_machine reference) terminal blocks fuel program memory stdout).snapshot reference).observation =
      (run_trace abstract_machine terminal blocks fuel program (memory.snapshot reference) stdout.snapshot).observation :=
  congrArg TraceResult.observation (trace_machine_refines terminal blocks fuel program memory stdout valid reference distinct)

private def with_pointer (operation : HeapEffect) (next : Pointer → TraceProgram) : TraceProgram :=
  .effect operation fun
    | .pointer pointer => next pointer
    | _ => .jump 0

def copied_alias_program (payload : UInt8) : TraceProgram :=
  with_pointer (.allocate 24) fun buffer =>
  with_pointer (.allocate 1) fun allocation =>
  .effect (.storeByte allocation payload) fun _ =>
  .effect (.storePointer (offset_pointer buffer 8) allocation) fun _ =>
  .effect (.copy (offset_pointer buffer 8) buffer 16) fun _ =>
  with_pointer (.loadPointer buffer) fun alias =>
  .effect (.loadByte alias) fun
    | .byte value => .output [value] (.output [10] (
        .effect (.release allocation) fun _ => .effect (.loadByte alias) fun _ => .finish 0))
    | _ => .jump 0

def copied_alias_run (payload : UInt8) : TraceResult HeapImage StdoutBuffer :=
  run_trace sparse_machine false (fun _ => none) 12 (copied_alias_program payload) ⟨[], ⟨1, 4096⟩⟩
    ⟨[], [], 0, true⟩

theorem copied_alias_observation :
    (copied_alias_run 65).snapshot.observation = (.fault (.access .dead), [65, 10]) := by
  rfl

theorem copied_alias_carries_word :
    read_data_pointer_word (copied_alias_run 65).heap.snapshot.objects ⟨1, 4096⟩ =
      .ok (some 2, 4144) := by
  rfl

theorem copied_alias_uses_overlapping_snapshot :
    let source : Pointer := ⟨1, 4104⟩
    let destination : Pointer := ⟨1, 4096⟩
    let state := (copied_alias_run 65).heap.snapshot
    source.capability = destination.capability ∧
      destination.address < source.address + 16 ∧ source.address < destination.address + 16 ∧
      runtime_copy_offsets state.objects source destination 16 = .ok (some (8, 0)) ∧
      (read_data_pointer_word state.objects destination = .ok (some 2, 4144)) := by
  exact ⟨rfl, by decide, by decide, rfl, rfl⟩

def emitting_loop : Nat → Option TraceProgram
  | 0 => some (.output [65, 10] (.jump 0))
  | _ + 1 => none

theorem emitting_loop_prefix (fuel : Nat) :
    (run_trace abstract_machine true emitting_loop (2 * fuel) (.jump 0)
      ⟨fun _ => none, ⟨1, 4096⟩⟩ ⟨[], [], true⟩).observation =
      (.paused, (List.replicate fuel [65, 10]).flatten) := by
  have progress (fuel : Nat) (visible : List UInt8) :
      (run_trace abstract_machine true emitting_loop (2 * fuel) (.jump 0)
        ⟨fun _ => none, ⟨1, 4096⟩⟩ ⟨visible, [], true⟩).observation =
        (.paused, visible ++ (List.replicate fuel [65, 10]).flatten) := by
    induction fuel generalizing visible with
    | zero => simp [run_trace, TraceResult.observation]
    | succ fuel ih =>
      have steps : 2 * (fuel + 1) = 2 * fuel + 1 + 1 := by omega
      rw [steps]
      simp only [run_trace, emitting_loop]
      have emitted : stdout_write true ⟨visible, [], true⟩ [65, 10] =
          ⟨visible ++ [65, 10], [], true⟩ := by
        unfold stdout_write
        change StdoutState.mk (visible ++ [] ++ [65, 10]) [] true = _
        simp
      rw [show abstract_machine.output = stdout_write from rfl, emitted]
      change (run_trace abstract_machine true emitting_loop (2 * fuel) (.jump 0)
        ⟨fun _ => none, ⟨1, 4096⟩⟩ ⟨visible ++ [65, 10], [], true⟩).observation = _
      simp [ih, List.replicate_succ, List.append_assoc]
  simpa using progress fuel []

abbrev BoundExpression (state fault : Type) := state → Except fault Int × state

def evaluate_bounds : List (BoundExpression state fault) → state → Except fault (List Int) × state
  | [], initial => (.ok [], initial)
  | expression :: rest, initial =>
    match expression initial with
    | (.error why, after) => (.error why, after)
    | (.ok size, after) =>
      let (dimensions, final) := evaluate_bounds rest after
      (dimensions.map (size :: ·), final)

inductive BoundsEvaluated : List (BoundExpression state fault) → state →
    List Int → state → Prop where
  | empty : BoundsEvaluated [] initial [] initial
  | next : expression initial = (.ok size, after) →
      BoundsEvaluated rest after dimensions final →
      BoundsEvaluated (expression :: rest) initial (size :: dimensions) final

theorem evaluate_bounds_correct (expressions : List (BoundExpression state fault)) (initial final : state)
    (dimensions : List Int) :
    evaluate_bounds expressions initial = (.ok dimensions, final) ↔
      BoundsEvaluated expressions initial dimensions final := by
  constructor
  · intro evaluated
    induction expressions generalizing initial final dimensions with
    | nil =>
      simp [evaluate_bounds] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact .empty
    | cons first rest ih =>
      cases effect : first initial with
      | mk result after =>
        cases result with
        | error why => simp [evaluate_bounds, effect] at evaluated
        | ok size =>
          cases tail : evaluate_bounds rest after with
          | mk tail_result stopped =>
            cases tail_result with
            | error why => simp [evaluate_bounds, effect, tail, Except.map] at evaluated
            | ok sizes =>
              simp [evaluate_bounds, effect, tail, Except.map] at evaluated
              obtain ⟨rfl, rfl⟩ := evaluated
              exact .next effect (ih _ _ _ tail)
  · intro evaluated
    induction evaluated with
    | empty => rfl
    | next read _ remaining => simp [evaluate_bounds, read, remaining, Except.map]

def capture_shape (width : Nat) (expressions : List (BoundExpression state fault)) (initial : state) :
    Option (List Nat) × state :=
  let (result, final) := evaluate_bounds expressions initial
  match result with
  | .error _ => (none, final)
  | .ok dimensions =>
    if dimensions.all (· > 0) then
      (some (array_spans width (dimensions.map Int.toNat)), final)
    else (none, final)

theorem captured_shape_correct (width : Nat) (expressions : List (BoundExpression state fault))
    (before after : state) (spans : List Nat) (captured : capture_shape width expressions before = (some spans, after)) :
    ∃ dimensions, BoundsEvaluated expressions before dimensions after ∧
      (∀ dimension ∈ dimensions, 0 < dimension) ∧
      ∀ rank, rank ≤ dimensions.length →
        spans[rank]? = some (array_extent width ((dimensions.map Int.toNat).drop rank)) := by
  cases evaluated : evaluate_bounds expressions before with
  | mk result final =>
    cases result with
    | error why => simp [capture_shape, evaluated] at captured
    | ok dimensions =>
      by_cases positive : ∀ dimension ∈ dimensions, 0 < dimension
      · have all : dimensions.all (· > 0) = true := by simpa using positive
        simp only [capture_shape, evaluated, all, if_true, Prod.mk.injEq, Option.some.injEq] at captured
        obtain ⟨rfl, rfl⟩ := captured
        exact ⟨dimensions, (evaluate_bounds_correct _ _ _ _).mp evaluated, positive, fun rank within =>
          array_span_at _ _ rank (by simpa using within)⟩
      · have all : dimensions.all (· > 0) = false := by
          apply Bool.eq_false_iff.mpr
          simpa using positive
        simp [capture_shape, evaluated, all] at captured

end Heresy

#print axioms Heresy.trace_machine_refines
#print axioms Heresy.copied_alias_observation
#print axioms Heresy.emitting_loop_prefix

#print axioms Heresy.captured_shape_correct
#print axioms Heresy.trace_heap_preserves_allocations
#print axioms Heresy.trace_visible_monotone
#print axioms Heresy.copied_alias_carries_word
#print axioms Heresy.copied_alias_uses_overlapping_snapshot
#print axioms Heresy.scalar_slot_refines
