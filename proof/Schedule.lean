import Ordinary
import Synchronisation

set_option warningAsError true

namespace Heresy

inductive ThreadCode (α : Type) where
  | idle
  | synchronise (op : SyncOp) (object other : Pointer) (next : Nat → ThreadCode α)
  | exit (status : Int)
  | fault (reason : HeapFault)
  | jump (block : Nat)
  | tick (next : ThreadCode α)
  | output (bytes : List (List UInt8)) (next : ThreadCode α)
  | effect (operation : HeapEffect) (next : HeapReply → ThreadCode α)
  | spawn (worker : ThreadCode α) (next : Nat → ThreadCode α) (handle : Option Pointer := none)
  | bindSelf (handle : Pointer) (next : ThreadCode α)
  | getSelf (next : Option Pointer → ThreadCode α)
  | resolve (handle : Pointer) (next : Option Nat → ThreadCode α)
  | finish (value : α)
  | join (child : Nat) (next : Except Nat α → ThreadCode α)
  | await (child : Nat) (next : Except Nat α → ThreadCode α)

def ThreadCode.fromTrace : TraceProgram → ThreadCode α
  | .finish status => .exit status
  | .fail reason => .fault reason
  | .jump block => .jump block
  | .tick next => .tick (fromTrace next)
  | .output bytes next => .output bytes (fromTrace next)
  | .effect operation next => .effect operation (fun reply => fromTrace (next reply))

inductive SyncCell where
  | mutex (queue : MutexQueue)
  | condition (waiting : List Nat)
  | destroyed

inductive WaitPhase where
  | lock | condition | granted | notified
  deriving BEq

structure SyncTable where
  cells : List ((Nat × Nat) × SyncCell) := []
  waiters : List (Nat × WaitPhase) := []

private def SyncTable.cell (table : SyncTable) (key : Nat × Nat) (cell : SyncCell) : SyncTable :=
  { table with cells := (key, cell) :: table.cells.filter (fun entry => entry.1 != key) }

private def SyncTable.wake (table : SyncTable) (thread : Nat) (phase : WaitPhase) : SyncTable :=
  { table with waiters := (thread, phase) :: table.waiters.filter (fun entry => entry.1 != thread) }

private def sync_key (heap : HeapState) (ptr : Pointer) (width : Nat) : Except HeapFault (Nat × Nat) := do
  let (object, slot) ← (runtime_checked heap.objects (some ptr) width).mapError .access
  if ptr.address % 8 != 0 then throw .unaligned
  if object.readonly then throw .readonly
  return (ptr.capability, slot)

private abbrev SyncResult := Except HeapFault (SyncTable × Option Nat)

private def acquire_mutex (heap : HeapState) (table : SyncTable) (thread : Nat) (ptr : Pointer) (tryOnly : Bool) :
    SyncResult := do
  let key ← sync_key heap ptr 32
  let .mutex queue := (table.cells.lookup key).getD (.mutex ⟨none, []⟩) | return (table, some 22)
  let (updated, result) := mutex_acquire tryOnly thread thread queue
  let table := table.cell key (.mutex updated)
  match result with
  | .complete status => return (table, some status)
  | .wait _ => return (table.wake thread .lock, none)

private def release_mutex (heap : HeapState) (table : SyncTable) (thread : Nat) (ptr : Pointer) :
    Except HeapFault (SyncTable × Nat) := do
  let key ← sync_key heap ptr 32
  let .mutex queue := (table.cells.lookup key).getD (.mutex ⟨none, []⟩) | return (table, 22)
  let some (updated, ticket) := mutex_release thread queue | return (table.cell key (.mutex queue), 1)
  let table := table.cell key (.mutex updated)
  return (ticket.elim table (fun next => table.wake next .granted), 0)

private def sync_step (heap : HeapState) (table : SyncTable) (thread : Nat) (op : SyncOp)
    (ptr other : Pointer) : SyncResult := do
  match table.waiters.lookup thread with
  | some .lock | some .condition => return (table, none)
  | some phase =>
    let cleared := { table with waiters := table.waiters.filter (fun entry => entry.1 != thread) }
    if phase == .granted then return (cleared, some 0)
    return ← acquire_mutex heap cleared thread other false
  | none => pure ()
  let empty := if op.isMutex then SyncCell.mutex ⟨none, []⟩ else SyncCell.condition []
  match op with
  | .lock | .trylock => acquire_mutex heap table thread ptr (op == .trylock)
  | .unlock =>
    let (table, status) ← release_mutex heap table thread ptr
    return (table, some status)
  | .mutexInit | .condInit =>
    if other.address != 0 then throw .syncAttributes
    let key ← sync_key heap ptr op.width
    return (table.cell key empty, some 0)
  | .mutexDestroy | .condDestroy =>
    let key ← sync_key heap ptr op.width
    let cell := (table.cells.lookup key).getD empty
    match cell with
    | .destroyed => return (table, some 22)
    | .mutex ⟨none, []⟩ | .condition [] => return (table.cell key .destroyed, some 0)
    | _ => return (table, some 16)
  | .wait =>
    if ptr.address == other.address then return (table, some 22)
    let key ← sync_key heap ptr 48
    let .condition waiting := (table.cells.lookup key).getD empty | return (table, some 22)
    let (released, status) ← release_mutex heap table thread other
    if status != 0 then return (released.cell key (.condition waiting), some status)
    return ((released.cell key (.condition (waiting ++ [thread]))).wake thread .condition, none)
  | .signal | .broadcast =>
    let key ← sync_key heap ptr 48
    let .condition waiting := (table.cells.lookup key).getD empty | return (table, some 22)
    let (chosen, remaining) := choose_signals (op == .broadcast) waiting
    let updated := table.cell key (.condition remaining)
    return (chosen.foldl (fun t waiter => t.wake waiter .notified) updated, some 0)

theorem blocked_condition_requires_notification (heap : HeapState) (table : SyncTable) (thread : Nat)
    (condition mutex : Pointer) (blocked : table.waiters.lookup thread = some .condition) :
    sync_step heap table thread .wait condition mutex = .ok (table, none) := by
  rw [sync_step, blocked]
  rfl

theorem notified_condition_reacquires_mutex (heap : HeapState) (table : SyncTable) (thread : Nat)
    (condition mutex : Pointer) (notified : table.waiters.lookup thread = some .notified) :
    sync_step heap table thread .wait condition mutex =
      acquire_mutex heap { table with waiters := table.waiters.filter (fun entry => entry.1 != thread) }
        thread mutex false := by
  rw [sync_step, notified]
  let cleared := { table with waiters := table.waiters.filter (fun entry => entry.1 != thread) }
  change (acquire_mutex heap cleared thread mutex false >>= pure) = acquire_mutex heap cleared thread mutex false
  cases acquire_mutex heap cleared thread mutex false <;> rfl

@[ext] structure ScheduleState (α heap buffer : Type) where
  memory : heap
  stdout : buffer
  jobs : Nat → ThreadCode α
  frames : Nat → ArrayFrames := fun _ => []
  joins : Nat → Option (JoinState α) := fun _ => none
  nextThread : Nat := 1
  outcome : TraceOutcome := .paused
  handles : List (Nat × Pointer) := []
  owner : Option Nat := none
  sync : SyncTable := {}

def ScheduleState.start (memory : heap) (stdout : buffer) (main : ThreadCode α) : ScheduleState α heap buffer :=
  ⟨memory, stdout, fun thread => if thread = 0 then main else .idle, fun _ => [], fun _ => none, 1, .paused, [], none, {}⟩

private def ScheduleState.resume (state : ScheduleState α heap buffer) (thread : Nat) (next : ThreadCode α) :
    ScheduleState α heap buffer :=
  { state with jobs := update_sync_cell state.jobs thread next }

private def ScheduleState.record (state : ScheduleState α heap buffer) (thread : Nat) (entry : JoinState α) :
    ScheduleState α heap buffer :=
  { state with joins := update_sync_cell state.joins thread (some entry) }

private def HeapEffect.lockOwner (thread : Nat) (current : Option Nat) : HeapEffect → Option Nat
  | .critical true => some thread
  | .critical false => none
  | _ => current

def ScheduleState.runnable (state : ScheduleState α heap buffer) (thread : Nat) : Bool :=
  state.owner.all (· == thread)

def schedule_step (machine : TraceMachine heap buffer) (terminal : Bool) (blocks : Nat → Option (ThreadCode α))
    (thread : Nat) (state : ScheduleState α heap buffer) : ScheduleState α heap buffer :=
  if state.outcome ≠ .paused ∨ state.runnable thread = false then state else
    match state.jobs thread with
    | .idle => state
    | .synchronise op ptr other next =>
      match sync_step (machine.heap_view state.memory) state.sync thread op ptr other with
      | .error reason => { state with outcome := .fault reason }
      | .ok (updated, none) => { state with sync := updated }
      | .ok (updated, some status) => { state.resume thread (next status) with sync := updated }
    | .exit status => { state with outcome := .returned (unsigned 8 status) }
    | .fault reason => { state with outcome := .fault reason }
    | .jump block =>
      match blocks block with
      | some next => state.resume thread next
      | none => { state with outcome := .fault .missingBlock }
    | .tick next => state.resume thread next
    | .output bytes next =>
      { state.resume thread next with stdout := bytes.foldl (machine.output terminal) state.stdout }
    | .effect operation next =>
      let localHeap := { machine.heap_view state.memory with arrayFrames := state.frames thread }
      match heap_effect localHeap operation with
      | .error reason => { state with outcome := .fault reason }
      | .ok edit =>
        { state.resume thread (next edit.reply) with
          owner := operation.lockOwner thread state.owner
          memory := machine.edit state.memory { edit with arrayFrames := none }
          frames := update_sync_cell state.frames thread (edit.arrayFrames.getD (state.frames thread)) }
    | .bindSelf handle next =>
      { state.resume thread next with handles := (thread, handle) :: state.handles }
    | .getSelf next => state.resume thread (next (state.handles.lookup thread))
    | .resolve handle next =>
      let found := state.handles.find? fun (_, ptr) => ptr.capability == handle.capability && ptr.address == handle.address
      state.resume thread (next (found.map Prod.fst))
    | .spawn worker next handle =>
      let child := state.nextThread
      let parent := (state.resume thread (next child)).resume child worker
      { parent.record child .published with
        handles := handle.elim state.handles (fun ptr => (child, ptr) :: state.handles)
        nextThread := child + 1
        frames := update_sync_cell state.frames child [] }
    | .finish value =>
      match state.joins thread with
      | some entry =>
        if entry.result.isSome then state else
          (state.resume thread .idle).record thread { entry with result := some value }
      | none => state
    | .join child next =>
      if child = thread then state.resume thread (next (.error 35)) else
        match state.joins child with
        | none => state.resume thread (next (.error 3))
        | some entry =>
          if entry.claimant.isSome then state.resume thread (next (.error 3)) else
            (state.resume thread (.await child next)).record child { entry with claimant := some thread }
    | .await child next =>
      match state.joins child with
      | some entry =>
        if entry.claimant = some thread ∧ entry.received.isNone = true then
          match entry.result with
          | none => state
          | some value =>
            (state.resume thread (next (.ok value))).record child { entry with received := some (thread, value) }
        else state.resume thread (next (.error 3))
      | none => state.resume thread (next (.error 3))

theorem exclusive_step (machine : TraceMachine heap buffer) (terminal : Bool)
    (blocks : Nat → Option (ThreadCode α)) (state : ScheduleState α heap buffer)
    (locked : state.owner = some owner) (other : owner ≠ thread) :
    schedule_step machine terminal blocks thread state = state := by
  simp [schedule_step, ScheduleState.runnable, locked, other]

theorem self_join_returns_deadlock (machine : TraceMachine heap buffer) (terminal : Bool)
    (blocks : Nat → Option (ThreadCode α)) (state : ScheduleState α heap buffer)
    (running : state.outcome = .paused) (runnable : state.runnable thread = true) (waiting : state.jobs thread = .join thread next) :
    schedule_step machine terminal blocks thread state = state.resume thread (next (.error 35)) := by
  simp [schedule_step, running, runnable, waiting]

def run_schedule (machine : TraceMachine heap buffer) (terminal : Bool) (blocks : Nat → Option (ThreadCode α))
    (schedule : List Nat) (initial : ScheduleState α heap buffer) : ScheduleState α heap buffer :=
  schedule.foldl (fun state thread => schedule_step machine terminal blocks thread state) initial

theorem exclusive_schedule (machine : TraceMachine heap buffer) (terminal : Bool)
    (blocks : Nat → Option (ThreadCode α)) (state : ScheduleState α heap buffer)
    (held : state.owner = some owner) (schedule : List Nat) (absent : owner ∉ schedule) :
    run_schedule machine terminal blocks schedule state = state := by
  induction schedule with
  | nil => rfl
  | cons thread later ih =>
    have other : owner ≠ thread := fun same => absent (List.mem_cons.mpr (.inl same))
    have rest : owner ∉ later := fun member => absent (List.mem_cons.mpr (.inr member))
    change run_schedule _ _ _ later (schedule_step _ _ _ thread state) = state
    rw [exclusive_step machine terminal blocks state held other]
    exact ih rest

private theorem schedule_step_literal (state : ScheduleState α HeapState StdoutState) (thread : Nat)
    (terminal : Bool) (blocks : Nat → Option (ThreadCode α))
    (fitted : state.memory.counter.ident ≤ 9223372036854775807) (found : state.memory.literals.lookup text = some ptr) :
    let next := schedule_step abstract_machine terminal blocks thread state
    next.memory.counter.ident ≤ 9223372036854775807 ∧ next.memory.literals.lookup text = some ptr := by
  unfold schedule_step
  split
  · exact ⟨fitted, found⟩
  · cases state.jobs thread with
    | effect operation _ =>
      dsimp only [abstract_machine, id_eq]
      split
      · exact ⟨fitted, found⟩
      · rename_i edit performed
        obtain ⟨transition, fits⟩ := heap_effect_transition { state.memory with arrayFrames := state.frames thread } operation edit fitted performed
        have persists := heap_transition_preserves_literal (text := text) transition (ptr := ptr) found
        exact ⟨fits, persists⟩
    | idle | tick | output | exit | fault | bindSelf | getSelf | resolve | spawn => exact ⟨fitted, found⟩
    | synchronise | jump | finish | join | await =>
      dsimp only
      repeat' first | exact ⟨fitted, found⟩ | split

theorem scheduled_literal_reuse (state : ScheduleState α HeapState StdoutState) (schedule : List Nat)
    (terminal : Bool) (blocks : Nat → Option (ThreadCode α))
    (fitted : state.memory.counter.ident ≤ 9223372036854775807) (found : state.memory.literals.lookup text = some ptr) :
    let after := run_schedule abstract_machine terminal blocks schedule state
    heap_effect after.memory (.intern text) = .ok { reply := .pointer ptr } := by
  induction schedule generalizing state with
  | nil => simp [run_schedule, heap_effect, found]
  | cons thread rest ih =>
    obtain ⟨fits, persists⟩ := schedule_step_literal state thread terminal blocks fitted found
    exact ih _ fits persists

theorem scheduled_intern_identity (state : ScheduleState α HeapState StdoutState)
    (terminal : Bool) (blocks : Nat → Option (ThreadCode α)) (thread : Nat) (schedule : List Nat)
    (running : state.outcome = .paused) (runnable : state.runnable thread = true) (ready : state.jobs thread = .effect (.intern text) next)
    (fitted : state.memory.counter.ident ≤ 9223372036854775807)
    (accepted : heap_effect { state.memory with arrayFrames := state.frames thread } (.intern text) = .ok edit) :
    ∃ ptr, edit.reply = .pointer ptr ∧
      let after := run_schedule abstract_machine terminal blocks (thread :: schedule) state
      heap_effect after.memory (.intern text) = .ok { reply := .pointer ptr } := by
  obtain ⟨ptr, reply, found, _⟩ := intern_publishes accepted
  obtain ⟨_, fits⟩ := heap_effect_transition { state.memory with arrayFrames := state.frames thread } (.intern text) edit fitted accepted
  refine ⟨ptr, reply, ?_⟩
  apply scheduled_literal_reuse (schedule_step abstract_machine terminal blocks thread state) schedule terminal blocks
  · simpa only [schedule_step, running, runnable, ne_eq, not_true_eq_false, Bool.true_eq_false, or_self, if_false, ready, abstract_machine, id_eq, accepted] using fits
  · simpa only [schedule_step, running, runnable, ne_eq, not_true_eq_false, Bool.true_eq_false, or_self, if_false, ready, abstract_machine, id_eq, accepted] using found

def ScheduleState.snapshot (state : ScheduleState α HeapImage StdoutBuffer) (reference : Nat → Nat := id) :
    ScheduleState α HeapState StdoutState :=
  ⟨state.memory.snapshot reference, state.stdout.snapshot, state.jobs, state.frames, state.joins,
    state.nextThread, state.outcome, state.handles, state.owner, state.sync⟩

private theorem schedule_step_refines (terminal : Bool) (blocks : Nat → Option (ThreadCode α))
    (thread : Nat) (state : ScheduleState α HeapImage StdoutBuffer)
    (reference : Nat → Nat) (distinct : Function.Injective reference)
    (valid : state.stdout.size = state.stdout.snapshot.pending.length) :
    let next := schedule_step (sparse_machine reference) terminal blocks thread state
    next.snapshot reference = schedule_step abstract_machine terminal blocks thread (state.snapshot reference) ∧
      next.stdout.size = next.stdout.snapshot.pending.length := by
  by_cases runnable : state.runnable thread
  case neg =>
    have blocked : state.runnable thread = false := by simpa using runnable
    have same : (state.snapshot reference).runnable thread = false := blocked
    simp [schedule_step, blocked, same, valid]
  case pos =>
    have same : (state.snapshot reference).runnable thread = true := runnable
    by_cases running : state.outcome = .paused
    · have same_outcome : (state.snapshot reference).outcome = state.outcome := rfl
      have same_job : (state.snapshot reference).jobs thread = state.jobs thread := rfl
      simp only [schedule_step, same_outcome, same_job, running, runnable, same, Bool.true_eq_false, or_self, ne_eq, not_true_eq_false, if_false]
      cases state.jobs thread with
      | synchronise op ptr other next =>
        cases outcome : sync_step (state.memory.snapshot reference) state.sync thread op ptr other with
        | error _ => simp [ScheduleState.snapshot, sparse_machine, abstract_machine, outcome, valid]
        | ok pair =>
          obtain ⟨updated, result⟩ := pair
          cases result <;> simp [ScheduleState.snapshot, ScheduleState.resume, sparse_machine, abstract_machine, outcome, valid]
      | effect operation continuation =>
        cases applied : heap_effect { state.memory.snapshot reference with arrayFrames := state.frames thread } operation with
        | error fault => simp [ScheduleState.snapshot, sparse_machine, abstract_machine, applied, valid]
        | ok edit =>
          simp [ScheduleState.snapshot, ScheduleState.resume, sparse_machine, abstract_machine, applied,
            heap_image_edit _ _ reference distinct, valid]
      | output bytes next =>
        obtain ⟨view, consistent⟩ := stdout_chunks_correct terminal state.stdout bytes valid
        simp [ScheduleState.snapshot, ScheduleState.resume, sparse_machine, abstract_machine, view, consistent]
      | jump block => cases destination : blocks block <;> simp [ScheduleState.snapshot, ScheduleState.resume, destination, valid]
      | idle | exit | fault | tick | spawn | bindSelf | getSelf | resolve =>
        simp [ScheduleState.snapshot, ScheduleState.resume, ScheduleState.record, valid]
      | finish value =>
        cases entry : state.joins thread <;> simp [ScheduleState.snapshot, ScheduleState.resume, ScheduleState.record, entry, valid]
        split <;> simp [valid]
      | join child next =>
        by_cases self : child = thread
        · simp [ScheduleState.snapshot, ScheduleState.resume, self, valid]
        · cases entry : state.joins child <;>
            simp [ScheduleState.snapshot, ScheduleState.resume, ScheduleState.record, self, entry, valid]
          split <;> simp [valid]
      | await child next =>
        cases entry : state.joins child with
        | none => simp [ScheduleState.snapshot, ScheduleState.resume, entry, valid]
        | some task =>
          by_cases ready : task.claimant = some thread ∧ task.received.isNone = true
          · cases result : task.result <;>
              simp [ScheduleState.snapshot, ScheduleState.resume, ScheduleState.record, entry, ready, result, valid]
          · simp only [ScheduleState.snapshot, entry, if_neg ready, ScheduleState.resume, valid, and_true]
    · simp [schedule_step, ScheduleState.snapshot, running, valid]

theorem schedule_refines (terminal : Bool) (blocks : Nat → Option (ThreadCode α)) (schedule : List Nat)
    (state : ScheduleState α HeapImage StdoutBuffer) (reference : Nat → Nat)
    (distinct : Function.Injective reference) (valid : state.stdout.size = state.stdout.snapshot.pending.length) :
    (run_schedule (sparse_machine reference) terminal blocks schedule state).snapshot reference =
      run_schedule abstract_machine terminal blocks schedule (state.snapshot reference) := by
  induction schedule generalizing state with
  | nil => rfl
  | cons thread later ih =>
    obtain ⟨agrees, consistent⟩ := schedule_step_refines terminal blocks thread state reference distinct valid
    simp only [run_schedule, List.foldl_cons]
    change (run_schedule (sparse_machine reference) terminal blocks later
      (schedule_step (sparse_machine reference) terminal blocks thread state)).snapshot reference =
      run_schedule abstract_machine terminal blocks later
        (schedule_step abstract_machine terminal blocks thread (state.snapshot reference))
    rw [ih _ consistent, agrees]

theorem scheduled_lowering (program : Ordinary.Program) (depth : Nat) (invocation : Ordinary.Invocation)
    (context : ThreadCode α → ScheduleState α HeapImage StdoutBuffer) (schedule : List Nat)
    (terminal : Bool) (blocks : Nat → Option (ThreadCode α)) (reference : Nat → Nat)
    (distinct : Function.Injective reference)
    (valid : ∀ code, (context code).stdout.size = (context code).stdout.snapshot.pending.length) :
    (run_schedule (sparse_machine reference) terminal blocks schedule
      (context (.fromTrace (program.target depth invocation)))).snapshot reference =
    run_schedule abstract_machine terminal blocks schedule
      ((context (.fromTrace ((program.source depth invocation).emit .finish))).snapshot reference) := by
  rw [Ordinary.lower_program_correct]
  exact schedule_refines _ _ _ _ reference distinct (valid _)

private abbrev Worker := List (String × Pointer) → String → Pointer → TraceProgram

private def thread_code (worker : Worker) : Nat → TraceProgram → ThreadCode Pointer
  | 0, _ => .idle
  | depth + 1, trace =>
    let resume := thread_code worker depth
    match trace with
    | .finish status => .exit status
    | .fail reason => .fault reason
    | .jump 1 => .idle
    | .jump _ => .fault .missingBlock
    | .tick next => .tick (resume next)
    | .output bytes next => .output bytes (resume next)
    | .effect op next =>
      match op with
      | .thread (.synchronise op ptr other) => .synchronise op ptr other fun n => resume (next (.word n))
      | .thread (.root handle) => .bindSelf handle (resume (next .done))
      | .thread (.create handle name arg globals) =>
        .spawn (resume (worker globals name arg)) (fun _ => resume (next .done)) (some handle)
      | .thread (.publish value) => .finish value
      | .thread (.join handle) => .resolve handle fun
        | none => resume (next (.word 3))
        | some child => .join child fun
          | .error code => resume (next (.word code))
          | .ok value => resume (next (.pointer value))
      | .thread .self => .getSelf fun ptr => resume (next (.pointer (ptr.getD ⟨0, 0⟩)))
      | operation => .effect operation fun reply => resume (next reply)

def Ordinary.Program.threads (program : Ordinary.Program) (depth : Nat) (invocation : Ordinary.Invocation) :=
  thread_code (program.worker depth) depth (program.target depth invocation)

def Ordinary.Program.sourceThreads (program : Ordinary.Program) (depth : Nat) (invocation : Ordinary.Invocation) :=
  thread_code (program.sourceWorker depth) depth ((program.source depth invocation).emit .finish)

theorem compiled_threads_refine (program : Ordinary.Program) (depth : Nat) (invocation : Ordinary.Invocation)
    (terminal : Bool) (schedule : List Nat) :
    (run_schedule sparse_machine terminal (fun _ => none) schedule (ScheduleState.start
      (HeapImage.mk [] ⟨1, 4096⟩ [] [] { events := invocation.files }) (StdoutBuffer.mk [] [] 0 true) (program.threads depth invocation))).snapshot =
    run_schedule abstract_machine terminal (fun _ => none) schedule (ScheduleState.start
      (HeapState.mk (fun _ => none) ⟨1, 4096⟩ [] [] { events := invocation.files }) (StdoutState.mk [] [] true) (program.sourceThreads depth invocation)) := by
  unfold Ordinary.Program.threads Ordinary.Program.sourceThreads
  rw [Ordinary.worker_correct, Ordinary.lower_program_correct]
  apply schedule_refines <;> first | exact Function.injective_id | rfl

private def round_robin (machine : TraceMachine heap buffer) (terminal : Bool) :
    Nat → Nat → ScheduleState Pointer heap buffer → List Nat
  | 0, _, _ => []
  | fuel + 1, thread, state =>
    if state.outcome != .paused then [] else
      let next := schedule_step machine terminal (fun _ => none) thread state
      thread :: round_robin machine terminal fuel ((thread + 1) % next.nextThread) next

def Ordinary.Program.threadSchedule (program : Ordinary.Program) (depth : Nat) (terminal : Bool)
    (invocation : Ordinary.Invocation) : List Nat :=
  round_robin sparse_machine terminal depth 0 (ScheduleState.start (HeapImage.mk [] ⟨1, 4096⟩ [] [] { events := invocation.files })
    (StdoutBuffer.mk [] [] 0 true) (program.threads depth invocation))

def Ordinary.Program.threadObservation (program : Ordinary.Program) (depth : Nat) (terminal : Bool)
    (invocation : Ordinary.Invocation) (schedule : List Nat) :=
  let state := run_schedule sparse_machine terminal (fun _ => none) schedule (ScheduleState.start
    (HeapImage.mk [] ⟨1, 4096⟩ [] [] { events := invocation.files }) (StdoutBuffer.mk [] [] 0 true) (program.threads depth invocation))
  TraceResult.observation ⟨state.outcome, state.snapshot.memory, state.stdout.snapshot⟩

def Ordinary.Program.sourceThreadObservation (program : Ordinary.Program) (depth : Nat) (terminal : Bool)
    (invocation : Ordinary.Invocation) (schedule : List Nat) :=
  let state := run_schedule abstract_machine terminal (fun _ => none) schedule (ScheduleState.start
    (HeapState.mk (fun _ => none) ⟨1, 4096⟩ [] [] { events := invocation.files }) (StdoutState.mk [] [] true) (program.sourceThreads depth invocation))
  TraceResult.observation ⟨state.outcome, state.memory, state.stdout⟩

theorem thread_observation_correct (program : Ordinary.Program) (depth : Nat) (terminal : Bool)
    (invocation : Ordinary.Invocation) (schedule : List Nat) :
    program.threadObservation depth terminal invocation schedule =
      program.sourceThreadObservation depth terminal invocation schedule :=
  congrArg (fun (state : ScheduleState Pointer HeapState StdoutState) =>
    TraceResult.observation ⟨state.outcome, state.memory, state.stdout⟩)
    (compiled_threads_refine program depth invocation terminal schedule)

def ValidJoinTable (joins : Nat → Option (JoinState α)) (frontier : Nat) : Prop :=
  ∀ child entry, joins child = some entry →
    child < frontier ∧ ∃ history, JoinTrace child .published history entry

private theorem record_join (valid : ValidJoinTable table before) (growth : before ≤ after)
    (allocated : child < after) (history : JoinTrace child .published events entry) :
    ValidJoinTable (update_sync_cell table child (some entry)) after := by
  intro key value found
  by_cases same : key = child
  · subst key
    simp [update_sync_cell] at found
    subst value
    exact ⟨allocated, _, history⟩
  · simp [update_sync_cell, same] at found
    obtain ⟨bound, previous⟩ := valid _ _ found
    exact ⟨Nat.lt_of_lt_of_le bound growth, previous⟩

private theorem advance_join (valid : ValidJoinTable table frontier) (found : table child = some entry)
    (step : JoinStep child entry event next) :
    ValidJoinTable (update_sync_cell table child (some next)) frontier := by
  obtain ⟨allocated, _, history⟩ := valid _ _ found
  exact record_join valid (Nat.le_refl _) allocated (.step history step)

private theorem schedule_step_joins (machine : TraceMachine heap buffer) (terminal : Bool)
    (blocks : Nat → Option (ThreadCode α)) (thread : Nat) (state : ScheduleState α heap buffer)
    (valid : ValidJoinTable state.joins state.nextThread) :
    let next := schedule_step machine terminal blocks thread state
    ValidJoinTable next.joins next.nextThread := by
  unfold schedule_step
  split
  · exact valid
  · cases state.jobs thread with
    | idle | tick | output | exit | fault | bindSelf | getSelf | resolve => exact valid
    | jump block =>
      dsimp only
      split <;> exact valid
    | synchronise | effect =>
      dsimp only
      split <;> exact valid
    | spawn worker next handle =>
      exact record_join valid (Nat.le_succ _) (Nat.lt_succ_self _) (.empty : JoinTrace _ .published [] _)
    | finish value =>
      cases found : state.joins thread with
      | none => exact valid
      | some entry =>
        dsimp only
        split
        · exact valid
        · rename_i empty
          exact advance_join valid found (.publish (by simpa using empty))
    | join child next =>
      dsimp only
      split
      · exact valid
      · rename_i different
        cases found : state.joins child with
        | none => exact valid
        | some entry =>
          dsimp only
          split
          · exact valid
          · rename_i available
            exact advance_join valid found (.claim (Ne.symm different) (by simpa using available))
    | await child next =>
      dsimp only
      cases found : state.joins child with
      | none => exact valid
      | some entry =>
        dsimp only
        split
        · rename_i claimed
          cases finished : entry.result with
          | none => exact valid
          | some value =>
            simpa only [finished] using advance_join valid found
              (.receive claimed.1 finished (by simpa using claimed.2))
        · exact valid

theorem scheduled_join_histories (machine : TraceMachine heap buffer) (terminal : Bool)
    (blocks : Nat → Option (ThreadCode α)) (schedule : List Nat) (memory : heap) (stdout : buffer)
    (main : ThreadCode α) :
    let result := run_schedule machine terminal blocks schedule (ScheduleState.start memory stdout main)
    ValidJoinTable result.joins result.nextThread := by
  have preserve (state : ScheduleState α heap buffer) (valid : ValidJoinTable state.joins state.nextThread) :
      let result := run_schedule machine terminal blocks schedule state
      ValidJoinTable result.joins result.nextThread := by
    induction schedule generalizing state with
    | nil => exact valid
    | cons thread _ ih => exact ih _ (schedule_step_joins machine terminal blocks thread state valid)
  exact preserve _ (by simp [ScheduleState.start, ValidJoinTable])

theorem scheduled_join_cells (machine : TraceMachine heap buffer) (terminal : Bool)
    (blocks : Nat → Option (ThreadCode α)) (schedule : List Nat) (memory : heap) (stdout : buffer)
    (main : ThreadCode α) :
    let result := run_schedule machine terminal blocks schedule (ScheduleState.start memory stdout main)
    ∀ child entry, result.joins child = some entry →
      ∃ history cell, CellTrace child history cell ∧ CellView cell entry ∧
        history.filterMap JoinEvent.received = entry.received.toList ∧ entry.valid child := by
  intro result child entry found
  obtain ⟨_, history, trace⟩ :=
    scheduled_join_histories machine terminal blocks schedule memory stdout main child entry found
  obtain ⟨cell, cells, view⟩ := cell_trace_complete trace
  exact ⟨history, cell, cells, view, (join_trace_prefix history entry trace).2.2⟩

def handoff_program (stale : Bool) : ThreadCode Pointer :=
  let worker := ThreadCode.effect (.allocate 1) fun
    | .pointer pointer => .effect (.storeByte pointer 65) fun _ => .finish pointer
    | _ => .fault .space
  .spawn worker fun child => .join child fun
    | .error code => .exit code
    | .ok pointer => .effect (.loadByte pointer) fun
      | .byte byte => .output [[byte]] (.output [[10]] (.effect (.release pointer) fun _ =>
          if stale then .effect (.loadByte pointer) (fun
            | .byte value => .exit value.toNat
            | _ => .exit 2) else .exit 0))
      | _ => .exit 2

private def handoff_state (stale : Bool) (schedule : List Nat) :=
  let state := ScheduleState.start (HeapImage.mk [] ⟨1, 4096⟩ [] [] {}) (StdoutBuffer.mk [] [] 0 true) (handoff_program stale)
  run_schedule sparse_machine true (fun _ => none) schedule state

def handoff_observation (stale : Bool) (schedule : List Nat) : TraceOutcome × List UInt8 :=
  let result := handoff_state stale schedule
  (result.outcome, result.stdout.snapshot.visible)

private inductive WorkerPhase where
  | started | allocated | stored | finished

private def WorkerPhase.advance : WorkerPhase → WorkerPhase
  | .started => .allocated
  | .allocated => .stored
  | .stored | .finished => .finished

private def WorkerPhase.steps : WorkerPhase → Nat
  | .started => 0
  | .allocated => 1
  | .stored => 2
  | .finished => 3

private inductive Handoff where
  | initial
  | racing (claimed : Bool) (worker : WorkerPhase)
  | received | loaded | emitted | written | freed | stopped

private def Handoff.select (phase : Handoff) (thread : Nat) : Handoff :=
  match phase, thread with
  | .initial, 0 => .racing false .started
  | .racing false worker, 0 => .racing true worker
  | .racing true .finished, 0 => .received
  | .racing claimed worker, 1 => .racing claimed worker.advance
  | .received, 0 => .loaded
  | .loaded, 0 => .emitted
  | .emitted, 0 => .written
  | .written, 0 => .freed
  | .freed, 0 => .stopped
  | _, _ => phase

private def Handoff.replay : Handoff → List Nat
  | .initial => []
  | .racing claimed worker => [0] ++ (if claimed then [0] else []) ++ List.replicate worker.steps 1
  | .received => [0, 0, 1, 1, 1, 0]
  | .loaded => [0, 0, 1, 1, 1, 0, 0]
  | .emitted => [0, 0, 1, 1, 1, 0, 0, 0]
  | .written => [0, 0, 1, 1, 1, 0, 0, 0, 0]
  | .freed => [0, 0, 1, 1, 1, 0, 0, 0, 0, 0]
  | .stopped => [0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]

private theorem handoff_step (stale : Bool) (phase : Handoff) (thread : Nat) :
    schedule_step sparse_machine true (fun _ => none) thread (handoff_state stale phase.replay) =
      handoff_state stale (phase.select thread).replay := by
  cases phase <;> try (rename_i claimed worker; cases claimed <;> cases worker)
  all_goals rcases thread with _ | ⟨_ | thread⟩
  all_goals cases stale
  all_goals first
    | rfl
    | apply ScheduleState.ext <;> first | rfl | (funext key; rcases key with _ | ⟨_ | key⟩ <;> rfl)

private theorem handoff_replay (stale : Bool) (schedule : List Nat) :
    handoff_state stale schedule = handoff_state stale (schedule.foldl Handoff.select .initial).replay := by
  have simulate (phase : Handoff) :
      run_schedule sparse_machine true (fun _ => none) schedule (handoff_state stale phase.replay) =
        handoff_state stale (schedule.foldl Handoff.select phase).replay := by
    induction schedule generalizing phase with
    | nil => rfl
    | cons thread later ih =>
      change run_schedule _ _ _ later (schedule_step _ _ _ thread _) = _
      rw [handoff_step]
      exact ih _
  exact simulate .initial

theorem scheduled_handoff_outcome (stale : Bool) (schedule : List Nat)
    (completed : (handoff_observation stale schedule).1 ≠ .paused) :
    handoff_observation stale schedule = (if stale then .fault (.access .dead) else .returned 0, [65, 10]) := by
  change (handoff_state stale schedule).outcome ≠ .paused at completed
  change ((handoff_state stale schedule).outcome, (handoff_state stale schedule).stdout.snapshot.visible) = _
  rw [handoff_replay stale schedule] at completed ⊢
  generalize h : schedule.foldl Handoff.select .initial = phase at completed ⊢
  cases phase with
  | racing claimed worker => cases claimed <;> cases worker <;> cases stale <;> exact (completed rfl).elim
  | stopped => cases stale <;> rfl
  | _ => cases stale <;> exact (completed rfl).elim

theorem scheduled_handoff_completion (stale : Bool) (schedule : List Nat) :
    handoff_observation stale (schedule ++ [0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]) =
      (if stale then .fault (.access .dead) else .returned 0, [65, 10]) := by
  unfold handoff_observation
  rw [handoff_replay, List.foldl_append]
  cases schedule.foldl Handoff.select .initial with
  | racing claimed worker => cases claimed <;> cases worker <;> cases stale <;> rfl
  | _ => cases stale <;> rfl

end Heresy

#print axioms Heresy.schedule_refines
#print axioms Heresy.scheduled_lowering
#print axioms Heresy.scheduled_join_cells
#print axioms Heresy.scheduled_join_histories
#print axioms Heresy.scheduled_handoff_completion
#print axioms Heresy.scheduled_handoff_outcome

#print axioms Heresy.thread_observation_correct

#print axioms Heresy.scheduled_intern_identity
