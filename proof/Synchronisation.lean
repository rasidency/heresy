import Std

set_option warningAsError true

namespace Heresy

structure MutexQueue where
  owner : Option Nat
  waiting : List (Nat × Nat)

inductive MutexResult where
  | complete (status : Nat)
  | wait (ticket : Nat)

def mutex_acquire (try_only : Bool) (thread ticket : Nat) (mutex : MutexQueue) : MutexQueue × MutexResult :=
  match mutex.owner with
  | none => (⟨some thread, mutex.waiting⟩, .complete 0)
  | some owner =>
    if try_only then (mutex, .complete 16)
    else if owner = thread then (mutex, .complete 35)
    else (⟨some owner, mutex.waiting ++ [(thread, ticket)]⟩, .wait ticket)

theorem busy_try_lock_preserves_queue (thread ticket owner : Nat) (waiting : List (Nat × Nat)) :
    mutex_acquire true thread ticket ⟨some owner, waiting⟩ = (⟨some owner, waiting⟩, .complete 16) := rfl

theorem waiting_lock_preserves_owner (thread ticket owner : Nat) (waiting : List (Nat × Nat))
    (different : owner ≠ thread) :
    mutex_acquire false thread ticket ⟨some owner, waiting⟩ =
      (⟨some owner, waiting ++ [(thread, ticket)]⟩, .wait ticket) := by
  simp [mutex_acquire, different]

def mutex_release (thread : Nat) (mutex : MutexQueue) : Option (MutexQueue × Option Nat) :=
  if mutex.owner = some thread then
    match mutex.waiting with
    | [] => some (⟨none, []⟩, none)
    | (next, ticket) :: rest => some (⟨some next, rest⟩, some ticket)
  else none

theorem mutex_release_handoff (thread successor ticket : Nat) (tail : List (Nat × Nat)) :
    mutex_release thread ⟨some thread, (successor, ticket) :: tail⟩ =
      some (⟨some successor, tail⟩, some ticket) := by
  simp [mutex_release]

theorem mutex_release_requires_owner (thread : Nat) (mutex next : MutexQueue) (ticket : Option Nat)
    (released : mutex_release thread mutex = some (next, ticket)) : mutex.owner = some thread := by
  by_cases owner : mutex.owner = some thread
  · exact owner
  · simp [mutex_release, owner] at released

def condition_enroll (thread ticket : Nat) (mutex : MutexQueue) (condition : List Nat) :
    Option (MutexQueue × List Nat × Option Nat) :=
  (mutex_release thread mutex).map fun (next, signal) => (next, condition ++ [ticket], signal)

theorem condition_enroll_releases_and_keeps_ticket (thread ticket : Nat) (mutex next : MutexQueue)
    (condition updated : List Nat) (signal : Option Nat)
    (enrolled : condition_enroll thread ticket mutex condition = some (next, updated, signal)) :
    mutex_release thread mutex = some (next, signal) ∧ updated = condition ++ [ticket] ∧ ticket ∈ updated := by
  cases release : mutex_release thread mutex with
  | none => simp [condition_enroll, release] at enrolled
  | some pair =>
    obtain ⟨owner, wake⟩ := pair
    simp [condition_enroll, release] at enrolled
    obtain ⟨rfl, rfl, rfl⟩ := enrolled
    exact ⟨rfl, rfl, by simp⟩

def update_sync_cell (cells : Nat → α) (slot : Nat) (value : α) : Nat → α :=
  fun key => if key = slot then value else cells key

theorem condition_and_mutex_updates_share_allocation (cells : Nat → α)
    (condition mutex : Nat) (condition_value mutex_value : α) (distinct : condition ≠ mutex) :
    let updated := update_sync_cell (update_sync_cell cells mutex mutex_value) condition condition_value
    updated condition = condition_value ∧ updated mutex = mutex_value ∧
      ∀ slot, slot ≠ condition → slot ≠ mutex → updated slot = cells slot := by
  simp [update_sync_cell, Ne.symm distinct]
  intro slot condition_distinct mutex_distinct
  simp [condition_distinct, mutex_distinct]

def choose_signals (broadcast : Bool) (waiting : List Nat) : List Nat × List Nat :=
  if broadcast then (waiting, [])
  else
    match waiting with
    | [] => ([], [])
    | first :: rest => ([first], rest)

theorem signal_partitions_queue (broadcast : Bool) (waiting : List Nat) :
    let (selected, retained) := choose_signals broadcast waiting
    selected ++ retained = waiting := by
  cases broadcast <;> cases waiting <;> simp [choose_signals]

theorem signal_takes_first (first : Nat) (rest : List Nat) :
    choose_signals false (first :: rest) = ([first], rest) := rfl

theorem broadcast_takes_all (waiting : List Nat) : choose_signals true waiting = (waiting, []) := rfl

structure SignalQueue where
  waiting : List Nat
  selected : List Nat
  posted : List Nat

def SignalQueue.contains (state : SignalQueue) (ticket : Nat) : Prop :=
  ticket ∈ state.waiting ∨ ticket ∈ state.selected ∨ ticket ∈ state.posted

def enqueue_signal (state : SignalQueue) (ticket : Nat) : SignalQueue :=
  { state with waiting := state.waiting ++ [ticket] }

def select_signals (state : SignalQueue) (broadcast : Bool) : SignalQueue :=
  let (chosen, retained) := choose_signals broadcast state.waiting
  { state with waiting := retained, selected := state.selected ++ chosen }

def post_signal (state : SignalQueue) (ticket : Nat) : SignalQueue :=
  { state with selected := state.selected.erase ticket, posted := ticket :: state.posted }

def consume_signal (state : SignalQueue) (ticket : Nat) : SignalQueue :=
  { state with posted := state.posted.erase ticket }

inductive SignalStep (tracked : Nat) : SignalQueue → SignalQueue → Prop where
  | enqueue : SignalStep tracked state (enqueue_signal state ticket)
  | select : SignalStep tracked state (select_signals state broadcast)
  | post : ticket ∈ state.selected → SignalStep tracked state (post_signal state ticket)
  | consume_other : ticket ∈ state.posted → tracked ≠ ticket → SignalStep tracked state (consume_signal state ticket)

theorem enrolment_survives_interleaving (tracked : Nat) (before after : SignalQueue)
    (step : SignalStep tracked before after) (pending : before.contains tracked) : after.contains tracked := by
  cases step with
  | enqueue =>
    rcases pending with waiting | selected | posted
    · exact Or.inl (List.mem_append_left _ waiting)
    · exact Or.inr (Or.inl selected)
    · exact Or.inr (Or.inr posted)
  | select =>
    rename_i broadcast
    have separated := signal_partitions_queue broadcast before.waiting
    cases selection : choose_signals broadcast before.waiting with
    | mk chosen retained =>
      simp only [selection] at separated
      have in_queues : tracked ∈ chosen ∨ tracked ∈ retained ∨ tracked ∈ before.selected ∨ tracked ∈ before.posted := by
        simpa only [SignalQueue.contains, ← separated, List.mem_append, or_assoc] using pending
      simpa [SignalQueue.contains, select_signals, selection, List.mem_append, or_left_comm, or_comm, or_assoc] using in_queues
  | post _selected =>
    rename_i ticket
    by_cases same : tracked = ticket
    · subst tracked
      simp [SignalQueue.contains, post_signal]
    · simpa [SignalQueue.contains, post_signal, same, List.mem_erase_of_ne] using pending
  | consume_other _ different =>
    simpa [SignalQueue.contains, consume_signal, List.mem_erase_of_ne different] using pending

inductive SignalTrace (tracked : Nat) : SignalQueue → SignalQueue → Prop where
  | empty : SignalTrace tracked state state
  | step : SignalTrace tracked before middle → SignalStep tracked middle after → SignalTrace tracked before after

theorem enrolment_survives_trace (tracked : Nat) (before after : SignalQueue)
    (trace : SignalTrace tracked before after) (pending : before.contains tracked) : after.contains tracked := by
  induction trace with
  | empty => exact pending
  | step _ action previous => exact enrolment_survives_interleaving tracked _ _ action previous

theorem signal_is_available_before_the_receiver_runs (ticket : Nat) (waiting : List Nat) (state : SignalQueue)
    (first : state.waiting = ticket :: waiting) :
    ticket ∈ (select_signals state false).selected ∧
      ticket ∈ (post_signal (select_signals state false) ticket).posted := by
  simp [select_signals, post_signal, first, choose_signals]

def MutexQueue.valid (mutex : MutexQueue) : Prop :=
  (mutex.waiting.map Prod.fst).Nodup ∧
    match mutex.owner with
    | none => mutex.waiting = []
    | some owner => owner ∉ mutex.waiting.map Prod.fst

theorem mutex_acquire_valid (try_only : Bool) (thread ticket : Nat) (mutex : MutexQueue)
    (valid : mutex.valid) (fresh : thread ∉ mutex.waiting.map Prod.fst) :
    (mutex_acquire try_only thread ticket mutex).1.valid := by
  cases owner : mutex.owner with
  | none =>
    have empty : mutex.waiting = [] := by simpa [owner] using valid.2
    simp [mutex_acquire, MutexQueue.valid, owner, empty]
  | some current =>
    have absent : current ∉ mutex.waiting.map Prod.fst := by simpa [owner] using valid.2
    by_cases same : current = thread
    · cases try_only <;> simpa [mutex_acquire, owner, same] using valid
    · cases try_only
      · simp [mutex_acquire, MutexQueue.valid, owner, same, absent, List.nodup_append, valid.1]
        intro earlier queued present equal
        subst earlier
        exact fresh (List.mem_map_of_mem (show (thread, queued) ∈ mutex.waiting from present))
      · simpa [mutex_acquire, owner] using valid

theorem mutex_release_valid (thread : Nat) (mutex next : MutexQueue) (signal : Option Nat)
    (valid : mutex.valid) (released : mutex_release thread mutex = some (next, signal)) : next.valid := by
  have owns := mutex_release_requires_owner thread mutex next signal released
  cases waiting : mutex.waiting with
  | nil =>
    simp [mutex_release, owns, waiting] at released
    obtain ⟨rfl, _⟩ := released
    simp [MutexQueue.valid]
  | cons entry tail =>
    obtain ⟨successor, ticket⟩ := entry
    simp [mutex_release, owns, waiting] at released
    obtain ⟨rfl, _⟩ := released
    have nodup := valid.1
    simp [MutexQueue.valid, waiting] at nodup ⊢
    exact nodup.symm

theorem mutex_handoff_reserves_ownership (owner successor ticket arriving new_ticket : Nat)
    (waiting : List (Nat × Nat)) (later : successor ≠ arriving) :
    let handoff := MutexQueue.mk (some successor) waiting
    mutex_release owner ⟨some owner, (successor, ticket) :: waiting⟩ = some (handoff, some ticket) ∧
      mutex_acquire true arriving new_ticket handoff = (handoff, .complete 16) ∧
      mutex_acquire false arriving new_ticket handoff =
        (⟨some successor, waiting ++ [(arriving, new_ticket)]⟩, .wait new_ticket) := by
  exact ⟨mutex_release_handoff owner successor ticket waiting,
    busy_try_lock_preserves_queue arriving new_ticket successor waiting,
    waiting_lock_preserves_owner arriving new_ticket successor waiting later⟩

theorem condition_enrolment_survives_handoff (thread ticket : Nat) (previous updated : MutexQueue)
    (queue : SignalQueue) (waiting : List Nat) (signal : Option Nat) (after : SignalQueue)
    (valid : previous.valid)
    (enrolled : condition_enroll thread ticket previous queue.waiting = some (updated, waiting, signal))
    (steps : SignalTrace ticket { queue with waiting } after) :
    updated.valid ∧ after.contains ticket := by
  obtain ⟨released, _, pending⟩ := condition_enroll_releases_and_keeps_ticket thread ticket
    previous updated queue.waiting waiting signal enrolled
  exact ⟨mutex_release_valid thread previous updated signal valid released,
    enrolment_survives_trace ticket _ after steps (.inl pending)⟩

def condition_reacquire (thread signal mutex_ticket : Nat) (condition : SignalQueue) (mutex : MutexQueue) :
    Option (SignalQueue × MutexQueue × MutexResult) :=
  if signal ∈ condition.posted then
    let (next, outcome) := mutex_acquire false thread mutex_ticket mutex
    some (consume_signal condition signal, next, outcome)
  else none

theorem condition_reacquire_requires_post (thread signal mutex_ticket : Nat) (condition updated : SignalQueue)
    (mutex next : MutexQueue) (outcome : MutexResult)
    (resumed : condition_reacquire thread signal mutex_ticket condition mutex = some (updated, next, outcome)) :
    signal ∈ condition.posted ∧ updated = consume_signal condition signal := by
  by_cases posted : signal ∈ condition.posted
  · simp [condition_reacquire, posted] at resumed
    exact ⟨posted, resumed.1.symm⟩
  · simp [condition_reacquire, posted] at resumed

theorem condition_immediate_reacquire_owns (thread signal mutex_ticket : Nat)
    (condition updated : SignalQueue) (mutex next : MutexQueue)
    (resumed : condition_reacquire thread signal mutex_ticket condition mutex =
      some (updated, next, .complete 0)) : next.owner = some thread := by
  have posted := (condition_reacquire_requires_post _ _ _ _ _ _ _ _ resumed).1
  cases owner : mutex.owner with
  | none =>
    simp [condition_reacquire, posted, mutex_acquire, owner] at resumed
    obtain ⟨_, rfl⟩ := resumed
    rfl
  | some current =>
    by_cases same : current = thread <;>
      simp [condition_reacquire, posted, mutex_acquire, owner, same] at resumed

inductive MutexHandoffs : MutexQueue → List Nat → MutexQueue → Prop where
  | idle : MutexHandoffs mutex [] mutex
  | step : mutex_release owner before = some (middle, some ticket) →
      MutexHandoffs middle tickets after → MutexHandoffs before (ticket :: tickets) after

theorem mutex_handoffs_serve_fifo (owner thread ticket : Nat) (earlier : List (Nat × Nat)) :
    MutexHandoffs ⟨some owner, earlier ++ [(thread, ticket)]⟩
      (earlier.map Prod.snd ++ [ticket]) ⟨some thread, []⟩ := by
  induction earlier generalizing owner with
  | nil => exact .step (mutex_release_handoff owner thread ticket []) .idle
  | cons entry rest ih =>
    obtain ⟨next, wake⟩ := entry
    exact .step (mutex_release_handoff owner next wake (rest ++ [(thread, ticket)])) (ih next)

theorem condition_queued_reacquire (thread signal ticket owner : Nat) (condition : SignalQueue)
    (earlier : List (Nat × Nat)) (posted : signal ∈ condition.posted) (different : owner ≠ thread) :
    let queued := MutexQueue.mk (some owner) (earlier ++ [(thread, ticket)])
    condition_reacquire thread signal ticket condition ⟨some owner, earlier⟩ =
      some (consume_signal condition signal, queued, .wait ticket) ∧
    MutexHandoffs queued (earlier.map Prod.snd ++ [ticket]) ⟨some thread, []⟩ := by
  exact ⟨by simp [condition_reacquire, posted, mutex_acquire, different],
    mutex_handoffs_serve_fifo owner thread ticket earlier⟩

structure JoinState (α : Type) where
  claimant : Option Nat := none
  result : Option α := none
  received : Option (Nat × α) := none

def JoinState.published : JoinState α := ⟨none, none, none⟩

inductive JoinEvent (α : Type) where
  | claim (caller : Nat)
  | finish (result : α)
  | receive (caller : Nat) (result : α)

def JoinEvent.claimant : JoinEvent α → Option Nat
  | .claim caller => some caller
  | _ => none

def JoinEvent.result : JoinEvent α → Option α
  | .finish result => some result
  | _ => none

def JoinEvent.received : JoinEvent α → Option (Nat × α)
  | .receive caller result => some (caller, result)
  | _ => none

inductive JoinStep (child : Nat) : JoinState α → JoinEvent α → JoinState α → Prop where
  | claim : caller ≠ child → before.claimant = none →
      JoinStep child before (.claim caller) { before with claimant := some caller }
  | publish : before.result = none →
      JoinStep child before (.finish result) { before with result := some result }
  | receive : before.claimant = some caller → before.result = some result → before.received = none →
      JoinStep child before (.receive caller result) { before with received := some (caller, result) }

inductive JoinTrace (child : Nat) : JoinState α → List (JoinEvent α) → JoinState α → Prop where
  | empty : JoinTrace child state [] state
  | step : JoinTrace child initial history before → JoinStep child before event after →
      JoinTrace child initial (history ++ [event]) after

def JoinState.valid (child : Nat) (state : JoinState α) : Prop :=
  (∀ caller, state.claimant = some caller → caller ≠ child) ∧
    ∀ caller result, state.received = some (caller, result) →
      state.claimant = some caller ∧ state.result = some result

private theorem join_step_valid (step : JoinStep child before event after) (valid : before.valid child) :
    after.valid child := by
  cases step with
  | claim different absent =>
    constructor
    · intro caller owned
      have same := Option.some.inj owned
      rwa [← same]
    · intro caller result received
      have claimed := (valid.2 caller result received).1
      simp [absent] at claimed
  | publish absent =>
    refine ⟨valid.1, ?_⟩
    intro caller result received
    have finished := (valid.2 caller result received).2
    simp [absent] at finished
  | receive claimed finished _ =>
    refine ⟨valid.1, ?_⟩
    intro caller result received
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj received)
    exact ⟨claimed, finished⟩

theorem join_trace_prefix (history : List (JoinEvent α)) (after : JoinState α)
    (trace : JoinTrace child .published history after) :
    history.filterMap JoinEvent.claimant = after.claimant.toList ∧
      history.filterMap JoinEvent.result = after.result.toList ∧
      history.filterMap JoinEvent.received = after.received.toList ∧ after.valid child := by
  generalize fresh : JoinState.published = initial at trace
  induction trace with
  | empty => subst initial; simp [JoinState.published, JoinState.valid]
  | step _ step prior =>
    obtain ⟨claims, results, receives, valid⟩ := prior
    refine ⟨?_, ?_, ?_, join_step_valid step valid⟩ <;>
      cases step <;> simp_all [JoinEvent.claimant, JoinEvent.result, JoinEvent.received]

theorem join_claim_and_post_commute (before : JoinState α) (caller child : Nat) (result : α)
    (different : caller ≠ child) (unclaimed : before.claimant = none)
    (unfinished : before.result = none) (undelivered : before.received = none) :
    let finished : JoinState α := ⟨some caller, some result, some (caller, result)⟩
    JoinTrace child before [.claim caller, .finish result, .receive caller result] finished ∧
      JoinTrace child before [.finish result, .claim caller, .receive caller result] finished := by
  cases before
  simp only at unclaimed unfinished undelivered
  subst_vars
  exact ⟨.step (.step (.step .empty (.claim different rfl)) (.publish rfl)) (.receive rfl rfl rfl),
    .step (.step (.step .empty (.publish rfl)) (.claim different rfl)) (.receive rfl rfl rfl)⟩

structure JoinCell (α : Type) where
  registered : Bool
  running : Bool
  waiter : Option Nat
  contents : Option α

inductive CellStep (child : Nat) : JoinCell α → JoinEvent α → JoinCell α → Prop where
  | claim : caller ≠ child → CellStep child ⟨true, running, none, contents⟩ (.claim caller)
      ⟨false, running, some caller, contents⟩
  | post : CellStep child ⟨registered, true, waiter, none⟩ (.finish result)
      ⟨registered, false, waiter, some result⟩
  | take : CellStep child ⟨false, running, some caller, some result⟩ (.receive caller result)
      ⟨false, running, none, none⟩

inductive CellView : JoinCell α → JoinState α → Prop where
  | fresh : CellView ⟨true, true, none, none⟩ ⟨none, none, none⟩
  | waiting : CellView ⟨false, true, some caller, none⟩ ⟨some caller, none, none⟩
  | posted : CellView ⟨true, false, none, some result⟩ ⟨none, some result, none⟩
  | ready : CellView ⟨false, false, some caller, some result⟩ ⟨some caller, some result, none⟩
  | taken : CellView ⟨false, false, none, none⟩ ⟨some caller, some result, some (caller, result)⟩

private theorem cell_step_sound (view : CellView cell state) (step : CellStep child cell event next) :
    ∃ after, JoinStep child state event after ∧ CellView next after := by
  cases view <;> cases step
  all_goals first
    | exact ⟨_, .claim (by assumption) rfl, .waiting⟩
    | exact ⟨_, .claim (by assumption) rfl, .ready⟩
    | exact ⟨_, .publish rfl, .posted⟩
    | exact ⟨_, .publish rfl, .ready⟩
    | exact ⟨_, .receive rfl rfl rfl, .taken⟩

private theorem cell_step_complete (view : CellView cell state) (step : JoinStep child state event after) :
    ∃ next, CellStep child cell event next ∧ CellView next after := by
  cases view <;> cases step <;> simp_all
  all_goals first
    | exact ⟨_, .claim (by assumption), .waiting⟩
    | exact ⟨_, .claim (by assumption), .ready⟩
    | exact ⟨_, .post, .posted⟩
    | exact ⟨_, .post, .ready⟩
    | exact ⟨_, .take, .taken⟩

inductive CellTrace (child : Nat) : List (JoinEvent α) → JoinCell α → Prop where
  | empty : CellTrace child [] ⟨true, true, none, none⟩
  | step : CellTrace child history before → CellStep child before event after →
      CellTrace child (history ++ [event]) after

theorem cell_trace_sound (trace : CellTrace child history cell) :
    ∃ state, JoinTrace child .published history state ∧ CellView cell state := by
  induction trace with
  | empty => exact ⟨_, .empty, .fresh⟩
  | step _ step prior =>
    obtain ⟨_, history, view⟩ := prior
    obtain ⟨_, advances, next⟩ := cell_step_sound view step
    exact ⟨_, .step history advances, next⟩

theorem cell_trace_complete (trace : JoinTrace child .published history state) :
    ∃ cell, CellTrace child history cell ∧ CellView cell state := by
  generalize start : JoinState.published = initial at trace
  induction trace with
  | empty => subst initial; exact ⟨_, .empty, .fresh⟩
  | step _ step prior =>
    obtain ⟨_, history, view⟩ := prior
    obtain ⟨_, advances, next⟩ := cell_step_complete view step
    exact ⟨_, .step history advances, next⟩

end Heresy

#print axioms Heresy.condition_enroll_releases_and_keeps_ticket
#print axioms Heresy.condition_and_mutex_updates_share_allocation
#print axioms Heresy.enrolment_survives_trace
#print axioms Heresy.signal_is_available_before_the_receiver_runs
#print axioms Heresy.mutex_acquire_valid
#print axioms Heresy.mutex_release_valid
#print axioms Heresy.mutex_handoff_reserves_ownership
#print axioms Heresy.condition_enrolment_survives_handoff

#print axioms Heresy.condition_queued_reacquire
#print axioms Heresy.join_trace_prefix
#print axioms Heresy.join_claim_and_post_commute
#print axioms Heresy.cell_trace_sound
#print axioms Heresy.cell_trace_complete
