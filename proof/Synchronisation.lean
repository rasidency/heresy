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

end Heresy

#print axioms Heresy.condition_enroll_releases_and_keeps_ticket
#print axioms Heresy.condition_and_mutex_updates_share_allocation
#print axioms Heresy.enrolment_survives_trace
#print axioms Heresy.signal_is_available_before_the_receiver_runs
