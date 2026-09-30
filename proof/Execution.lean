import Proof

set_option warningAsError true

namespace Heresy

abbrev PartialCalls := Nat → List Int → Option Int

def no_partial_calls : PartialCalls := fun _ _ => none

private def collect_arguments : List (Option α) → Option (List α)
  | [] => some []
  | first :: rest => List.cons <$> first <*> collect_arguments rest

def source_expression (calls : PartialCalls) (locals : Locals) : Source → Option Int
  | .constant value => some value
  | .parameter index => some (locals index)
  | .binary operator left right => do
    let left ← source_expression calls locals left
    let right ← source_expression calls locals right
    pure (unsigned 64 (operate operator left right))
  | .conditional condition yes no => do
    let test ← source_expression calls locals condition
    if test = 0 then source_expression calls locals no else source_expression calls locals yes
  | .invoke slot arguments => do
    let values ← collect_arguments (arguments.map (source_expression calls locals))
    calls slot values

def target_expression (calls : PartialCalls) (locals : Locals) : Target → Option Int
  | .constant value => some value
  | .parameter index => some (locals index)
  | .binary operator left right => do
    let left ← target_expression calls locals left
    let right ← target_expression calls locals right
    pure (operate operator left right)
  | .wrap width body => unsigned width <$> target_expression calls locals body
  | .conditional condition yes no => do
    let test ← target_expression calls locals condition
    if test = 0 then target_expression calls locals no else target_expression calls locals yes
  | .invoke slot arguments => do
    let values ← collect_arguments (arguments.map (target_expression calls locals))
    calls slot values

theorem partial_expression_lower (calls : PartialCalls) (locals : Locals) (expression : Source) :
    target_expression calls locals (lower expression) = source_expression calls locals expression := by
  induction expression using Source.induct with
  | literal value => simp only [lower, source_expression, target_expression]
  | param index => simp only [lower, source_expression, target_expression]
  | binary operator left right first second =>
    simp only [lower, source_expression, target_expression, first, second]
    cases source_expression calls locals left <;> cases source_expression calls locals right <;> rfl
  | conditional condition yes no tested chosen alternative =>
    simp only [lower, source_expression, target_expression, tested, chosen, alternative]
  | invoke slot arguments each =>
    simp only [lower, source_expression, target_expression, List.map_map, Function.comp_def]
    rw [List.map_congr_left each]

def run_command (view : state → Locals) (write : state → Nat → Int → state) :
    Nat → Command (Locals → Option Int) → state → Option (CommandOutcome state)
  | 0, _, _ => none
  | _ + 1, .skip, initial => some (.next initial)
  | _ + 1, .store slot value, initial =>
    (fun output => .next (write initial slot output)) <$> value (view initial)
  | _ + 1, .result value, initial => .returned <$> value (view initial)
  | fuel + 1, .sequence first second, initial => do
    match ← run_command view write fuel first initial with
    | .next updated => run_command view write fuel second updated
    | .returned value => pure (.returned value)
  | fuel + 1, .select condition yes no, initial => do
    let test ← condition (view initial)
    run_command view write fuel (if test = 0 then no else yes) initial
  | fuel + 1, .loop condition body, initial => do
    let test ← condition (view initial)
    if test = 0 then pure (.next initial)
    else
      match ← run_command view write fuel body initial with
      | .next updated => run_command view write fuel (.loop condition body) updated
      | .returned value => pure (.returned value)

def returns_value : Command expr → Bool
  | .result _ => true
  | .sequence first second => returns_value first || returns_value second
  | .select _ yes no => returns_value yes && returns_value no
  | _ => false

theorem run_returns_value (view : state → Locals) (write : state → Nat → Int → state)
    (fuel : Nat) (body : Command (Locals → Option Int)) (initial : state) (outcome : CommandOutcome state)
    (requires_return : returns_value body = true) (observed : run_command view write fuel body initial = some outcome) :
    ∃ value, outcome = .returned value := by
  induction fuel generalizing body initial outcome with
  | zero => simp [run_command] at observed
  | succ fuel shorter =>
    cases body with
    | skip => simp [returns_value] at requires_return
    | store slot value => simp [returns_value] at requires_return
    | loop guard iteration => simp [returns_value] at requires_return
    | result expression =>
      cases result : expression (view initial) with
      | none => simp [run_command, result] at observed
      | some value =>
        simp [run_command, result] at observed
        exact ⟨value, observed.symm⟩
    | sequence first second =>
      cases current : run_command view write fuel first initial with
      | none => simp [run_command, current] at observed
      | some completed =>
        cases completed with
        | returned value =>
          simp [run_command, current] at observed
          exact ⟨value, observed.symm⟩
        | next updated =>
          simp only [returns_value, Bool.or_eq_true] at requires_return
          rcases requires_return with from_first | from_second
          · obtain ⟨_, contradiction⟩ := shorter first initial _ from_first current
            cases contradiction
          · apply shorter second updated _ from_second
            simpa [run_command, current] using observed
    | select condition yes no =>
      simp only [returns_value, Bool.and_eq_true] at requires_return
      cases tested : condition (view initial) with
      | none => simp [run_command, tested] at observed
      | some value =>
        by_cases zero : value = 0
        · apply shorter no initial _ requires_return.2
          simpa [run_command, tested, zero] using observed
        · apply shorter yes initial _ requires_return.1
          simpa [run_command, tested, zero] using observed

theorem returns_value_map (body : Command α) (transform : α → β) :
    returns_value (body.map transform) = returns_value body := by
  induction body <;> simp_all [Command.map, returns_value]

theorem run_command_projects (view : state → Locals) (write : state → Nat → Int → state)
    (writes : ∀ initial index value, view (write initial index value) = write_local (view initial) index value)
    (fuel : Nat) (body : Command (Locals → Option Int)) (initial : state) :
    (run_command view write fuel body initial).map (CommandOutcome.project view) =
      run_command id write_local fuel body (view initial) := by
  induction fuel generalizing body initial with
  | zero => rfl
  | succ fuel project_run =>
    cases body with
    | skip => rfl
    | store slot value =>
      simp only [run_command, id_eq]
      cases value (view initial) with
      | none => rfl
      | some result => simp [Option.map, CommandOutcome.project, writes]
    | result value =>
      simp only [run_command, id_eq]
      cases value (view initial) <;> rfl
    | sequence first second =>
      have first_run := (project_run first initial).symm
      simp only [run_command, first_run]
      cases step : run_command view write fuel first initial with
      | none => rfl
      | some observed =>
        cases observed with
        | next updated => exact project_run second updated
        | returned value => rfl
    | select condition yes no =>
      simp only [run_command, id_eq]
      cases condition (view initial) with
      | none => rfl
      | some test => exact project_run (if test = 0 then no else yes) initial
    | loop condition body =>
      have iteration := (project_run body initial).symm
      simp only [run_command, id_eq, iteration]
      cases condition (view initial) with
      | none => rfl
      | some test =>
        by_cases finished : test = 0
        · simp [finished, CommandOutcome.project]
        · simp [finished]
          cases step : run_command view write fuel body initial with
          | none => rfl
          | some observed =>
            cases observed with
            | next updated => exact project_run (.loop condition body) updated
            | returned value => rfl

def initialise_frame (write : state → Nat → Int → state) : Nat → List Int → state → state
  | _, [], initial => initial
  | index, value :: rest, initial => initialise_frame write (index + 1) rest (write initial index value)

theorem initialise_frame_projects (view : state → Locals) (write : state → Nat → Int → state)
    (writes : ∀ initial index value, view (write initial index value) = write_local (view initial) index value)
    (index : Nat) (values : List Int) (initial : state) :
    view (initialise_frame write index values initial) =
      initialise_frame write_local index values (view initial) := by
  induction values generalizing index initial with
  | nil => rfl
  | cons value rest other => simp only [initialise_frame, other, writes]

private def frame_result : CommandOutcome state → Option Int
  | .returned value => some value
  | .next _ => none

private theorem frame_result_projects (view : state → Locals) (outcome : Option (CommandOutcome state)) :
    (outcome.map (CommandOutcome.project view)).bind frame_result = outcome.bind frame_result := by
  cases outcome with
  | none => rfl
  | some result => cases result <;> rfl

def link_frames (evaluate : PartialCalls → Locals → expr → Option Int) (view : state → Locals)
    (write : state → Nat → Int → state) (empty : state) (fuel : Nat) :
    Nat → List (Helper (Command expr)) → PartialCalls → PartialCalls
  | _, [], calls => calls
  | slot, helper :: rest, calls =>
    let initial := initialise_frame write 0
    let command := helper.body.map (fun expression locals => evaluate calls locals expression)
    let implementation := fun values => (run_command view write fuel command (initial values empty)).bind frame_result
    let extended := fun requested values => if requested = slot then implementation values else calls requested values
    link_frames evaluate view write empty fuel (slot + 1) rest extended

def lower_frame (helper : Helper (Command Source)) : Helper (Command Target) :=
  ⟨helper.arity, helper.body.map lower⟩

theorem partial_commands_lower (calls : PartialCalls) (body : Command Source) :
    (body.map lower).map (fun expression locals => target_expression calls locals expression) =
      body.map (fun expression locals => source_expression calls locals expression) := by
  have expression (node : Source) :
      (fun locals => target_expression calls locals (lower node)) = (fun locals => source_expression calls locals node) :=
    funext (fun locals => partial_expression_lower calls locals node)
  induction body <;> simp only [Command.map, expression] at * <;> simp_all

theorem framed_link_correct (helpers : List (Helper (Command Source))) (fuel slot : Nat) (calls : PartialCalls) :
    link_frames target_expression read_sparse write_sparse ∅ fuel slot (helpers.map lower_frame) calls =
      link_frames source_expression id write_local (fun _ => 0) fuel slot helpers calls := by
  induction helpers generalizing slot calls with
  | nil => rfl
  | cons helper rest after =>
    simp only [List.map_cons, link_frames, lower_frame, partial_commands_lower]
    rw [after]
    congr 1
    funext requested arguments
    by_cases current : requested = slot
    · simp only [current, if_true]
      have projected := run_command_projects read_sparse write_sparse sparse_write_refines fuel
        (helper.body.map (fun expression locals => source_expression calls locals expression))
        (initialise_frame write_sparse 0 arguments ∅)
      rw [initialise_frame_projects read_sparse write_sparse sparse_write_refines, sparse_empty] at projected
      rw [← projected, frame_result_projects]
    · simp [current]

def source_exit (helpers : List (Helper (Command Source))) (body : Command Source) (fuel : Nat) : Option Int :=
  let calls := link_frames source_expression id write_local (fun _ => 0) fuel 0 helpers no_partial_calls
  let outcome := run_command id write_local fuel (body.map (fun expression locals => source_expression calls locals expression))
    (fun _ => 0)
  outcome.map (fun result => unsigned 8 (signed 32 result.value))

def target_exit (helpers : List (Helper (Command Target))) (body : Command Target) (fuel : Nat) : Option Int :=
  let calls := link_frames target_expression read_sparse write_sparse ∅ fuel 0 helpers no_partial_calls
  let outcome := run_command read_sparse write_sparse fuel
    (body.map (fun expression locals => target_expression calls locals expression)) ∅
  outcome.map (fun result => unsigned 8 result.value)

theorem framed_exit_correct (helpers : List (Helper (Command Source))) (body : Command Source) (fuel : Nat) :
    target_exit (helpers.map lower_frame) (body.map lower) fuel = source_exit helpers body fuel := by
  simp only [target_exit, source_exit, framed_link_correct, partial_commands_lower, exit_status_truncation]
  let calls := link_frames source_expression id write_local (fun _ => 0) fuel 0 helpers no_partial_calls
  let command := body.map (fun expression locals => source_expression calls locals expression)
  have projected := run_command_projects read_sparse write_sparse sparse_write_refines fuel command ∅
  rw [sparse_empty] at projected
  rw [← projected]
  cases run_command read_sparse write_sparse fuel command ∅ with
  | none => rfl
  | some result => cases result <;> rfl

theorem framed_observations_correct (helpers : List (Helper (Command Source))) (body : Command Source) (status : Int) :
    (∃ fuel, target_exit (helpers.map lower_frame) (body.map lower) fuel = some status) ↔
      ∃ fuel, source_exit helpers body fuel = some status := by
  simp only [framed_exit_correct]

end Heresy

#print axioms Heresy.framed_link_correct
#print axioms Heresy.framed_exit_correct
#print axioms Heresy.run_returns_value
