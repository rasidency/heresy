import Proof

set_option warningAsError true

namespace Heresy

abbrev PartialCalls := Nat → List Int → Option Int

def no_partial_calls : PartialCalls := fun _ _ => none

private def collect_arguments : List (Option α) → Option (List α)
  | [] => some []
  | first :: rest => do
    let value ← first
    let remainder ← collect_arguments rest
    pure (value :: remainder)

def OptionExtends (before after : Option α) : Prop :=
  ∀ value, before = some value → after = some value

private theorem option_same (value : Option α) : OptionExtends value value := fun _ observed => observed

private theorem option_map_extends (transform : α → β) (before after : Option α)
    (refinement : OptionExtends before after) : OptionExtends (transform <$> before) (transform <$> after) := by
  cases before with
  | none => simp [OptionExtends]
  | some value =>
    have same := refinement value rfl
    subst after
    exact option_same _

private theorem option_bind_extends (before after : Option α) (first second : α → Option β)
    (refinement : OptionExtends before after) (next : ∀ value, OptionExtends (first value) (second value)) :
    OptionExtends (before >>= first) (after >>= second) := by
  cases before with
  | none => simp [OptionExtends]
  | some value =>
    have same := refinement value rfl
    subst after
    exact next value

private theorem collect_extends (arguments : List α) (before after : α → Option β)
    (refinement : ∀ argument ∈ arguments, OptionExtends (before argument) (after argument)) :
    OptionExtends (collect_arguments (arguments.map before)) (collect_arguments (arguments.map after)) := by
  induction arguments with
  | nil => exact option_same _
  | cons first rest remaining =>
    simp only [List.map_cons, collect_arguments]
    apply option_bind_extends _ _ _ _ (refinement first (by simp))
    intro value
    apply option_bind_extends _ _ _ _ (remaining (fun argument present => refinement argument (by simp [present])))
    intro _
    exact option_same _

def CallsExtend (before after : PartialCalls) : Prop :=
  ∀ slot arguments, OptionExtends (before slot arguments) (after slot arguments)

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

theorem source_expression_extends (before after : PartialCalls) (links : CallsExtend before after)
    (locals : Locals) (expression : Source) :
    OptionExtends (source_expression before locals expression) (source_expression after locals expression) := by
  induction expression using Source.induct with
  | literal => simp only [source_expression]; exact option_same _
  | param => simp only [source_expression]; exact option_same _
  | binary operator left right first second =>
    simp only [source_expression]
    apply option_bind_extends _ _ _ _ first
    intro x
    apply option_bind_extends _ _ _ _ second
    intro y
    exact option_same (some (unsigned 64 (operate operator x y)))
  | conditional condition yes no test chosen alternative =>
    simp only [source_expression]
    apply option_bind_extends _ _ _ _ test
    intro guard
    by_cases taken : guard = 0
    · simpa only [taken, if_true] using alternative
    · simpa only [taken, if_false] using chosen
  | invoke slot arguments each =>
    simp only [source_expression]
    exact option_bind_extends _ _ _ _ (collect_extends arguments _ _ each) (links slot)

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

theorem run_command_extends (view : state → Locals) (write : state → Nat → Int → state)
    (before after : expr → Locals → Option Int)
    (expressions : ∀ value locals, OptionExtends (before value locals) (after value locals))
    (smaller larger : Nat) (more : smaller ≤ larger) (body : Command expr) (initial : state) :
    OptionExtends (run_command view write smaller (body.map before) initial)
      (run_command view write larger (body.map after) initial) := by
  induction smaller generalizing larger body initial with
  | zero => simp [run_command, OptionExtends]
  | succ fuel recurse =>
    cases larger with
    | zero => omega
    | succ larger =>
      have allowed : fuel ≤ larger := by omega
      cases body with
      | skip => exact option_same _
      | store slot value =>
        simp only [Command.map, run_command]
        exact option_map_extends _ _ _ (expressions value (view initial))
      | result value =>
        simp only [Command.map, run_command]
        exact option_map_extends _ _ _ (expressions value (view initial))
      | sequence first second =>
        simp only [Command.map, run_command]
        apply option_bind_extends _ _ _ _ (recurse larger allowed first initial)
        intro step
        cases step with
        | next updated => exact recurse larger allowed second updated
        | returned value => exact option_same _
      | select condition yes no =>
        simp only [Command.map, run_command]
        apply option_bind_extends _ _ _ _ (expressions condition (view initial))
        intro test
        by_cases zero : test = 0
        · simpa only [zero, if_true] using recurse larger allowed no initial
        · simpa only [zero, if_false] using recurse larger allowed yes initial
      | loop condition body =>
        simp only [Command.map, run_command]
        apply option_bind_extends _ _ _ _ (expressions condition (view initial))
        intro test
        by_cases zero : test = 0
        · simp only [zero, if_true]
          exact option_same _
        · simp only [zero, if_false]
          apply option_bind_extends _ _ _ _ (recurse larger allowed body initial)
          intro iteration
          cases iteration with
          | next updated => exact recurse larger allowed (.loop condition body) updated
          | returned value => exact option_same _

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

theorem initialise_frame_read (start : Nat) (values : List Int) (initial : Locals) (index : Nat) :
    initialise_frame write_local start values initial index =
      if index < start then initial index else (values[index - start]?).getD (initial index) := by
  induction values generalizing start initial with
  | nil => simp [initialise_frame]
  | cons value rest bound =>
    rw [initialise_frame, bound]
    by_cases earlier : index < start
    · have earlier_next : index < start + 1 := by omega
      have different : index ≠ start := by omega
      simp [earlier, earlier_next, write_local, different]
    · by_cases equal : index = start
      · subst index
        simp [write_local]
      · have later : ¬ index < start + 1 := by omega
        have displacement : index - start = index - (start + 1) + 1 := by omega
        simp [earlier, later, displacement, List.getElem?_cons_succ, write_local, equal]

theorem sparse_frame_binds (values : List Int) :
    read_sparse (initialise_frame write_sparse 0 values ∅) = arguments_view values := by
  rw [initialise_frame_projects read_sparse write_sparse sparse_write_refines, sparse_empty]
  funext index
  simp [initialise_frame_read, arguments_view]

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

theorem source_links_extend (helpers : List (Helper (Command Source))) (smaller larger : Nat)
    (more : smaller ≤ larger) (slot : Nat) (before after : PartialCalls) (extension : CallsExtend before after) :
    CallsExtend (link_frames source_expression id write_local (fun _ => 0) smaller slot helpers before)
      (link_frames source_expression id write_local (fun _ => 0) larger slot helpers after) := by
  induction helpers generalizing slot before after with
  | nil => exact extension
  | cons helper rest recurse =>
    simp only [link_frames]
    apply recurse
    intro requested values
    by_cases current : requested = slot
    · simp only [current, if_true]
      apply option_bind_extends _ _ _ _ (run_command_extends id write_local
        (fun expression locals => source_expression before locals expression)
        (fun expression locals => source_expression after locals expression)
        (fun expression locals => source_expression_extends before after extension locals expression)
        smaller larger more helper.body (initialise_frame write_local 0 values (fun _ => 0)))
      intro observed
      exact option_same (frame_result observed)
    · simpa only [current, if_false] using extension requested values

theorem source_exit_extends (helpers : List (Helper (Command Source))) (body : Command Source)
    (smaller larger : Nat) (more : smaller ≤ larger) :
    OptionExtends (source_exit helpers body smaller) (source_exit helpers body larger) := by
  simp only [source_exit]
  apply option_map_extends
  apply run_command_extends id write_local _ _ _ smaller larger more body (fun _ => 0)
  intro expression locals
  apply source_expression_extends
  exact source_links_extend helpers smaller larger more 0 _ _ (fun _ _ => option_same _)

theorem framed_exit_unique (helpers : List (Helper (Command Source))) (body : Command Source)
    (first_fuel second_fuel : Nat) (first second : Int)
    (run_first : source_exit helpers body first_fuel = some first)
    (run_second : source_exit helpers body second_fuel = some second) : first = second := by
  have first_observed := source_exit_extends helpers body first_fuel (max first_fuel second_fuel) (Nat.le_max_left _ _) first run_first
  have second_observed := source_exit_extends helpers body second_fuel (max first_fuel second_fuel) (Nat.le_max_right _ _) second run_second
  exact Option.some.inj (first_observed.symm.trans second_observed)

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

def recursive_calls (evaluate : PartialCalls → Locals → expr → Option Int) (view : state → Locals)
    (write : state → Nat → Int → state) (empty : state) (helpers : Array (Helper (Command expr))) :
    Nat → PartialCalls
  | 0 => no_partial_calls
  | fuel + 1 => fun slot values =>
    match helpers[slot]? with
    | none => none
    | some helper =>
      if values.length = helper.arity then
        let prior := recursive_calls evaluate view write empty helpers fuel
        let command := helper.body.map (fun expression locals => evaluate prior locals expression)
        (run_command view write (fuel + 1) command (initialise_frame write 0 values empty)).bind frame_result
      else none

theorem recursive_calls_correct (helpers : Array (Helper (Command Source))) (fuel : Nat) :
    recursive_calls target_expression read_sparse write_sparse ∅ (helpers.map lower_frame) fuel =
      recursive_calls source_expression id write_local (fun _ => 0) helpers fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel rest =>
    funext slot values
    simp only [recursive_calls, Array.getElem?_map, rest]
    cases found : helpers[slot]? with
    | none => rfl
    | some helper =>
      simp only [Option.map_some, lower_frame, partial_commands_lower]
      split
      · have projected := run_command_projects read_sparse write_sparse sparse_write_refines (fuel + 1)
          (helper.body.map (fun expression locals =>
            source_expression (recursive_calls source_expression id write_local (fun _ => 0) helpers fuel) locals expression))
          (initialise_frame write_sparse 0 values ∅)
        rw [initialise_frame_projects read_sparse write_sparse sparse_write_refines, sparse_empty] at projected
        rw [← projected, frame_result_projects]
      · rfl

theorem recursive_calls_extend (helpers : Array (Helper (Command Source))) (smaller larger : Nat) (more : smaller ≤ larger) :
    CallsExtend (recursive_calls source_expression id write_local (fun _ => 0) helpers smaller)
      (recursive_calls source_expression id write_local (fun _ => 0) helpers larger) := by
  induction smaller generalizing larger with
  | zero =>
    intro slot values
    simp [recursive_calls, no_partial_calls, OptionExtends]
  | succ fuel recurse =>
    cases larger with
    | zero => omega
    | succ larger =>
      have earlier := recurse larger (by omega)
      intro slot values
      simp only [recursive_calls]
      cases found : helpers[slot]? with
      | none => exact option_same _
      | some helper =>
        by_cases arity : values.length = helper.arity
        · simp only [arity, if_true]
          apply option_bind_extends _ _ _ _ (run_command_extends id write_local
            (fun expression locals => source_expression
              (recursive_calls source_expression id write_local (fun _ => 0) helpers fuel) locals expression)
            (fun expression locals => source_expression
              (recursive_calls source_expression id write_local (fun _ => 0) helpers larger) locals expression)
            (fun expression locals => source_expression_extends _ _ earlier locals expression)
            (fuel + 1) (larger + 1) more helper.body (initialise_frame write_local 0 values (fun _ => 0)))
          intro result
          exact option_same (frame_result result)
        · simpa only [arity, if_false] using option_same (none : Option Int)

def recursive_source_exit (helpers : Array (Helper (Command Source))) (body : Command Source) (fuel : Nat) : Option Int :=
  let calls := recursive_calls source_expression id write_local (fun _ => 0) helpers fuel
  let outcome := run_command id write_local fuel (body.map (fun expression locals => source_expression calls locals expression))
    (fun _ => 0)
  outcome.map (fun result => unsigned 8 (signed 32 result.value))

theorem recursive_source_exit_extends (helpers : Array (Helper (Command Source))) (body : Command Source)
    (smaller larger : Nat) (more : smaller ≤ larger) :
    OptionExtends (recursive_source_exit helpers body smaller) (recursive_source_exit helpers body larger) := by
  simp only [recursive_source_exit]
  apply option_map_extends
  apply run_command_extends id write_local _ _ _ smaller larger more body (fun _ => 0)
  intro expression locals
  exact source_expression_extends _ _ (recursive_calls_extend helpers smaller larger more) locals expression

def recursive_target_exit (helpers : Array (Helper (Command Target))) (body : Command Target) (fuel : Nat) : Option Int :=
  let calls := recursive_calls target_expression read_sparse write_sparse ∅ helpers fuel
  let outcome := run_command read_sparse write_sparse fuel
    (body.map (fun expression locals => target_expression calls locals expression)) ∅
  outcome.map (fun result => unsigned 8 result.value)

theorem recursive_exit_correct (helpers : Array (Helper (Command Source))) (body : Command Source) (fuel : Nat) :
    recursive_target_exit (helpers.map lower_frame) (body.map lower) fuel = recursive_source_exit helpers body fuel := by
  simp only [recursive_target_exit, recursive_source_exit, recursive_calls_correct, partial_commands_lower, exit_status_truncation]
  let calls := recursive_calls source_expression id write_local (fun _ => 0) helpers fuel
  let command := body.map (fun expression locals => source_expression calls locals expression)
  have projected := run_command_projects read_sparse write_sparse sparse_write_refines fuel command ∅
  rw [sparse_empty] at projected
  rw [← projected]
  cases run_command read_sparse write_sparse fuel command ∅ with
  | none => rfl
  | some result => cases result <;> rfl

theorem recursive_observations_correct (helpers : Array (Helper (Command Source))) (body : Command Source) (status : Int) :
    (∃ fuel, recursive_target_exit (helpers.map lower_frame) (body.map lower) fuel = some status) ↔
      ∃ fuel, recursive_source_exit helpers body fuel = some status := by
  simp only [recursive_exit_correct]

end Heresy

#print axioms Heresy.framed_link_correct
#print axioms Heresy.framed_exit_correct
#print axioms Heresy.run_returns_value
#print axioms Heresy.sparse_frame_binds
#print axioms Heresy.source_exit_extends
#print axioms Heresy.framed_exit_unique
#print axioms Heresy.recursive_calls_correct
#print axioms Heresy.recursive_source_exit_extends
#print axioms Heresy.recursive_observations_correct
