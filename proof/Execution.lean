import Proof

set_option warningAsError true

namespace Heresy

abbrev PartialCalls := Nat → List Int → Option Int

def no_partial_calls : PartialCalls := fun _ _ => none

def collect_arguments : List (Option α) → Option (List α)
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

theorem collect_extends (arguments : List α) (before after : α → Option β)
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

def frame_result : CommandOutcome state → Option Int
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

inductive LoopPhase where
  | test
  | body
  | advance

def LoopPhase.block : LoopPhase → Nat
  | .test => 0
  | .body => 1
  | .advance => 2

inductive LoopFlow (value : Type) where
  | next
  | continue
  | stop
  | returned (result : value)

structure LoopActions (state fault value : Type) where
  test : state → Except fault Bool × state
  body : state → Except fault (LoopFlow value) × state
  advance : state → Except fault Unit × state

abbrev LoopResult (fault value : Type) := Except fault (Option value)

inductive LoopEvaluates (actions : LoopActions state fault value) :
    LoopPhase → state → LoopResult fault value → state → Prop where
  | test_fault : actions.test initial = (.error why, final) → LoopEvaluates actions .test initial (.error why) final
  | test_false : actions.test initial = (.ok false, final) → LoopEvaluates actions .test initial (.ok none) final
  | test_true : actions.test initial = (.ok true, next) → LoopEvaluates actions .body next result final →
      LoopEvaluates actions .test initial result final
  | body_fault : actions.body initial = (.error why, final) → LoopEvaluates actions .body initial (.error why) final
  | body_break : actions.body initial = (.ok .stop, final) → LoopEvaluates actions .body initial (.ok none) final
  | body_return : actions.body initial = (.ok (.returned returned), final) →
      LoopEvaluates actions .body initial (.ok (some returned)) final
  | body_next : actions.body initial = (.ok .next, next) → LoopEvaluates actions .advance next result final →
      LoopEvaluates actions .body initial result final
  | body_continue : actions.body initial = (.ok .continue, next) → LoopEvaluates actions .advance next result final →
      LoopEvaluates actions .body initial result final
  | advance_fault : actions.advance initial = (.error why, final) → LoopEvaluates actions .advance initial (.error why) final
  | advance_next : actions.advance initial = (.ok (), next) → LoopEvaluates actions .test next result final →
      LoopEvaluates actions .advance initial result final

def loop_blocks (actions : LoopActions state fault value) : Blocks state (LoopResult fault value) :=
  fun index initial => match index with
  | 0 => some (match actions.test initial with
    | (.error why, final) => .stop (.error why) final
    | (.ok false, final) => .stop (.ok none) final
    | (.ok true, next) => .jump LoopPhase.body.block next)
  | 1 => some (match actions.body initial with
    | (.error why, final) => .stop (.error why) final
    | (.ok .stop, final) => .stop (.ok none) final
    | (.ok (.returned returned), final) => .stop (.ok (some returned)) final
    | (.ok .next, next) | (.ok .continue, next) => .jump LoopPhase.advance.block next)
  | 2 => some (match actions.advance initial with
    | (.error why, final) => .stop (.error why) final
    | (.ok (), next) => .jump LoopPhase.test.block next)
  | _ => none

private theorem loop_evaluation_compiles (actions : LoopActions state fault value) (phase : LoopPhase)
    (initial final : state) (result : LoopResult fault value) (execution : LoopEvaluates actions phase initial result final) :
    Terminates (loop_blocks actions) phase.block initial result final := by
  induction execution with
  | test_fault observed => exact .stop (by simp [loop_blocks, LoopPhase.block, observed])
  | test_false observed => exact .stop (by simp [loop_blocks, LoopPhase.block, observed])
  | test_true observed _ later => exact .jump (by simp [loop_blocks, LoopPhase.block, observed]) later
  | body_fault observed => exact .stop (by simp [loop_blocks, LoopPhase.block, observed])
  | body_break observed => exact .stop (by simp [loop_blocks, LoopPhase.block, observed])
  | body_return observed => exact .stop (by simp [loop_blocks, LoopPhase.block, observed])
  | body_next observed _ later => exact .jump (by simp [loop_blocks, LoopPhase.block, observed]) later
  | body_continue observed _ later => exact .jump (by simp [loop_blocks, LoopPhase.block, observed]) later
  | advance_fault observed => exact .stop (by simp [loop_blocks, LoopPhase.block, observed])
  | advance_next observed _ later => exact .jump (by simp [loop_blocks, LoopPhase.block, observed]) later

private theorem loop_dispatch_reflects (actions : LoopActions state fault value) (entry : Nat)
    (initial final : state) (result : LoopResult fault value)
    (execution : Terminates (loop_blocks actions) entry initial result final) :
    ∀ phase, phase.block = entry → LoopEvaluates actions phase initial result final := by
  induction execution with
  | @stop entry initial result final edge =>
    rintro phase rfl
    cases phase with
    | test =>
      cases observed : actions.test initial with
      | mk outcome after =>
        cases outcome with
        | error why =>
          simp [loop_blocks, LoopPhase.block, observed] at edge
          obtain ⟨rfl, rfl⟩ := edge
          exact .test_fault observed
        | ok condition =>
          cases condition <;> simp [loop_blocks, LoopPhase.block, observed] at edge
          obtain ⟨rfl, rfl⟩ := edge
          exact .test_false observed
    | body =>
      cases observed : actions.body initial with
      | mk outcome after =>
        cases outcome with
        | error why =>
          simp [loop_blocks, LoopPhase.block, observed] at edge
          obtain ⟨rfl, rfl⟩ := edge
          exact .body_fault observed
        | ok flow =>
          cases flow <;> simp [loop_blocks, LoopPhase.block, observed] at edge
          · obtain ⟨rfl, rfl⟩ := edge
            exact .body_break observed
          · obtain ⟨rfl, rfl⟩ := edge
            exact .body_return observed
    | advance =>
      cases observed : actions.advance initial with
      | mk outcome after =>
        cases outcome with
        | error why =>
          simp [loop_blocks, LoopPhase.block, observed] at edge
          obtain ⟨rfl, rfl⟩ := edge
          exact .advance_fault observed
        | ok _ => simp [loop_blocks, LoopPhase.block, observed] at edge
  | @jump entry initial target after result final edge _ later =>
    rintro phase rfl
    cases phase with
    | test =>
      cases observed : actions.test initial with
      | mk outcome state =>
        cases outcome with
        | error why => simp [loop_blocks, LoopPhase.block, observed] at edge
        | ok condition =>
          cases condition <;> simp [loop_blocks, LoopPhase.block, observed] at edge
          obtain ⟨rfl, rfl⟩ := edge
          exact .test_true observed (later .body rfl)
    | body =>
      cases observed : actions.body initial with
      | mk outcome state =>
        cases outcome with
        | error why => simp [loop_blocks, LoopPhase.block, observed] at edge
        | ok flow =>
          cases flow <;> simp [loop_blocks, LoopPhase.block, observed] at edge
          · obtain ⟨rfl, rfl⟩ := edge
            exact .body_next observed (later .advance rfl)
          · obtain ⟨rfl, rfl⟩ := edge
            exact .body_continue observed (later .advance rfl)
    | advance =>
      cases observed : actions.advance initial with
      | mk outcome state =>
        cases outcome with
        | error why => simp [loop_blocks, LoopPhase.block, observed] at edge
        | ok done =>
          cases done
          simp [loop_blocks, LoopPhase.block, observed] at edge
          obtain ⟨rfl, rfl⟩ := edge
          exact .advance_next observed (later .test rfl)

theorem loop_dispatch_preserves_execution (actions : LoopActions state fault value) (phase : LoopPhase)
    (initial final : state) (result : LoopResult fault value) :
    Terminates (loop_blocks actions) phase.block initial result final ↔ LoopEvaluates actions phase initial result final :=
  ⟨fun execution => loop_dispatch_reflects actions _ _ _ _ execution phase rfl,
    loop_evaluation_compiles actions phase initial final result⟩

def loop_graph (phase : LoopPhase) : DispatchGraph := ⟨phase.block, [[1], [2], [0]]⟩

def loop_actions (actions : LoopActions state fault value) : List (state → Option (Transfer state (LoopResult fault value))) :=
  [loop_blocks actions 0, loop_blocks actions 1, loop_blocks actions 2]

private theorem loop_guard_preserves_blocks (actions : LoopActions state fault value) (phase : LoopPhase) :
    guarded_blocks (loop_graph phase) (loop_actions actions) = loop_blocks actions := by
  funext index initial
  cases index with
  | zero =>
    cases tested : actions.test initial with
    | mk outcome after =>
      cases outcome with
      | error _ => simp [guarded_blocks, loop_graph, loop_actions, loop_blocks, tested]
      | ok result => cases result <;> simp [guarded_blocks, loop_graph, loop_actions, loop_blocks, LoopPhase.block, tested]
  | succ index =>
    cases index with
    | zero =>
      cases evaluated : actions.body initial with
      | mk outcome after =>
        cases outcome with
        | error _ => simp [guarded_blocks, loop_graph, loop_actions, loop_blocks, evaluated]
        | ok flow => cases flow <;> simp [guarded_blocks, loop_graph, loop_actions, loop_blocks, LoopPhase.block, evaluated]
    | succ index =>
      cases index with
      | zero =>
        cases advanced : actions.advance initial with
        | mk outcome after =>
          cases outcome with
          | error _ => simp [guarded_blocks, loop_graph, loop_actions, loop_blocks, advanced]
          | ok done => cases done; simp [guarded_blocks, loop_graph, loop_actions, loop_blocks, LoopPhase.block, advanced]
      | succ index => simp [guarded_blocks, loop_graph, loop_actions, loop_blocks]

theorem guarded_loop_preserves_execution (actions : LoopActions state fault value) (phase : LoopPhase)
    (initial final : state) (result : LoopResult fault value) :
    (∃ fuel, run_blocks (guarded_blocks (loop_graph phase) (loop_actions actions)) fuel (loop_graph phase).entry initial =
      some (result, final)) ↔ LoopEvaluates actions phase initial result final := by
  rw [loop_guard_preserves_blocks]
  exact (run_blocks_correct (loop_blocks actions) phase.block initial final result).trans
    (loop_dispatch_preserves_execution actions phase initial final result)

def RelatedAction (related : source → target → Prop) (left : source → outcome × source)
    (right : target → outcome × target) : Prop :=
  ∀ before initial, related before initial →
    (left before).1 = (right initial).1 ∧ related (left before).2 (right initial).2

structure RelatedLoopActions (related : source → target → Prop) (left : LoopActions source fault value)
    (right : LoopActions target fault value) : Prop where
  test : RelatedAction related left.test right.test
  body : RelatedAction related left.body right.body
  advance : RelatedAction related left.advance right.advance

private theorem RelatedAction.advance (related : source → target → Prop) {left : source → outcome × source}
    {right : target → outcome × target} (corresponds : RelatedAction related left right)
    {before after : source} {initial : target} {result : outcome} (paired : related before initial)
    (executed : left before = (result, after)) :
    ∃ next, right initial = (result, next) ∧ related after next := by
  have crossed := corresponds before initial paired
  rw [executed] at crossed
  exact ⟨(right initial).2, Prod.ext crossed.1.symm rfl, crossed.2⟩

private theorem RelatedAction.swap {related : source → target → Prop} {left : source → outcome × source}
    {right : target → outcome × target} (corresponds : RelatedAction related left right) :
    RelatedAction (fun target source => related source target) right left := by
  intro initial before paired
  have crossed := corresponds before initial paired
  exact ⟨crossed.1.symm, crossed.2⟩

def bind_action (first : state → Except fault α × state)
    (rest : α → state → Except fault β × state) (initial : state) : Except fault β × state :=
  match first initial with
  | (.error why, final) => (.error why, final)
  | (.ok value, next) => rest value next

private theorem RelatedAction.bind {related : source → target → Prop}
    {left : source → Except fault α × source} {right : target → Except fault α × target}
    {then_left : α → source → Except fault β × source} {then_right : α → target → Except fault β × target}
    (first : RelatedAction related left right) (rest : ∀ value, RelatedAction related (then_left value) (then_right value)) :
    RelatedAction related (bind_action left then_left) (bind_action right then_right) := by
  intro before initial paired
  cases executed : left before with
  | mk result after =>
    obtain ⟨next, matched, paired⟩ := first.advance related paired executed
    cases result with
    | error why => simpa [bind_action, executed, matched] using paired
    | ok value => simpa [bind_action, executed, matched] using rest value after next paired

def branch_action (test : state → Except fault Bool × state)
    (yes no : state → Except fault value × state) : state → Except fault value × state :=
  bind_action test (fun result => if result then yes else no)

theorem related_branch_preserves_execution {related : source → target → Prop}
    {source_test : source → Except fault Bool × source} {target_test : target → Except fault Bool × target}
    {source_yes source_no : source → Except fault value × source} {target_yes target_no : target → Except fault value × target}
    (tests : RelatedAction related source_test target_test) (yes : RelatedAction related source_yes target_yes)
    (no : RelatedAction related source_no target_no) :
    RelatedAction related (branch_action source_test source_yes source_no) (branch_action target_test target_yes target_no) := by
  apply tests.bind
  intro result
  cases result
  · exact no
  · exact yes

def logic_action (conjunction : Bool) (left right : state → Except fault Bool × state) :
    state → Except fault Bool × state :=
  bind_action left (fun result => if result = conjunction then right else fun state => (.ok (!conjunction), state))

inductive SharedEvaluates (common : state → Except fault α × state)
    (test : α → state → Except fault Bool × state) (convert : α → state → Except fault β × state)
    (fallback : state → Except fault β × state) : state → Except fault β × state → Prop where
  | common_fault (h : common initial = (.error why, final)) :
      SharedEvaluates common test convert fallback initial (.error why, final)
  | test_fault (h : common initial = (.ok value, next)) (t : test value next = (.error why, final)) :
      SharedEvaluates common test convert fallback initial (.error why, final)
  | reuse (h : common initial = (.ok value, next)) (t : test value next = (.ok true, after)) :
      SharedEvaluates common test convert fallback initial (convert value after)
  | alternate (h : common initial = (.ok value, next)) (t : test value next = (.ok false, after)) :
      SharedEvaluates common test convert fallback initial (fallback after)

theorem shared_conditional_correct (common : state → Except fault α × state)
    (test : α → state → Except fault Bool × state) (convert : α → state → Except fault β × state)
    (fallback : state → Except fault β × state) (initial : state) (result : Except fault β × state) :
    SharedEvaluates common test convert fallback initial result ↔
      bind_action common (fun value => branch_action (test value) (convert value) fallback) initial = result := by
  constructor
  · intro evaluated
    cases evaluated <;> simp_all [branch_action, bind_action]
  · intro evaluated
    subst result
    cases h : common initial with
    | mk outcome next =>
      cases outcome with
      | error why => simpa [bind_action, h] using (SharedEvaluates.common_fault (test := test) (convert := convert) (fallback := fallback) h)
      | ok value =>
        cases t : test value next with
        | mk truth after =>
          cases truth with
          | error why => simpa [bind_action, branch_action, h, t] using (SharedEvaluates.test_fault (convert := convert) (fallback := fallback) h t)
          | ok truth =>
            cases truth with
            | false => simpa [bind_action, branch_action, h, t] using (SharedEvaluates.alternate (convert := convert) (fallback := fallback) h t)
            | true => simpa [bind_action, branch_action, h, t] using (SharedEvaluates.reuse (convert := convert) (fallback := fallback) h t)

theorem related_logic_preserves_execution {related : source → target → Prop} (conjunction : Bool)
    {source_left source_right : source → Except fault Bool × source} {target_left target_right : target → Except fault Bool × target}
    (left : RelatedAction related source_left target_left) (right : RelatedAction related source_right target_right) :
    RelatedAction related (logic_action conjunction source_left source_right) (logic_action conjunction target_left target_right) := by
  apply left.bind
  intro result
  by_cases evaluates : result = conjunction
  · simpa [evaluates] using right
  · intro before initial paired
    simpa [evaluates] using paired

def chain_actions : List (state → Except fault (LoopFlow value) × state) → state → Except fault (LoopFlow value) × state
  | [] => fun initial => (.ok .next, initial)
  | action :: rest => bind_action action (fun
    | .next => chain_actions rest
    | flow => fun initial => (.ok flow, initial))

theorem related_chain_preserves_execution (related : source → target → Prop)
    (actions : List ((source → Except fault (LoopFlow value) × source) × (target → Except fault (LoopFlow value) × target)))
    (corresponds : ∀ action ∈ actions, RelatedAction related action.1 action.2) :
    RelatedAction related (chain_actions (actions.map Prod.fst)) (chain_actions (actions.map Prod.snd)) := by
  induction actions with
  | nil => intro before initial paired; exact ⟨rfl, paired⟩
  | cons first rest induction_rest =>
    have head := corresponds first (by simp)
    have tail := induction_rest (fun action included => corresponds action (List.mem_cons_of_mem _ included))
    apply head.bind
    intro flow
    cases flow
    · exact tail
    all_goals intro before initial paired; exact ⟨rfl, paired⟩

theorem related_loop_actions_preserve_execution (related : source → target → Prop)
    (left : LoopActions source fault value) (right : LoopActions target fault value)
    (actions : RelatedLoopActions related left right) (phase : LoopPhase) (before after : source)
    (result : LoopResult fault value) (execution : LoopEvaluates left phase before result after) :
    ∀ initial, related before initial → ∃ final, LoopEvaluates right phase initial result final ∧ related after final := by
  induction execution with
  | test_fault observed =>
    intro initial paired
    obtain ⟨after, tested, paired⟩ := actions.test.advance related paired observed
    exact ⟨after, .test_fault tested, paired⟩
  | test_false observed =>
    intro initial paired
    obtain ⟨after, tested, paired⟩ := actions.test.advance related paired observed
    exact ⟨after, .test_false tested, paired⟩
  | test_true observed _ later =>
    intro initial paired
    obtain ⟨next, tested, paired⟩ := actions.test.advance related paired observed
    obtain ⟨final, finished, matched⟩ := later next paired
    exact ⟨final, .test_true tested finished, matched⟩
  | body_fault observed =>
    intro initial paired
    obtain ⟨after, executed, paired⟩ := actions.body.advance related paired observed
    exact ⟨after, .body_fault executed, paired⟩
  | body_break observed =>
    intro initial paired
    obtain ⟨after, executed, paired⟩ := actions.body.advance related paired observed
    exact ⟨after, .body_break executed, paired⟩
  | body_return observed =>
    intro initial paired
    obtain ⟨after, executed, paired⟩ := actions.body.advance related paired observed
    exact ⟨after, .body_return executed, paired⟩
  | body_next observed _ later =>
    intro initial paired
    obtain ⟨next, executed, paired⟩ := actions.body.advance related paired observed
    obtain ⟨final, finished, matched⟩ := later next paired
    exact ⟨final, .body_next executed finished, matched⟩
  | body_continue observed _ later =>
    intro initial paired
    obtain ⟨next, executed, paired⟩ := actions.body.advance related paired observed
    obtain ⟨final, finished, matched⟩ := later next paired
    exact ⟨final, .body_continue executed finished, matched⟩
  | advance_fault observed =>
    intro initial paired
    obtain ⟨after, advanced, paired⟩ := actions.advance.advance related paired observed
    exact ⟨after, .advance_fault advanced, paired⟩
  | advance_next observed _ later =>
    intro initial paired
    obtain ⟨next, advanced, paired⟩ := actions.advance.advance related paired observed
    obtain ⟨final, finished, matched⟩ := later next paired
    exact ⟨final, .advance_next advanced finished, matched⟩

theorem guarded_loop_preserves_observations (related : source → target → Prop)
    (left : LoopActions source fault value) (right : LoopActions target fault value)
    (actions : RelatedLoopActions related left right) (phase : LoopPhase) (before : source) (initial : target)
    (paired : related before initial) (observe_source : source → observation) (observe_target : target → observation)
    (agrees : ∀ source target, related source target → observe_source source = observe_target target)
    (result : LoopResult fault value) (observed : observation) :
    (∃ fuel final, run_blocks (guarded_blocks (loop_graph phase) (loop_actions right)) fuel phase.block initial =
      some (result, final) ∧ observe_target final = observed) ↔
    ∃ after, LoopEvaluates left phase before result after ∧ observe_source after = observed := by
  constructor
  · rintro ⟨fuel, final, executed, visible⟩
    have finished := (guarded_loop_preserves_execution right phase initial final result).mp ⟨fuel, executed⟩
    have converse : RelatedLoopActions (fun target source => related source target) right left :=
      ⟨actions.test.swap, actions.body.swap, actions.advance.swap⟩
    obtain ⟨after, evaluated, matched⟩ :=
      related_loop_actions_preserve_execution _ right left converse phase _ _ _ finished before paired
    exact ⟨after, evaluated, (agrees after final matched).trans visible⟩
  · rintro ⟨after, evaluated, visible⟩
    obtain ⟨final, finished, matched⟩ :=
      related_loop_actions_preserve_execution related left right actions phase before after result evaluated initial paired
    obtain ⟨fuel, executed⟩ := (guarded_loop_preserves_execution right phase initial final result).mpr finished
    exact ⟨fuel, final, executed, (agrees after final matched).symm.trans visible⟩

inductive LoopContinues (actions : LoopActions state fault value) : LoopPhase → state → LoopPhase → state → Prop where
  | tested : actions.test initial = (.ok true, after) → LoopContinues actions .test initial .body after
  | completed : actions.body initial = (.ok .next, after) → LoopContinues actions .body initial .advance after
  | continued : actions.body initial = (.ok .continue, after) → LoopContinues actions .body initial .advance after
  | advanced : actions.advance initial = (.ok (), after) → LoopContinues actions .advance initial .test after

inductive LoopPrefix (actions : LoopActions state fault value) (entry : LoopPhase) (initial : state) :
    LoopPhase → state → Prop where
  | entry : LoopPrefix actions entry initial entry initial
  | step : LoopPrefix actions entry initial phase before → LoopContinues actions phase before next after →
      LoopPrefix actions entry initial next after

private theorem related_loop_prefix_step (related : source → target → Prop)
    (left : LoopActions source fault value) (right : LoopActions target fault value)
    (actions : RelatedLoopActions related left right) (entry phase next : LoopPhase) (before after : source) (initial : target)
    (paired : related before initial) (continues : LoopContinues left phase before next after) :
    ∃ final, guarded_blocks (loop_graph entry) (loop_actions right) phase.block initial = some (.jump next.block final) ∧
      related after final := by
  rw [loop_guard_preserves_blocks]
  cases continues with
  | tested observed =>
    obtain ⟨final, tested, matched⟩ := actions.test.advance related paired observed
    exact ⟨final, by simp [loop_blocks, LoopPhase.block, tested], matched⟩
  | completed observed =>
    obtain ⟨final, completed, matched⟩ := actions.body.advance related paired observed
    exact ⟨final, by simp [loop_blocks, LoopPhase.block, completed], matched⟩
  | continued observed =>
    obtain ⟨final, continued, matched⟩ := actions.body.advance related paired observed
    exact ⟨final, by simp [loop_blocks, LoopPhase.block, continued], matched⟩
  | advanced observed =>
    obtain ⟨final, advanced, matched⟩ := actions.advance.advance related paired observed
    exact ⟨final, by simp [loop_blocks, LoopPhase.block, advanced], matched⟩

theorem guarded_loop_preserves_prefix (related : source → target → Prop)
    (left : LoopActions source fault value) (right : LoopActions target fault value)
    (actions : RelatedLoopActions related left right) (entry phase : LoopPhase) (before after : source) (initial : target)
    (paired : related before initial) (visited : LoopPrefix left entry before phase after) :
    ∃ final, DispatchVisits (guarded_blocks (loop_graph entry) (loop_actions right)) entry.block initial phase.block final ∧
      related after final := by
  induction visited with
  | entry => exact ⟨initial, .entry, paired⟩
  | step _ action earlier =>
    obtain ⟨middle, reached, matched⟩ := earlier
    obtain ⟨final, stepped, same⟩ := related_loop_prefix_step related left right actions entry _ _ _ _ middle matched action
    exact ⟨final, .jump reached stepped, same⟩

structure SwitchEntry where
  bounds : Option (Int × Int)
  target : Nat

def switch_matches (selector : Int) (entry : SwitchEntry) : Bool :=
  match entry.bounds with
  | none => false
  | some (lower, upper) => decide (lower ≤ selector ∧ selector ≤ upper)

def switch_search (selector : Int) : Option Nat → List SwitchEntry → Option Nat
  | fallback, [] => fallback
  | fallback, entry :: rest =>
    match entry.bounds with
    | none => switch_search selector (some entry.target) rest
    | some _ => if switch_matches selector entry then some entry.target else switch_search selector fallback rest

def last_switch_default : List SwitchEntry → Option Nat
  | [] => none
  | entry :: rest =>
    (last_switch_default rest).or (if entry.bounds.isNone then some entry.target else none)

theorem switch_search_preserves_selection (selector : Int) (fallback : Option Nat) (entries : List SwitchEntry) :
    switch_search selector fallback entries =
      ((entries.find? (switch_matches selector)).map SwitchEntry.target).or ((last_switch_default entries).or fallback) := by
  induction entries generalizing fallback with
  | nil => rfl
  | cons entry rest later =>
    cases bounds : entry.bounds with
    | none =>
      simp [switch_search, switch_matches, bounds, last_switch_default, later]
    | some pair =>
      by_cases matched : switch_matches selector entry = true
      · simp [switch_search, bounds, matched]
      · simp [switch_search, bounds, matched, last_switch_default, later]

theorem switch_search_lists_target (selector : Int) (fallback : Option Nat) (entries : List SwitchEntry)
    (target : Nat) (selected : switch_search selector fallback entries = some target) :
    fallback = some target ∨ ∃ entry ∈ entries, entry.target = target := by
  induction entries generalizing fallback with
  | nil => exact .inl selected
  | cons entry rest later =>
    cases bounds : entry.bounds with
    | none =>
      simp only [switch_search, bounds] at selected
      rcases later (some entry.target) selected with first | ⟨chosen, present, target_eq⟩
      · exact .inr ⟨entry, by simp, Option.some.inj first⟩
      · exact .inr ⟨chosen, List.mem_cons_of_mem _ present, target_eq⟩
    | some span =>
      by_cases matched : switch_matches selector entry = true
      · simp [switch_search, bounds, matched] at selected
        exact .inr ⟨entry, by simp, selected⟩
      · simp [switch_search, bounds, matched] at selected
        rcases later fallback selected with first | ⟨chosen, present, target_eq⟩
        · exact .inl first
        · exact .inr ⟨chosen, List.mem_cons_of_mem _ present, target_eq⟩

theorem guarded_switch_accepts_selection (graph : DispatchGraph)
    (actions : List (state → Option (Transfer state result))) (shape : graph.successors.length = actions.length)
    (selector : Int) (fallback : Option Nat) (entries : List SwitchEntry) (index selected : Nat) (initial : state)
    (row : List Nat) (action : state → Option (Transfer state result))
    (installed : (graph.successors.zip actions)[index]? = some (row, action))
    (listed : ∀ target, (fallback = some target ∨ ∃ entry ∈ entries, entry.target = target) → target ∈ row)
    (chosen : switch_search selector fallback entries = some selected)
    (jump : action initial = some (.jump selected initial)) :
    guarded_blocks graph actions index initial = some (.jump selected initial) := by
  have present := listed selected (switch_search_lists_target selector fallback entries selected chosen)
  simp [guarded_blocks, shape, installed, jump, present]

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
#print axioms Heresy.loop_dispatch_preserves_execution
#print axioms Heresy.guarded_loop_preserves_execution
#print axioms Heresy.guarded_loop_preserves_observations
#print axioms Heresy.guarded_loop_preserves_prefix
#print axioms Heresy.related_branch_preserves_execution
#print axioms Heresy.shared_conditional_correct
#print axioms Heresy.related_logic_preserves_execution
#print axioms Heresy.related_chain_preserves_execution
#print axioms Heresy.switch_search_preserves_selection
#print axioms Heresy.guarded_switch_accepts_selection
