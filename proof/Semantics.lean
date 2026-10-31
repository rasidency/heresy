import Execution

set_option warningAsError true

namespace Heresy

abbrev Procedures := Array (Helper (Command Source))

inductive Evaluation where
  | expression (state : Locals) (expression : Source) (value : Int)
  | arguments (state : Locals) (arguments : List Source) (values : List Int)
  | command (state : Locals) (body : Command Source) (outcome : CommandOutcome Locals)
  | application (slot : Nat) (values : List Int) (value : Int)

inductive Evaluates (helpers : Procedures) : Evaluation → Prop where
  | literal : Evaluates helpers (.expression locals (.constant value) value)
  | local_value : Evaluates helpers (.expression locals (.parameter index) (locals index))
  | binary : Evaluates helpers (.expression locals left lhs) → Evaluates helpers (.expression locals right rhs) →
      Evaluates helpers (.expression locals (.binary operator left right) (unsigned 64 (operate operator lhs rhs)))
  | conditional_yes : Evaluates helpers (.expression locals test condition) → condition ≠ 0 →
      Evaluates helpers (.expression locals yes value) → Evaluates helpers (.expression locals (.conditional test yes no) value)
  | conditional_no : Evaluates helpers (.expression locals test 0) →
      Evaluates helpers (.expression locals no value) → Evaluates helpers (.expression locals (.conditional test yes no) value)
  | invoke : Evaluates helpers (.arguments locals args values) → Evaluates helpers (.application slot values output) →
      Evaluates helpers (.expression locals (.invoke slot args) output)
  | no_arguments : Evaluates helpers (.arguments locals [] [])
  | more_arguments : Evaluates helpers (.expression locals first value) → Evaluates helpers (.arguments locals rest others) →
      Evaluates helpers (.arguments locals (first :: rest) (value :: others))
  | apply_helper : helpers[slot]? = some helper → values.length = helper.arity →
      Evaluates helpers (.command (initialise_frame write_local 0 values (fun _ => 0)) helper.body (.returned result)) →
      Evaluates helpers (.application slot values result)
  | skip : Evaluates helpers (.command locals .skip (.next locals))
  | store : Evaluates helpers (.expression locals expression value) →
      Evaluates helpers (.command locals (.store slot expression) (.next (write_local locals slot value)))
  | result : Evaluates helpers (.expression locals expression value) →
      Evaluates helpers (.command locals (.result expression) (.returned value))
  | sequence_next : Evaluates helpers (.command locals first (.next updated)) →
      Evaluates helpers (.command updated second outcome) → Evaluates helpers (.command locals (.sequence first second) outcome)
  | sequence_returned : Evaluates helpers (.command locals first (.returned value)) →
      Evaluates helpers (.command locals (.sequence first second) (.returned value))
  | select_yes : Evaluates helpers (.expression locals test condition) → condition ≠ 0 →
      Evaluates helpers (.command locals yes outcome) → Evaluates helpers (.command locals (.select test yes no) outcome)
  | select_no : Evaluates helpers (.expression locals test 0) →
      Evaluates helpers (.command locals no outcome) → Evaluates helpers (.command locals (.select test yes no) outcome)
  | loop_done : Evaluates helpers (.expression locals test 0) →
      Evaluates helpers (.command locals (.loop test body) (.next locals))
  | loop_next : Evaluates helpers (.expression locals test condition) → condition ≠ 0 →
      Evaluates helpers (.command locals body (.next updated)) → Evaluates helpers (.command updated (.loop test body) outcome) →
      Evaluates helpers (.command locals (.loop test body) outcome)
  | loop_returned : Evaluates helpers (.expression locals test condition) → condition ≠ 0 →
      Evaluates helpers (.command locals body (.returned value)) →
      Evaluates helpers (.command locals (.loop test body) (.returned value))

private def table (helpers : Procedures) (fuel : Nat) : PartialCalls :=
  recursive_calls source_expression id write_local (fun _ => 0) helpers fuel

private def execute (calls : PartialCalls) (fuel : Nat) (locals : Locals) (body : Command Source) :
    Option (CommandOutcome Locals) :=
  run_command id write_local fuel (body.map (fun expression frame => source_expression calls frame expression)) locals

private def approximation (helpers : Procedures) (fuel : Nat) : Evaluation → Prop
  | .expression locals expression value => source_expression (table helpers fuel) locals expression = some value
  | .arguments locals expressions values =>
    collect_arguments (expressions.map (source_expression (table helpers fuel) locals)) = some values
  | .application slot values result => table helpers fuel slot values = some result
  | .command locals body outcome => execute (table helpers fuel) fuel locals body = some outcome

private theorem approximation_extends (helpers : Procedures) (goal : Evaluation) (smaller larger : Nat)
    (more : smaller ≤ larger) (observed : approximation helpers smaller goal) :
    approximation helpers larger goal := by
  have calls := recursive_calls_extend helpers smaller larger more
  cases goal with
  | expression locals expression value =>
    exact source_expression_extends _ _ calls locals expression value observed
  | arguments locals expressions values =>
    exact collect_extends expressions _ _ (fun expression _ => source_expression_extends _ _ calls locals expression) values observed
  | application slot values result => exact calls slot values result observed
  | command locals body outcome =>
    exact run_command_extends id write_local
      (fun expression frame => source_expression (table helpers smaller) frame expression)
      (fun expression frame => source_expression (table helpers larger) frame expression)
      (fun expression frame => source_expression_extends _ _ calls frame expression) smaller larger more body locals outcome observed

private theorem arguments_sound (helpers : Procedures) (locals : Locals) (read : Source → Option Int)
    (arguments : List Source) (values : List Int) (observed : collect_arguments (arguments.map read) = some values)
    (sound : ∀ expression ∈ arguments, ∀ value, read expression = some value →
      Evaluates helpers (.expression locals expression value)) : Evaluates helpers (.arguments locals arguments values) := by
  induction arguments generalizing values with
  | nil =>
    simp [collect_arguments] at observed
    cases observed
    exact .no_arguments
  | cons first rest later =>
    cases current : read first with
    | none => simp [collect_arguments, current] at observed
    | some value =>
      cases remaining : collect_arguments (rest.map read) with
      | none => simp [collect_arguments, current, remaining] at observed
      | some values =>
        simp [collect_arguments, current, remaining] at observed
        cases observed
        exact .more_arguments (sound first (by simp) value current)
          (later values remaining (fun expression present => sound expression (by simp [present])))

private theorem expression_sound (helpers : Procedures) (calls : PartialCalls) (locals : Locals)
    (call_sound : ∀ slot values result, calls slot values = some result → Evaluates helpers (.application slot values result))
    (expression : Source) (value : Int) (observed : source_expression calls locals expression = some value) :
    Evaluates helpers (.expression locals expression value) := by
  induction expression using Source.induct generalizing value with
  | literal value =>
    simp [source_expression] at observed
    cases observed
    exact .literal
  | param index =>
    simp [source_expression] at observed
    cases observed
    exact .local_value
  | binary operator left right first second =>
    cases left_result : source_expression calls locals left with
    | none => simp [source_expression, left_result] at observed
    | some lhs =>
      cases right_result : source_expression calls locals right with
      | none => simp [source_expression, left_result, right_result] at observed
      | some rhs =>
        simp [source_expression, left_result, right_result] at observed
        cases observed
        exact .binary (first lhs left_result) (second rhs right_result)
  | conditional test yes no guard chosen alternative =>
    cases test_result : source_expression calls locals test with
    | none => simp [source_expression, test_result] at observed
    | some condition =>
      by_cases zero : condition = 0
      · cases zero
        exact .conditional_no (guard 0 test_result) (alternative value (by simpa [source_expression, test_result] using observed))
      · exact .conditional_yes (guard condition test_result) zero
          (chosen value (by simpa [source_expression, test_result, zero] using observed))
  | invoke slot arguments each =>
    cases bound : collect_arguments (arguments.map (source_expression calls locals)) with
    | none => simp [source_expression, bound] at observed
    | some values =>
      exact .invoke (arguments_sound helpers locals _ arguments values bound each)
        (call_sound slot values value (by simpa [source_expression, bound] using observed))

private theorem command_sound (helpers : Procedures) (calls : PartialCalls)
    (call_sound : ∀ slot values result, calls slot values = some result → Evaluates helpers (.application slot values result))
    (fuel : Nat) (body : Command Source) (locals : Locals) (outcome : CommandOutcome Locals)
    (observed : execute calls fuel locals body = some outcome) : Evaluates helpers (.command locals body outcome) := by
  induction fuel generalizing body locals outcome with
  | zero => simp [execute, run_command] at observed
  | succ fuel recurse =>
    cases body with
    | skip =>
      simp [execute] at observed
      cases observed
      exact .skip
    | store slot expression =>
      cases value : source_expression calls locals expression with
      | none => simp [execute, Command.map, run_command, value] at observed
      | some stored =>
        simp [execute, Command.map, run_command, value] at observed
        cases observed
        exact .store (expression_sound helpers calls locals call_sound _ stored value)
    | result expression =>
      cases value : source_expression calls locals expression with
      | none => simp [execute, Command.map, run_command, value] at observed
      | some returned =>
        simp [execute, Command.map, run_command, value] at observed
        cases observed
        exact .result (expression_sound helpers calls locals call_sound _ returned value)
    | sequence first second =>
      cases before : execute calls fuel locals first with
      | none =>
        unfold execute at before
        simp [execute, Command.map, run_command, before] at observed
      | some current =>
        have steps := recurse first locals current before
        unfold execute at before
        cases current with
        | returned value =>
          simp [execute, Command.map, run_command, before] at observed
          cases observed
          exact .sequence_returned steps
        | next updated =>
          exact .sequence_next steps (recurse second updated outcome (by
            simpa [execute, Command.map, run_command, before] using observed))
    | select test yes no =>
      cases tested : source_expression calls locals test with
      | none => simp [execute, Command.map, run_command, tested] at observed
      | some condition =>
        by_cases zero : condition = 0
        · cases zero
          exact .select_no (expression_sound helpers calls locals call_sound _ 0 tested)
            (recurse no locals outcome (by simpa [execute, Command.map, run_command, tested] using observed))
        · exact .select_yes (expression_sound helpers calls locals call_sound _ condition tested) zero
            (recurse yes locals outcome (by simpa [execute, Command.map, run_command, tested, zero] using observed))
    | loop test body =>
      cases tested : source_expression calls locals test with
      | none => simp [execute, Command.map, run_command, tested] at observed
      | some condition =>
        by_cases zero : condition = 0
        · cases zero
          simp [execute, Command.map, run_command, tested] at observed
          cases observed
          exact .loop_done (expression_sound helpers calls locals call_sound _ 0 tested)
        · cases iteration : execute calls fuel locals body with
          | none =>
            unfold execute at iteration
            simp [execute, Command.map, run_command, tested, zero, iteration] at observed
          | some current =>
            have steps := recurse body locals current iteration
            have guard := expression_sound helpers calls locals call_sound _ condition tested
            unfold execute at iteration
            cases current with
            | returned value =>
              simp [execute, Command.map, run_command, tested, zero, iteration] at observed
              cases observed
              exact .loop_returned guard zero steps
            | next updated =>
              exact .loop_next guard zero steps (recurse (.loop test body) updated outcome (by
                simpa [execute, Command.map, run_command, tested, zero, iteration] using observed))

private theorem table_sound (helpers : Procedures) (fuel slot : Nat) (values : List Int) (result : Int)
    (observed : table helpers fuel slot values = some result) : Evaluates helpers (.application slot values result) := by
  induction fuel generalizing slot values result with
  | zero => simp [table, recursive_calls, no_partial_calls] at observed
  | succ fuel smaller =>
    simp only [table, recursive_calls] at observed
    cases found : helpers[slot]? with
    | none => simp [found] at observed
    | some helper =>
      simp only [found] at observed
      split at observed
      · rename_i arity
        let locals := initialise_frame write_local 0 values (fun _ => 0)
        cases running : execute (table helpers fuel) (fuel + 1) locals helper.body with
        | none => simp [execute, table, locals] at running; simp [running] at observed
        | some flow =>
          have derived := command_sound helpers (table helpers fuel) smaller (fuel + 1) helper.body locals flow running
          simp [execute, table, locals] at running
          cases flow with
          | next updated => simp [running, frame_result] at observed
          | returned value =>
            simp [running, frame_result] at observed
            cases observed
            exact .apply_helper found arity derived
      · simp at observed

theorem approximation_sound (helpers : Procedures) (fuel : Nat) (goal : Evaluation)
    (observed : approximation helpers fuel goal) : Evaluates helpers goal := by
  have calls := table_sound helpers fuel
  cases goal with
  | expression locals expression value => exact expression_sound helpers _ locals calls expression value observed
  | arguments locals expressions values =>
    exact arguments_sound helpers locals _ expressions values observed
      (fun expression _ value evaluated => expression_sound helpers _ locals calls expression value evaluated)
  | command locals body outcome => exact command_sound helpers _ calls fuel body locals outcome observed
  | application slot values result => exact calls slot values result observed

private theorem common_fuel (helpers : Procedures) (one two : Evaluation)
    (first : ∃ fuel, approximation helpers fuel one) (second : ∃ fuel, approximation helpers fuel two) :
    ∃ fuel, approximation helpers fuel one ∧ approximation helpers fuel two := by
  obtain ⟨left, observed_left⟩ := first
  obtain ⟨right, observed_right⟩ := second
  exact ⟨max left right,
    approximation_extends helpers one left _ (Nat.le_max_left _ _) observed_left,
    approximation_extends helpers two right _ (Nat.le_max_right _ _) observed_right⟩

private theorem execute_extends (helpers : Procedures) (earlier_calls later_calls before after : Nat)
    (calls : earlier_calls ≤ later_calls) (steps : before ≤ after) (locals : Locals) (body : Command Source) :
    OptionExtends (execute (table helpers earlier_calls) before locals body)
      (execute (table helpers later_calls) after locals body) :=
  run_command_extends id write_local
    (fun expression frame => source_expression (table helpers earlier_calls) frame expression)
    (fun expression frame => source_expression (table helpers later_calls) frame expression)
    (fun expression frame => source_expression_extends _ _ (recursive_calls_extend helpers earlier_calls later_calls calls) frame expression)
    before after steps body locals

private theorem advance_calls (helpers : Procedures) (fuel : Nat) (locals : Locals) (body : Command Source)
    (outcome : CommandOutcome Locals) (observed : approximation helpers fuel (.command locals body outcome)) :
    execute (table helpers (fuel + 1)) fuel locals body = some outcome :=
  execute_extends helpers fuel (fuel + 1) fuel fuel (Nat.le_succ _) (Nat.le_refl _) locals body outcome observed

theorem approximation_complete (helpers : Procedures) (goal : Evaluation) (derivation : Evaluates helpers goal) :
    ∃ fuel, approximation helpers fuel goal := by
  induction derivation with
  | literal => exact ⟨0, by simp [approximation, source_expression]⟩
  | local_value => exact ⟨0, by simp [approximation, source_expression]⟩
  | binary _ _ left right =>
    obtain ⟨fuel, lhs, rhs⟩ := common_fuel helpers _ _ left right
    simp only [approximation] at lhs rhs
    exact ⟨fuel, by simp [approximation, source_expression, lhs, rhs]⟩
  | conditional_yes _ nonzero _ tested chosen =>
    obtain ⟨fuel, guard, taken⟩ := common_fuel helpers _ _ tested chosen
    simp only [approximation] at guard taken
    exact ⟨fuel, by simp [approximation, source_expression, guard, nonzero, taken]⟩
  | conditional_no _ _ tested chosen =>
    obtain ⟨fuel, guard, taken⟩ := common_fuel helpers _ _ tested chosen
    simp only [approximation] at guard taken
    exact ⟨fuel, by simp [approximation, source_expression, guard, taken]⟩
  | invoke _ _ arguments called =>
    obtain ⟨fuel, inputs, result⟩ := common_fuel helpers _ _ arguments called
    simp only [approximation] at inputs result
    exact ⟨fuel, by simp [approximation, source_expression, inputs, result]⟩
  | no_arguments => exact ⟨0, by simp [approximation, collect_arguments]⟩
  | more_arguments _ _ head tail =>
    obtain ⟨fuel, first, rest⟩ := common_fuel helpers _ _ head tail
    simp only [approximation] at first rest
    exact ⟨fuel, by simp [approximation, collect_arguments, first, rest]⟩
  | apply_helper found arity _ evaluated =>
    obtain ⟨fuel, observed⟩ := evaluated
    have advanced := execute_extends helpers fuel fuel fuel (fuel + 1) (Nat.le_refl _) (Nat.le_succ _) _ _ _ observed
    unfold execute table at advanced
    exact ⟨fuel + 1, by simp [approximation, table, recursive_calls, found, arity, advanced, frame_result]⟩
  | skip => exact ⟨1, by simp [approximation, execute, Command.map, run_command]⟩
  | store _ evaluated =>
    obtain ⟨fuel, observed⟩ := evaluated
    have advanced := approximation_extends helpers _ fuel (fuel + 1) (Nat.le_succ _) observed
    simp only [approximation] at advanced
    exact ⟨fuel + 1, by simp [approximation, execute, Command.map, run_command, advanced]⟩
  | result _ evaluated =>
    obtain ⟨fuel, observed⟩ := evaluated
    have advanced := approximation_extends helpers _ fuel (fuel + 1) (Nat.le_succ _) observed
    simp only [approximation] at advanced
    exact ⟨fuel + 1, by simp [approximation, execute, Command.map, run_command, advanced]⟩
  | sequence_next _ _ first second =>
    obtain ⟨fuel, beginning, suffix⟩ := common_fuel helpers _ _ first second
    have beginning := advance_calls helpers fuel _ _ _ beginning
    have suffix := advance_calls helpers fuel _ _ _ suffix
    unfold execute at beginning suffix
    exact ⟨fuel + 1, by simp [approximation, execute, Command.map, run_command, beginning, suffix]⟩
  | sequence_returned _ first =>
    obtain ⟨fuel, beginning⟩ := first
    have beginning := advance_calls helpers fuel _ _ _ beginning
    unfold execute at beginning
    exact ⟨fuel + 1, by simp [approximation, execute, Command.map, run_command, beginning]⟩
  | select_yes _ nonzero _ tested chosen =>
    obtain ⟨fuel, guard, taken⟩ := common_fuel helpers _ _ tested chosen
    have guard := approximation_extends helpers _ fuel (fuel + 1) (Nat.le_succ _) guard
    have taken := advance_calls helpers fuel _ _ _ taken
    simp only [approximation] at guard
    unfold execute at taken
    exact ⟨fuel + 1, by simp [approximation, execute, Command.map, run_command, guard, nonzero, taken]⟩
  | select_no _ _ tested chosen =>
    obtain ⟨fuel, guard, taken⟩ := common_fuel helpers _ _ tested chosen
    have guard := approximation_extends helpers _ fuel (fuel + 1) (Nat.le_succ _) guard
    have taken := advance_calls helpers fuel _ _ _ taken
    simp only [approximation] at guard
    unfold execute at taken
    exact ⟨fuel + 1, by simp [approximation, execute, Command.map, run_command, guard, taken]⟩
  | loop_done _ tested =>
    obtain ⟨fuel, guard⟩ := tested
    have guard := approximation_extends helpers _ fuel (fuel + 1) (Nat.le_succ _) guard
    simp only [approximation] at guard
    exact ⟨fuel + 1, by simp [approximation, execute, Command.map, run_command, guard]⟩
  | loop_next _ nonzero _ _ tested current repeated =>
    obtain ⟨first, guard, iteration⟩ := common_fuel helpers _ _ tested current
    obtain ⟨second, remainder⟩ := repeated
    let fuel := max first second
    have guard := approximation_extends helpers _ first (fuel + 1)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)) guard
    have iteration := advance_calls helpers fuel _ _ _
      (approximation_extends helpers _ first fuel (Nat.le_max_left _ _) iteration)
    have remainder := advance_calls helpers fuel _ _ _
      (approximation_extends helpers _ second fuel (Nat.le_max_right _ _) remainder)
    simp only [approximation] at guard
    unfold execute at iteration remainder
    simp only [Command.map] at remainder
    exact ⟨fuel + 1, by simp [approximation, execute, Command.map, run_command, guard, nonzero, iteration, remainder]⟩
  | loop_returned _ nonzero _ tested current =>
    obtain ⟨fuel, guard, iteration⟩ := common_fuel helpers _ _ tested current
    have guard := approximation_extends helpers _ fuel (fuel + 1) (Nat.le_succ _) guard
    have iteration := advance_calls helpers fuel _ _ _ iteration
    simp only [approximation] at guard
    unfold execute at iteration
    exact ⟨fuel + 1, by simp [approximation, execute, Command.map, run_command, guard, nonzero, iteration]⟩

def source_observes_exit (helpers : Procedures) (body : Command Source) (status : Int) : Prop :=
  ∃ outcome, Evaluates helpers (.command (fun _ => 0) body outcome) ∧
    unsigned 8 (signed 32 outcome.value) = status

theorem recursive_source_adequate (helpers : Procedures) (body : Command Source) (status : Int) :
    (∃ fuel, recursive_source_exit helpers body fuel = some status) ↔ source_observes_exit helpers body status := by
  constructor
  · rintro ⟨fuel, result⟩
    change (execute (table helpers fuel) fuel (fun _ => 0) body).map
      (fun outcome => unsigned 8 (signed 32 outcome.value)) = some status at result
    cases run : execute (table helpers fuel) fuel (fun _ => 0) body with
    | none => simp [run] at result
    | some outcome =>
      exact ⟨outcome, approximation_sound helpers fuel _ run, by simpa [run] using result⟩
  · rintro ⟨outcome, execution, status_eq⟩
    obtain ⟨fuel, run⟩ := approximation_complete helpers _ execution
    refine ⟨fuel, ?_⟩
    change (execute (table helpers fuel) fuel (fun _ => 0) body).map
      (fun outcome => unsigned 8 (signed 32 outcome.value)) = some status
    change execute (table helpers fuel) fuel (fun _ => 0) body = some outcome at run
    simp [run, status_eq]

theorem recursive_target_refines (helpers : Procedures) (body : Command Source) (status : Int) :
    (∃ fuel, recursive_target_exit (helpers.map lower_frame) (body.map lower) fuel = some status) ↔
      source_observes_exit helpers body status :=
  (recursive_observations_correct helpers body status).trans (recursive_source_adequate helpers body status)

inductive ProcessOutcome where
  | returned (value : Int)
  | finished (status : Int)
  | transfer
  | panic (message : String) (recent : List String) (tracing : Bool)

inductive ProcessEvent where
  | close (handle : Nat)
  | flush_stdout
  | stderr (text : String)
  | exit (status : Int)
  deriving DecidableEq

def process_exit (value : Int) : ProcessOutcome := .finished (unsigned 8 value)

def process_report : ProcessOutcome → List ProcessEvent
  | .returned value => [.exit (unsigned 8 value)]
  | .finished code => [.exit code]
  | .transfer => [.stderr "heresy panic: control transfer escaped its function", .exit 70]
  | .panic message recent tracing =>
    [.stderr ("heresy panic: " ++ message)] ++
    (if tracing || recent.isEmpty then [] else [.stderr (String.intercalate "\n" recent.reverse)]) ++ [.exit 70]

def process_epilogue (handles : List Nat) (outcome : ProcessOutcome) : List ProcessEvent :=
  handles.map .close ++ .flush_stdout :: process_report outcome

theorem process_return (handles : List Nat) (value : Int) :
    process_epilogue handles (.returned value) = process_epilogue handles (process_exit (signed 32 value)) := by
  simp [process_epilogue, process_exit, process_report, exit_status_truncation]

theorem process_closes_then_flushes (handles : List Nat) (outcome : ProcessOutcome) :
    (process_epilogue handles outcome).take (handles.length + 1) = handles.map .close ++ [.flush_stdout] ∧
    (process_epilogue handles outcome).drop (handles.length + 1) = process_report outcome := by
  simp [process_epilogue, List.take_append, List.drop_append]
  exact List.take_of_length_le (by simp)

theorem process_exit_is_final (handles : List Nat) (outcome : ProcessOutcome) :
    ∃ status earlier, process_epilogue handles outcome = earlier ++ [.exit status] ∧
      ∀ code, ProcessEvent.exit code ∉ earlier := by
  cases outcome with
  | returned value =>
    exact ⟨unsigned 8 value, handles.map .close ++ [.flush_stdout], by simp [process_epilogue, process_report, List.append_assoc],
      by simp⟩
  | finished status =>
    exact ⟨status, handles.map .close ++ [.flush_stdout], by simp [process_epilogue, process_report, List.append_assoc],
      by simp⟩
  | transfer =>
    exact ⟨70, handles.map .close ++ [.flush_stdout, .stderr "heresy panic: control transfer escaped its function"],
      by simp [process_epilogue, process_report, List.append_assoc], by simp⟩
  | panic message recent tracing =>
    by_cases immediate : (tracing || recent.isEmpty) = true
    · exact ⟨70, handles.map .close ++ [.flush_stdout, .stderr ("heresy panic: " ++ message)],
        by simp [process_epilogue, process_report, immediate, List.append_assoc], by simp⟩
    · exact ⟨70, handles.map .close ++ [.flush_stdout, .stderr ("heresy panic: " ++ message),
          .stderr (String.intercalate "\n" recent.reverse)],
        by simp [process_epilogue, process_report, immediate, List.append_assoc], by simp⟩

structure StreamToken where
  ident : Nat
  address : Int

structure StreamTable (α : Type) where
  next : Nat
  handles : Nat → Option α

def stream_address (ident : Nat) : Int := 4611686018427387904 + ident

def stream_lookup (table : StreamTable α) (token : StreamToken) : Option α :=
  if token.address = stream_address token.ident then table.handles token.ident else none

def register_stream (table : StreamTable α) (handle : α) : Option (StreamToken × StreamTable α) :=
  if table.next < 4611686018427387904 then
    let key := table.next
    some (⟨key, stream_address key⟩, ⟨key + 1, fun ident => if ident = key then some handle else table.handles ident⟩)
  else none

def unregister_stream (table : StreamTable α) (token : StreamToken) : Option (StreamTable α) :=
  match stream_lookup table token with
  | none => none
  | some _ => some { table with handles := fun ident => if ident = token.ident then none else table.handles ident }

def StreamTable.valid (table : StreamTable α) : Prop :=
  ∀ ident handle, table.handles ident = some handle → ident < table.next

theorem registered_stream_address_range (table after : StreamTable α) (handle : α) (token : StreamToken)
    (registered : register_stream table handle = some (token, after)) :
    token.address = stream_address token.ident ∧
      4611686018427387904 ≤ token.address ∧ token.address < 9223372036854775808 := by
  by_cases fits : table.next < 4611686018427387904
  · simp [register_stream, fits] at registered
    obtain ⟨rfl, _⟩ := registered
    change _ ∧ 4611686018427387904 ≤ stream_address table.next ∧ stream_address table.next < 9223372036854775808
    exact ⟨rfl, by unfold stream_address; omega, by unfold stream_address; omega⟩
  · simp [register_stream, fits] at registered

inductive StreamStep : StreamTable α → StreamTable α → Prop where
  | opened : register_stream before handle = some (token, after) → StreamStep before after
  | closed : unregister_stream before token = some after → StreamStep before after

theorem stream_step_preserves_valid (before after : StreamTable α) (step : StreamStep before after)
    (valid : before.valid) : after.valid := by
  intro ident handle found
  cases step with
  | opened registered =>
    by_cases fits : before.next < 4611686018427387904
    · simp [register_stream, fits] at registered
      obtain ⟨_, rfl⟩ := registered
      by_cases allocated : ident = before.next
      · simp [allocated]
      · have earlier := valid ident handle (by simpa [allocated] using found)
        exact Nat.lt_succ_of_lt earlier
    · simp [register_stream, fits] at registered
  | closed unregistered =>
    rename_i token
    cases lookup : stream_lookup before token with
    | none => simp [unregister_stream, lookup] at unregistered
    | some previous =>
      simp [unregister_stream, lookup] at unregistered
      subst after
      by_cases erased : ident = token.ident
      · simp [erased] at found
      · exact valid ident handle (by simpa [erased] using found)

theorem stream_step_preserves_retired (before after : StreamTable α) (step : StreamStep before after)
    (ident : Nat) (retired : ident < before.next ∧ before.handles ident = none) :
    ident < after.next ∧ after.handles ident = none := by
  cases step with
  | opened registered =>
    by_cases fits : before.next < 4611686018427387904
    · simp [register_stream, fits] at registered
      obtain ⟨_, rfl⟩ := registered
      exact ⟨Nat.lt_succ_of_lt retired.1, by simp [Nat.ne_of_lt retired.1, retired.2]⟩
    · simp [register_stream, fits] at registered
  | closed unregistered =>
    rename_i token
    cases found : stream_lookup before token with
    | none => simp [unregister_stream, found] at unregistered
    | some handle =>
      simp [unregister_stream, found] at unregistered
      subst after
      exact ⟨retired.1, by simp [retired.2]⟩

inductive StreamTrace : StreamTable α → StreamTable α → Prop where
  | start : StreamTrace state state
  | step : StreamTrace before middle → StreamStep middle after → StreamTrace before after

theorem stream_trace_valid (after : StreamTable α)
    (trace : StreamTrace ⟨1, fun _ => none⟩ after) : after.valid := by
  induction trace with
  | start => intro ident handle found; contradiction
  | step _ action earlier => exact stream_step_preserves_valid _ _ action earlier

theorem closed_stream_stays_invalid (before closed after : StreamTable α) (token alias : StreamToken)
    (valid : before.valid) (same : alias.ident = token.ident) (success : unregister_stream before token = some closed)
    (trace : StreamTrace closed after) : stream_lookup after alias = none := by
  have initially_retired : token.ident < closed.next ∧ closed.handles token.ident = none := by
    cases found : stream_lookup before token with
    | none => simp [unregister_stream, found] at success
    | some handle =>
      have looked_up : before.handles token.ident = some handle := by
        unfold stream_lookup at found
        split at found <;> simp_all
      simp [unregister_stream, found] at success
      subst closed
      exact ⟨valid _ _ looked_up, by simp⟩
  have still_retired : token.ident < after.next ∧ after.handles token.ident = none := by
    induction trace with
    | start => exact initially_retired
    | step _ action earlier => exact stream_step_preserves_retired _ _ action _ earlier
  simp [stream_lookup, same, still_retired.2]

theorem wrong_stream_address_is_rejected (table : StreamTable α) (token : StreamToken)
    (invalid : token.address ≠ stream_address token.ident) : stream_lookup table token = none := by
  simp [stream_lookup, invalid]

end Heresy

#print axioms Heresy.approximation_sound
#print axioms Heresy.approximation_complete
#print axioms Heresy.recursive_target_refines
#print axioms Heresy.process_return
#print axioms Heresy.process_closes_then_flushes
#print axioms Heresy.process_exit_is_final
#print axioms Heresy.closed_stream_stays_invalid
#print axioms Heresy.wrong_stream_address_is_rejected
#print axioms Heresy.stream_trace_valid
#print axioms Heresy.registered_stream_address_range
