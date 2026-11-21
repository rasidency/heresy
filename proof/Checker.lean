import Lean.Data.Json
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Semantics
import Containers
import Synchronisation
import Runtime
import Ordinary
import Surface
import Native
import Schedule

set_option warningAsError true

open Lean

namespace Heresy

def validates_kernel (expression : Source) (body : String) : Bool :=
  body == render_target (lower expression)

theorem kernel_certificate_sound (expression : Source) (body : String)
    (accepted : validates_kernel expression body = true) :
    ∃ target : Target, body = render_target target ∧
      ∀ parameters, target_eval parameters target = source_eval parameters expression := by
  refine ⟨lower expression, ?_, lower_correct expression⟩
  simpa [validates_kernel] using accepted

private def json_field (node : Json) (key : String) : Json :=
  (node.getObjVal? key).toOption.getD .null

private def field_text (node : Json) (key : String) : String :=
  (json_field node key).getStr?.toOption.getD ""

private def child_nodes (node : Json) : List Json :=
  ((json_field node "inner").getArr?.toOption.getD #[]).toList

private def qualified_spelling (type : Json) : String :=
  let canonical := field_text type "desugaredQualType"
  let written := field_text type "qualType"
  let nestedTag := ["struct", "union"].any fun tag =>
    canonical.startsWith (tag ++ " ") && (canonical.splitOn "::(unnamed at ").length == 2 &&
      written.startsWith (tag ++ " @") && (written.drop (tag.length + 2)).toNat?.isSome
  if canonical.isEmpty || nestedTag then written else canonical

private def type_spelling (node : Json) : String :=
  qualified_spelling (json_field node "type")

private def require (candidate : Option α) (message : String) : Except String α :=
  candidate.elim (.error message) .ok

private def read_operator : String → Except String Operator
  | "+" => .ok .add
  | "-" => .ok .sub
  | "*" => .ok .mul
  | "&" => .ok .band
  | "|" => .ok .bor
  | "^" => .ok .bxor
  | other => .error ("unsupported kernel operator " ++ other)

private def direct_callee : Nat → Json → String
  | 0, _ => ""
  | depth + 1, node =>
    match field_text node "kind", child_nodes node with
    | "DeclRefExpr", [] =>
      let declaration := json_field node "referencedDecl"
      if field_text declaration "kind" == "FunctionDecl" then field_text declaration "name" else ""
    | "ParenExpr", [child] => direct_callee depth child
    | "ImplicitCastExpr", [child] =>
      if field_text node "castKind" == "FunctionToPointerDecay" then direct_callee depth child else ""
    | _, _ => ""

private abbrev HelperScope := String → Option (Nat × Nat)

private def read_expression (lookup_helper : HelperScope) (lookup_slot : String → Option Nat) :
    Nat → Json → Except String Source
  | 0, _ => .error "incomplete kernel expression"
  | depth + 1, node => do
    unless type_spelling node == "unsigned long" do
      throw "kernel expression requires unsigned long"
    match field_text node "kind", child_nodes node with
    | "IntegerLiteral", [] =>
      let value ← require (field_text node "value").toInt? "invalid kernel constant"
      if 0 ≤ value ∧ value < modulus 64 then pure (.constant value)
      else throw "kernel constant exceeds 64 bits"
    | "DeclRefExpr", [] =>
      let ident := field_text (json_field node "referencedDecl") "id"
      let index ← require (lookup_slot ident) "expression references external or uninitialised state"
      pure (.parameter index)
    | "ParenExpr", [child] => read_expression lookup_helper lookup_slot depth child
    | "ImplicitCastExpr", [child] =>
      unless field_text node "castKind" == "LValueToRValue" ||
          field_text node "castKind" == "NoOp" do
        throw "kernel cast changes the value"
      read_expression lookup_helper lookup_slot depth child
    | "BinaryOperator", [left, right] =>
      .binary <$> read_operator (field_text node "opcode")
              <*> read_expression lookup_helper lookup_slot depth left
              <*> read_expression lookup_helper lookup_slot depth right
    | "ConditionalOperator", [condition, yes, no] =>
      .conditional <$> read_expression lookup_helper lookup_slot depth condition
                   <*> read_expression lookup_helper lookup_slot depth yes <*> read_expression lookup_helper lookup_slot depth no
    | "CallExpr", target :: arguments =>
      let (slot, arity) ← require (lookup_helper (direct_callee depth target)) "call requires an available unsigned long helper"
      unless arity == arguments.length do
        throw "closed helper call has the wrong arity"
      .invoke slot <$> arguments.mapM (read_expression lookup_helper lookup_slot depth)
    | _, _ => throw "unsupported kernel expression"

private def hex_binding (stem name : String) : String :=
  let digits := "0123456789abcdef".toList.toArray
  name.toUTF8.toList.foldl (fun symbol byte =>
    (symbol.push digits[byte.toNat / 16]!).push digits[byte.toNat % 16]!) (stem ++ "_")

private def kernel_symbol := hex_binding "k"

private def haskell_quote (name : String) : String := Ordinary.quote_bytes name.toUTF8.toList

private def source_declaration (node : Json) : Bool :=
  let origin := json_field node "loc"
  let expansion := json_field origin "expansionLoc"
  let location := if expansion == .null then origin else expansion
  json_field location "offset" != .null && json_field location "includedFrom" == .null

private def unit_namespace (count index : Nat) : String :=
  if count > 1 then "unit:" ++ toString index ++ ":" else ""

private def unit_function_declarations (tree : Json) : List Json :=
  (child_nodes tree).filter (fun node => source_declaration node && field_text node "kind" == "FunctionDecl")

private def function_definitions (nodes : List Json) : List Json :=
  nodes.filter (fun node => (child_nodes node).any (fun body => field_text body "kind" == "CompoundStmt"))

private def unit_function_key (unit_name : String) (declarations : List Json) (name : String) : String :=
  if declarations.any (fun node => field_text node "storageClass" == "static" && field_text node "name" == name)
  then unit_name ++ name else name

private def unit_entries (unit_name : String) (tree : Json) : List (String × String) :=
  let functions := unit_function_declarations tree
  (function_definitions functions).map (fun node =>
    let key := unit_function_key unit_name functions (field_text node "name")
    (key, hex_binding "f" key))

def link_entries (trees : List Json) : List (String × String) :=
  (trees.zipIdx).flatMap (fun (tree, index) => unit_entries (unit_namespace trees.length index) tree)

private def object_definitions (tree : Json) : List Json :=
  let candidates := (child_nodes tree).filter (fun node => source_declaration node && field_text node "kind" == "VarDecl" &&
    (field_text node "storageClass" != "extern" || !(field_text node "init").isEmpty))
  candidates.foldl (fun retained node =>
    let name := field_text node "name"
    if (field_text node "init").isEmpty &&
        retained.any (fun previous => field_text previous "name" == name && !(field_text previous "init").isEmpty) then
      retained
    else node :: retained.filter (fun previous => field_text previous "name" != name)) []

private def startup_nodes : Nat → Json → Except String (List Json)
  | 0, _ => .error "incomplete traversal of a typed translation unit"
  | depth + 1, node => do
    let children := child_nodes node
    let children := if field_text node "kind" == "OpaqueValueExpr" then []
      else if field_text node "kind" == "GenericSelectionExpr" then
        children.filter (fun child => json_field child "selected" == .bool true)
      else if children.isEmpty then ((json_field node "array_filler").getArr?.toOption.getD #[]).toList.drop 1
      else children
    pure (node :: (← children.mapM (startup_nodes depth)).flatten)

private def thread_reference (node : Json) : Bool :=
  let names := ["pthread_create", "pthread_join", "pthread_self", "pthread_equal", "pthread_mutex_init", "pthread_mutex_destroy",
    "pthread_mutex_lock", "pthread_mutex_trylock", "pthread_mutex_unlock", "pthread_cond_init", "pthread_cond_destroy",
    "pthread_cond_wait", "pthread_cond_signal", "pthread_cond_broadcast"]
  let target := json_field node "referencedDecl"
  field_text node "kind" == "DeclRefExpr" && field_text target "kind" == "FunctionDecl" && names.contains (field_text target "name")

structure LinkStartup where
  parallel : Bool
  labels : List String

private def label_names (unit_name : String) (functions : List (String × List Json)) : List (String × String) :=
  functions.foldl (fun labels (name, nodes) =>
    nodes.foldl (fun labels node =>
      let ident := field_text node "labelDeclId"
      if field_text node "kind" == "AddrLabelExpr" && !(labels.any (fun entry => entry.1 == ident)) then
        (ident, "label:" ++ unit_name ++ name ++ ":" ++ toString labels.length) :: labels
      else labels) labels) []

private def unit_startup (unit_name : String) (depth : Nat) (tree : Json) : Except String LinkStartup := do
  let functions ← (function_definitions (unit_function_declarations tree)).mapM (fun node =>
    (field_text node "name", ·) <$> startup_nodes depth node)
  let objects ← (object_definitions tree).mapM (startup_nodes depth)
  pure ⟨(functions.any (fun (_, nodes) => nodes.any thread_reference)) || (objects.any (·.any thread_reference)),
    (label_names unit_name functions).map Prod.snd⟩

def link_startup (units : List (Nat × Json)) : Except String LinkStartup := do
  let plans ← units.zipIdx.mapM (fun ((depth, tree), index) => unit_startup (unit_namespace units.length index) depth tree)
  pure ⟨plans.any (·.parallel), (plans.flatMap LinkStartup.labels).mergeSort (· ≤ ·)⟩

inductive LinkAction where
  | allocate (unit : Nat)
  | initialise (unit : Nat)

def link_schedule (count : Nat) : List LinkAction :=
  (List.range count).map .allocate ++ (List.range count).map .initialise

theorem link_schedule_order (count : Nat) :
    (link_schedule count).take count = (List.range count).map .allocate ∧
    (link_schedule count).drop count = (List.range count).map .initialise := by
  simp [link_schedule]

private def render_phase (count : Nat) (phase : String) : String :=
  let action (stem : String) (unit : Nat) :=
    let unit_name := unit_namespace count unit
    stem ++ phase ++ if unit_name.isEmpty then "" else "_" ++ hex_binding "unit" unit_name
  let actions := (link_schedule count).map (fun
    | .allocate unit => action "allocate" unit
    | .initialise unit => action "initialise" unit)
  "(do { " ++ String.intercalate "; " actions ++ " })"

private def render_link_line (entries : List (String × String)) (count : Nat) (startup : LinkStartup) : String :=
  let bindings := entries.map (fun (key, handler) => "(" ++ haskell_quote key ++ ", " ++ handler ++ ")")
  let labels := String.intercalate ", " (startup.labels.map haskell_quote)
  let parallel := if startup.parallel then "True " else "False "
  "main = execute [" ++ String.intercalate ", " bindings ++ "] [" ++ labels ++ "] " ++ parallel ++
    render_phase count "Globals" ++ " " ++ render_phase count "Thread"

private def validates_link_runtime (generated : String) : Bool :=
  let gate := "  gate <- if parallel then Just <$> newMVar () else pure Nothing"
  let setup := String.intercalate "\n" [
    "      initial = World counter [] S.empty literalTable (S.fromList entries) codes \"startup\" 0 [] False False table (terminal, output) gate threads owner nullPointer initThread",
    "      action = do",
    "        initialiser",
    "        when parallel $ do",
    "          handle <- allocate \"thread\" 0",
    "          modify' (\\w -> w { currentThread = handle })",
    "        initThread"]
  let entry := String.intercalate "\n" [
    "        mainFunction <- gets (S.lookup \"main\" . functions)",
    "        case mainFunction of",
    "          Nothing -> panic \"no main function\"",
    "          Just f -> f [Number (toInteger (length strings)), argv]"]
  [gate, setup, entry].all (fun equation => (generated.splitOn ("\n" ++ equation ++ "\n")).length == 2)

def validates_linkage (trees : List Json) (startup : LinkStartup) (generated : String) : Bool :=
  let entries := link_entries trees
  let lines := generated.splitOn "\n"
  decide (entries.map Prod.fst).Nodup && (entries.map Prod.fst).contains "main" &&
    entries.all (fun (_, handler) => (lines.filter (· == handler ++ " :: [Value] -> R Value")).length == 1) &&
    (validates_link_runtime generated &&
      (lines.filter (·.startsWith "main =")) == [render_link_line entries trees.length startup])

private theorem unique_lookup (bindings : List (String × String))
    (unique : (bindings.map Prod.fst).Nodup) (key handler : String) (found : (key, handler) ∈ bindings) :
    bindings.lookup key = some handler := by
  induction bindings with
  | nil => simp at found
  | cons first rest ih =>
    obtain ⟨name, body⟩ := first
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp found with equal | later
    · cases equal
      exact List.lookup_cons_self
    · have different : key ≠ name := by
        intro same
        exact unique.1 (same ▸ List.mem_map_of_mem later)
      simp [List.lookup_cons, beq_eq_false_iff_ne.mpr different, ih unique.2 later]

theorem linkage_certificate_routes (trees : List Json) (startup : LinkStartup) (generated : String)
    (accepted : validates_linkage trees startup generated = true) (key handler : String)
    (definition : (key, handler) ∈ link_entries trees) : (link_entries trees).lookup key = some handler := by
  apply unique_lookup _ _ _ _ definition
  simp only [validates_linkage, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact accepted.1.1.1

theorem certified_definition_authentication (trees : List Json) (startup : LinkStartup) (generated : String)
    (accepted : validates_linkage trees startup generated = true) (symbols : String → Option Int)
    (raw : Int) (key handler : String) (definition : (key, handler) ∈ link_entries trees) :
    runtime_call_route symbols ((link_entries trees).reverse.lookup ·) (some (raw, key)) = some (.definition handler) ↔
      symbols key = some raw := by
  simp only [validates_linkage, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have distinct : ((link_entries trees).reverse.map Prod.fst).Nodup := by
    rw [List.map_reverse]
    exact (List.reverse_perm _).symm.nodup accepted.1.1.1
  have found := unique_lookup _ distinct key handler (List.mem_reverse.mpr definition)
  rw [runtime_call_definition, found]
  simp

theorem linkage_certificate_line (trees : List Json) (startup : LinkStartup) (generated : String)
    (accepted : validates_linkage trees startup generated = true) :
    render_link_line (link_entries trees) trees.length startup ∈ generated.splitOn "\n" := by
  simp only [validates_linkage, Bool.and_eq_true] at accepted
  have member : render_link_line (link_entries trees) trees.length startup ∈
      (generated.splitOn "\n").filter (·.startsWith "main =") := by
    rw [beq_iff_eq.mp accepted.2.2]
    simp
  exact (List.mem_filter.mp member).1

def validate_linkage (frontends : List String) (generated : String) : Except String Nat :=
  match frontends.mapM Json.parse with
  | .error message => .error message
  | .ok trees =>
    match link_startup ((frontends.map (·.utf8ByteSize + 1)).zip trees) with
    | .error message => .error message
    | .ok startup =>
      if validates_linkage trees startup generated then .ok (link_entries trees).length
      else .error "emitted function table or startup differs from the typed translation units"

theorem linkage_validation_sound (frontends : List String) (generated : String) (count : Nat)
    (accepted : validate_linkage frontends generated = .ok count) :
    ∃ trees startup, frontends.mapM Json.parse = .ok trees ∧
      link_startup ((frontends.map (·.utf8ByteSize + 1)).zip trees) = .ok startup ∧
      count = (link_entries trees).length ∧
      render_link_line (link_entries trees) trees.length startup ∈ generated.splitOn "\n" := by
  cases parsed : frontends.mapM Json.parse with
  | error message => simp [validate_linkage, parsed] at accepted
  | ok trees =>
    cases planned : link_startup ((frontends.map (·.utf8ByteSize + 1)).zip trees) with
    | error message => simp [validate_linkage, parsed, planned] at accepted
    | ok startup =>
      by_cases valid : validates_linkage trees startup generated = true
      · simp [validate_linkage, parsed, planned, valid] at accepted
        exact ⟨trees, startup, rfl, planned, accepted.symm, linkage_certificate_line _ _ _ valid⟩
      · simp [validate_linkage, parsed, planned, valid] at accepted

private def kernel_source (node : Json) (depth : Nat) (lookup_helper : HelperScope := fun _ => none) :
    Except String (Source × Nat) := do
  let inputs := (child_nodes node).filter (fun child => field_text child "kind" == "ParmVarDecl")
  unless inputs.all (fun argument => type_spelling argument == "unsigned long") do
    throw "kernel parameters require unsigned long"
  let identifiers := inputs.map (fun argument => field_text argument "id")
  if identifiers.any (·.isEmpty) || !decide identifiers.Nodup then
    throw "invalid kernel parameter identities"
  unless (type_spelling node).startsWith "unsigned long (" do
    throw "kernel result requires unsigned long"
  let block ← require ((child_nodes node).find? (fun child => field_text child "kind" == "CompoundStmt"))
    "missing kernel definition"
  match child_nodes block with
  | [statement] =>
    match field_text statement "kind", child_nodes statement with
    | "ReturnStmt", [expression] =>
      let source ← read_expression lookup_helper (fun name => identifiers.idxOf? name) depth expression
      pure (source, inputs.length)
    | _, _ => throw "kernel body must return one expression"
  | _ => throw "kernel body must have one statement"

private def has_normalisation : List String → Bool
  | [] => false
  | line :: rest =>
    if line == "normalise :: Int -> Bool -> Integer -> Integer" then
      rest.take 4 == [
        "normalise width signed n =",
        "  let modulus = 2 ^ width",
        "      bits = n `mod` modulus",
        "  in if signed && bits >= modulus `div` 2 then bits - modulus else bits"]
    else has_normalisation rest

private def kernel_entry_pattern (arity : Nat) : String :=
  if arity = 0 then "_" else
    "(" ++ String.intercalate " : " ((List.range arity).map (fun index => "a" ++ toString index) ++ ["_"]) ++ ")"

private def kernel_entry_body (name : String) (arity : Nat) : String :=
  let arguments := (List.range arity).map (fun index => "(number a" ++ toString index ++ ")")
  " (marshal (IntegerType 64 False) <$> (pure (Number (" ++ kernel_symbol name ++ " " ++
    String.intercalate " " arguments ++ "))))"

private def kernel_location_tail : List Char → Bool
  | ['"'] => true
  | '"' :: _ => false
  | '\\' :: _ :: rest => kernel_location_tail rest
  | '\\' :: [] => false
  | _ :: rest => kernel_location_tail rest
  | [] => false

private def kernel_entry_head (name : String) (arity : Nat) : String :=
  hex_binding "f" name ++ " " ++ kernel_entry_pattern arity ++ " = at \""

private def kernel_entry_equation (name : String) (arity : Nat) (line : String) : Bool :=
  let head := kernel_entry_head name arity
  let body := kernel_entry_body name arity
  let location := (line.drop head.length).take (line.length - head.length - body.length)
  kernel_location_tail location.toList && line == head ++ location ++ body

private def kernel_entry_matches (lines : List String) (name : String) (arity : Nat) : Bool :=
  let entry := hex_binding "f" name
  let signature := entry ++ " :: [Value] -> R Value"
  let fallback := entry ++ " _ = panic " ++ haskell_quote ("wrong argument count for " ++ name)
  match lines.filter (·.startsWith (entry ++ " ")) with
  | [declared, equation] => arity == 0 && declared == signature && kernel_entry_equation name arity equation
  | [declared, equation, failed] => arity != 0 && declared == signature && kernel_entry_equation name arity equation && failed == fallback
  | _ => false

theorem checked_kernel_entry_equation (lines : List String) (name : String) (arity : Nat)
    (accepted : kernel_entry_matches lines name arity = true) :
    ∃ location : String, kernel_location_tail location.toList = true ∧
      kernel_entry_head name arity ++ location ++ kernel_entry_body name arity ∈ lines := by
  have found : ∃ equation ∈ lines, kernel_entry_equation name arity equation = true := by
    unfold kernel_entry_matches at accepted
    dsimp only at accepted
    split at accepted
    next declared equation selected =>
      have member : equation ∈ lines.filter (·.startsWith (hex_binding "f" name ++ " ")) := by
        rw [selected]
        simp
      simp only [Bool.and_eq_true] at accepted
      exact ⟨equation, (List.mem_filter.mp member).1, accepted.2⟩
    next declared equation failed selected =>
      have member : equation ∈ lines.filter (·.startsWith (hex_binding "f" name ++ " ")) := by
        rw [selected]
        simp
      simp only [Bool.and_eq_true] at accepted
      exact ⟨equation, (List.mem_filter.mp member).1, accepted.1.2⟩
    next => contradiction
  obtain ⟨equation, present, checked⟩ := found
  simp only [kernel_entry_equation, Bool.and_eq_true, beq_iff_eq] at checked
  exact ⟨_, checked.1, checked.2 ▸ present⟩

def kernel_return (target : Target) (arguments : Nat → Int) : Int := unsigned 64 (target_eval arguments target)

theorem kernel_return_preserves_result (source : Source) (body : String) (arguments : Nat → Int)
    (accepted : validates_kernel source body = true) :
    ∃ target, body = render_target target ∧ kernel_return target arguments = unsigned 64 (source_eval arguments source) := by
  obtain ⟨target, rendered, correct⟩ := kernel_certificate_sound source body accepted
  exact ⟨target, rendered, congrArg (unsigned 64) (correct arguments)⟩

def validate_kernels (frontend generated : String) : Except String Nat := do
  let tree ← Json.parse frontend
  let lines := generated.splitOn "\n"
  unless has_normalisation lines do
    throw "generated integer normalisation differs from the model"
  unless lines.contains "number (Number n) = n" &&
      lines.contains "marshal (IntegerType width _) value = Number (normalise width False (number value))" do
    throw "generated integer entry conversion differs from the model"
  let declarations := lines.filter (·.startsWith "k_")
  let mut checked := 0
  for node in child_nodes tree do
    if field_text node "kind" == "FunctionDecl" &&
        (child_nodes node).any (fun child => field_text child "kind" == "CompoundStmt") then
      let name := field_text node "name"
      let symbol := kernel_symbol name
      let matching := declarations.filter (·.startsWith (symbol ++ " "))
      if !matching.isEmpty then
        let (source, arity) ← kernel_source node frontend.length
        let signature := symbol ++ " :: " ++ String.intercalate " -> " (List.replicate (arity + 1) "Integer")
        let inputs := (List.range arity).map (fun index => "x" ++ toString index)
        let header := symbol ++ " " ++ String.intercalate " " inputs ++ " = "
        match matching with
        | [actual_signature, equation] =>
          unless actual_signature == signature && equation.startsWith header &&
              validates_kernel source (equation.drop header.length) do
            throw ("kernel differs from verified lowering: " ++ name)
          unless kernel_entry_matches lines name arity do
            throw ("kernel entry differs from verified lowering: " ++ name)
          checked := checked + 1
        | _ => throw ("invalid kernel declarations for " ++ name)
  if checked == 0 || declarations.length != 2 * checked then
    throw "unaccounted or missing kernel declarations"
  else pure checked

private def read_dispatch (row : String) : Except String DispatchGraph := do
  unless row.endsWith ")" do
    throw "invalid dispatch equation"
  let tree ← Json.parse ("[" ++ row.take (row.length - 1) ++ "]")
  match (← tree.getArr?).toList with
  | [entry, successors] =>
    let entry ← entry.getNat?
    let rows ← (← successors.getArr?).toList.mapM fun targets => do
      (← targets.getArr?).toList.mapM Json.getNat?
    pure ⟨entry, rows⟩
  | _ => throw "invalid dispatch graph"

private def validates_dispatch_runtime (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
  let chain := String.intercalate "\n" [
    "chain :: [R Flow] -> R Flow",
    "chain [] = pure Next",
    "chain (action : rest) = action >>= \\flow -> if flow == Next then chain rest else pure flow"]
  let logic := String.intercalate "\n" [
    "logic :: Bool -> R Value -> R Value -> R Value",
    "logic conjunction left right = do",
    "  a <- left",
    "  if truth a == conjunction then boolean . truth <$> right else pure (boolean (not conjunction))"]
  let conditional := String.intercalate "\n" [
    "conditional :: R Value -> (Value -> R Value) -> (Value -> R Value) -> R Value -> R Value",
    "conditional common test convertValue fallback = do",
    "  shared <- common",
    "  tested <- test shared",
    "  if truth tested then convertValue shared else fallback"]
  let branch := String.intercalate "\n" [
    "branch :: R Value -> R Flow -> R Flow -> R Flow",
    "branch condition yes no = condition >>= \\v -> if truth v then yes else no"]
  let loop := String.intercalate "\n" [
    "loop :: R Value -> R Flow -> R Value -> R Flow",
    "loop condition body advance = do",
    "  value <- condition",
    "  if not (truth value) then pure Next else do",
    "    result <- body",
    "    case result of",
    "      Return v -> pure (Return v)",
    "      Break -> pure Next",
    "      _ -> advance >> loop condition body advance"]
  let postloop := String.intercalate "\n" [
    "postloop :: R Flow -> R Value -> R Flow",
    "postloop body condition = do",
    "  result <- body",
    "  case result of",
    "    Return value -> pure (Return value)",
    "    Break -> pure Next",
    "    _ -> do",
    "      value <- condition",
    "      if truth value then postloop body condition else pure Next"]
  let redirect := String.intercalate "\n" [
    "redirectFlow :: Int -> Int -> R Flow -> R Flow",
    "redirectFlow stop restart action = do",
    "  result <- action",
    "  case result of",
    "    Break -> pure (Jump stop)",
    "    Continue -> pure (Jump restart)",
    "    _ -> pure result"]
  let selection := String.intercalate "\n" [
    "selection :: R Value -> [(Maybe (R Value, R Value), R Flow)] -> R Flow",
    "selection condition entries = do",
    "  value <- number <$> condition",
    "  let search fallback [] = pure fallback",
    "      search fallback remaining@((label, _) : rest) = case label of",
    "        Nothing -> search (Just remaining) rest",
    "        Just (lower, upper) -> do",
    "          lo <- number <$> lower",
    "          hi <- number <$> upper",
    "          if lo <= value && value <= hi then pure (Just remaining) else search fallback rest",
    "  selected <- search Nothing entries",
    "  result <- maybe (pure Next) (chain . map snd) selected",
    "  pure (if result == Break then Next else result)"]
  let dispatch := String.intercalate "\n" [
    "dispatch :: (Int, [[Int]]) -> [R Flow] -> R Flow",
    "dispatch (entry, edges) actions",
    "  | length edges /= length actions = panic \"incomplete control-flow graph\"",
    "  | otherwise = go entry",
    "  where",
    "    table = M.fromDistinctAscList (zip [0 ..] (zip (map I.fromList edges) actions))",
    "    go index = case M.lookup index table of",
    "      Nothing -> panic \"invalid control-flow target\"",
    "      Just (targets, action) -> do",
    "        result <- action",
    "        case result of",
    "          Jump next | I.member next targets -> go next",
    "                    | otherwise -> panic \"unlisted control-flow target\"",
    "          _ -> pure result"]
  let computed := String.intercalate "\n" [
    "indirectJump :: [(String, Int)] -> R Value -> R Flow",
    "indirectJump targets expression = do",
    "  value <- expression",
    "  case value of",
    "    Function raw name -> do",
    "      canonical <- gets (S.lookup name . symbols)",
    "      case lookup name targets of",
    "        Just target | canonical == Just raw -> pure (Jump target)",
    "        _ -> panic \"invalid computed jump target\"",
    "    _ -> panic \"invalid computed jump target\""]
  [chain, logic, conditional, branch, loop, postloop, redirect, selection, dispatch, computed].all sections.contains

private def push_dispatch_token (token : String) (tokens : List String) : List String :=
  if token.isEmpty then tokens else token :: tokens

private def dispatch_tokens : List Char → Bool → String → List String → List String
  | [], _, word, tokens => (push_dispatch_token word tokens).reverse
  | '\\' :: _ :: rest, true, word, tokens => dispatch_tokens rest true word tokens
  | '"' :: rest, quoted, word, tokens =>
    dispatch_tokens rest (!quoted) "" (if quoted then tokens else "literal" :: push_dispatch_token word tokens)
  | ch :: rest, quoted, word, tokens =>
    if quoted then dispatch_tokens rest true word tokens
    else if ch.isAlphanum || ch == '_' || ch == '\'' then dispatch_tokens rest false (word.push ch) tokens
    else if ch.isWhitespace then dispatch_tokens rest false "" (push_dispatch_token word tokens)
    else dispatch_tokens rest false "" (String.singleton ch :: push_dispatch_token word tokens)

private def closing_token : String → Option String
  | "(" => some ")"
  | "[" => some "]"
  | "{" => some "}"
  | _ => none

private def dispatch_action_count : List String → List String → Nat → Bool → Option Nat
  | [], _, _, _ => none
  | "]" :: _, [], count, expected => if expected && count != 0 then none else some count
  | "(" :: rest, [], count, true => dispatch_action_count rest [")"] (count + 1) false
  | "," :: rest, [], count, false => dispatch_action_count rest [] count true
  | _ :: _, [], _, _ => none
  | token :: rest, expected :: nested, count, pending =>
    if token == expected then dispatch_action_count rest nested count pending
    else if [")", "]", "}"].contains token then none
    else
      match closing_token token with
      | none => dispatch_action_count rest (expected :: nested) count pending
      | some closing => dispatch_action_count rest (closing :: expected :: nested) count pending

private def dispatch_calls : List String → Except String (List (String × Nat))
  | "dispatch" :: name :: "[" :: rest => do
    unless name.startsWith "g_" do throw "invalid dispatch graph reference"
    let count ← require (dispatch_action_count rest [] 0 true) "invalid dispatch action list"
    pure ((name, count) :: (← dispatch_calls rest))
  | _ :: rest => dispatch_calls rest
  | [] => pure []

def validates_dispatch_counts (graphs calls : List (String × Nat)) : Bool :=
  calls.length == graphs.length && graphs.all (fun graph => calls.contains graph)

theorem checked_dispatch_counts (graphs calls : List (String × Nat))
    (accepted : validates_dispatch_counts graphs calls = true) (name : String) (graph : DispatchGraph)
    (declared : (name, graph.successors.length) ∈ graphs) :
    (name, graph.successors.length) ∈ calls := by
  simp [validates_dispatch_counts, List.all_eq_true] at accepted
  exact accepted.2 name graph.successors.length declared

def validate_dispatches (generated : String) : Except String Nat := do
  unless validates_dispatch_runtime generated do
    throw "dispatch runtime differs from the model"
  let lines := generated.splitOn "\n"
  let mut graphs : List (String × Nat) := []
  let mut signatures : List String := []
  for line in lines.filter (·.startsWith "g_") do
    let signature := " :: (Int, [[Int]])"
    if line.endsWith signature then
      signatures := line.take (line.length - signature.length) :: signatures
    else
      match line.splitOn " = (" with
      | [name, row] =>
        let graph ← read_dispatch row
        unless valid_dispatch graph do
          throw ("dispatch target outside its graph: " ++ name)
        graphs := (name, graph.successors.length) :: graphs
      | _ => throw "invalid dispatch declaration"
  let names := graphs.map Prod.fst
  if names.isEmpty || !decide names.Nodup || names != signatures then
    throw "unaccounted or missing dispatch declarations"
  let calls ← (lines.filter (fun line => (line.splitOn "dispatch g_").length > 1)).mapM (fun line =>
    dispatch_calls (dispatch_tokens line.toList false "" []))
  unless validates_dispatch_counts graphs calls.flatten do
    throw "dispatch action counts differ from the declared graphs"
  pure names.length

def standalone_runtime (runtime : String) : Except String String :=
  match runtime.splitOn "\nmodule Heap\n" with
  | [pragmas, exported] =>
    match exported.splitOn "\nimport " with
    | header :: first :: rest =>
      if header.startsWith "  (" && header.endsWith ") where\n" then
        .ok (pragmas ++ "\nmodule Main where\n\nimport " ++ String.intercalate "\nimport " (first :: rest))
      else .error "invalid Heap export list"
    | _ => .error "missing Heap imports"
  | _ => .error "missing or ambiguous Heap module header"

def bind_runtime (runtime generated : String) :
    Except String { body : String // ∃ prelude,
      standalone_runtime runtime = .ok prelude ∧ generated = prelude ++ "\n" ++ body } :=
  match standalone_runtime runtime with
  | .error why => .error why
  | .ok prelude =>
    let body := generated.drop (prelude.length + 1)
    if identical : generated = prelude ++ "\n" ++ body then
      .ok ⟨body, prelude, rfl, identical⟩
    else .error "generated runtime differs from the supplied Heap module"

private def has_dispatch (body : String) : Bool :=
  (body.splitOn "\n").any fun line => line.startsWith "g_" || (line.splitOn "dispatch g_").length > 1

def validate_module (runtime : String) (frontends : List String) (generated : String) : Except String Nat := do
  let body ← bind_runtime runtime generated
  let functions ← validate_linkage frontends generated
  if has_dispatch body.val then
    let _ ← validate_dispatches generated
  pure functions

theorem module_runtime_bound (runtime : String) (frontends : List String) (generated : String)
    (count : Nat) (accepted : validate_module runtime frontends generated = .ok count) :
    ∃ prelude body, standalone_runtime runtime = .ok prelude ∧
      generated = prelude ++ "\n" ++ body ∧ validate_linkage frontends generated = .ok count ∧
      (has_dispatch body = true → ∃ graphs, validate_dispatches generated = .ok graphs) := by
  cases bound : bind_runtime runtime generated with
  | error why => simp [validate_module, bound, bind, Except.bind] at accepted
  | ok artifact =>
    obtain ⟨prelude, translated, identical⟩ := artifact.property
    cases linked : validate_linkage frontends generated with
    | error why => simp [validate_module, bound, linked, bind, Except.bind] at accepted
    | ok bindings =>
      refine ⟨prelude, artifact.val, translated, identical, ?_, ?_⟩
      · cases dispatch : has_dispatch artifact.val
        · simpa [validate_module, bound, linked, dispatch, bind, Except.bind, pure, Except.pure] using accepted
        · cases verified : validate_dispatches generated with
          | error why => simp [validate_module, bound, linked, dispatch, verified, bind, Except.bind] at accepted
          | ok graphs =>
            simpa [validate_module, bound, linked, dispatch, verified, bind, Except.bind, pure, Except.pure] using accepted
      · intro dispatch
        cases verified : validate_dispatches generated with
        | error why => simp [validate_module, bound, linked, dispatch, verified, bind, Except.bind] at accepted
        | ok graphs => exact ⟨graphs, rfl⟩

def validates_access (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
  let lookup := String.intercalate "\n" [
    "readObject :: Capability -> R Object",
    "readObject NoCapability = panic \"access through a pointer with no allocation capability\"",
    "readObject (Capability _ reference) = liftIO (readIORef reference)"]
  let check := String.intercalate "\n" [
    "checked :: Int -> Value -> R (Capability, Object, Int)",
    "checked size (Pointer capability raw) = do",
    "  object <- readObject capability",
    "  unless (live object) (panic (\"use after free of allocation #\" ++ show capability ++ \"; allocated at \" ++ origin object))",
    "  let displacement = raw - base object",
    "  when (size < 0 || displacement < 0 || displacement > toInteger (extent object) || toInteger size > toInteger (extent object) - displacement)",
    "    (panic (\"out of bounds in allocation #\" ++ show capability ++ \": offset \" ++ show displacement ++ \", access \" ++ show size ++ \", extent \" ++ show (extent object)))",
    "  pure (capability, object, fromInteger displacement)",
    "checked _ _ = panic \"memory access requires a data pointer\""]
  [lookup, check].all sections.contains

def validates_pointer_arithmetic (generated : String) : Bool :=
  let offsets := String.intercalate "\n" [
    "offset :: Integer -> Value -> Value",
    "offset n (Pointer cap raw) = Pointer cap (normalise 64 False (raw + n))",
    "offset n (Function raw name) = Function (normalise 64 False (raw + n)) name",
    "offset n (Stream ident raw) = Stream ident (normalise 64 False (raw + n))",
    "offset _ v = v"]
  let arithmetic := String.intercalate "\n" [
    "  in case op of",
    "    \"+\" -> case (a, b) of",
    "      (_, Number _) | addressed a -> Right (offset (y * stride) a)",
    "      (Number _, _) | addressed b -> Right (offset (x * stride) b)",
    "      _ -> arithmetic (x + y)",
    "    \"-\" -> case (a, b) of",
    "      (_, Number _) | addressed a -> Right (offset (negate y * stride) a)",
    "      _ | addressed a && addressed b -> if stride == 0 then Left \"zero pointer stride\" else wrap ((x - y) `quot` stride)",
    "      _ -> arithmetic (x - y)"]
  let bounds := String.intercalate "\n" [
    "builtin name [Pointer capability _] | name == \"zgetlower\" || name == \"zgetupper\" =",
    "  case capability of",
    "    NoCapability -> pure nullPointer",
    "    _ -> do",
    "      object <- readObject capability",
    "      pure (Pointer capability (base object + if name == \"zgetupper\" && live object then toInteger (extent object) else 0))"]
  (generated.splitOn "\n\n").contains offsets &&
    (generated.splitOn arithmetic).length == 2 && (generated.splitOn bounds).length == 2

def validates_argument_slots (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
  let size := String.intercalate "\n" [
    "slotSize :: Int -> Integer",
    "slotSize size = ((toInteger size + 7) `div` 8) * 8"]
  let alignment := String.intercalate "\n" [
    "addSlot :: Integer -> CType -> (Integer, Integer)",
    "addSlot from ty =",
    "  let alignment = case ty of",
    "        FloatingType 80 -> 16",
    "        ComplexType 80 -> 16",
    "        AggregateType _ a -> max 8 (toInteger a)",
    "        _ -> 8",
    "  in alignedSlot from ty alignment"]
  let placement := String.intercalate "\n" [
    "alignedSlot :: Integer -> CType -> Integer -> (Integer, Integer)",
    "alignedSlot from ty alignment =",
    "  let start = ((from + alignment - 1) `div` alignment) * alignment",
    "  in (start, start + slotSize (widthOf ty))"]
  let area := String.intercalate "\n" [
    "argumentArea :: [Value] -> R Value",
    "argumentArea values = do",
    "  let slot value = case value of",
    "        Aggregate size alignment _ _ -> (AggregateType size alignment, value)",
    "        Extended _ -> (FloatingType 80, value)",
    "        Complex width _ _ -> (ComplexType width, value)",
    "        Wide _ -> (IntegerType 128 False, value)",
    "        _ | addressed value -> (PointerType, value)",
    "          | otherwise -> (IntegerType 64 False, value)",
    "      slots = map slot values",
    "      offsets = scanl (\\index (ty, _) -> snd (addSlot index ty)) 0 slots",
    "  size <- hostSize (last offsets)",
    "  area <- allocate \"argument\" size",
    "  forM_ (zip offsets slots) $ \\(index, (ty, value)) ->",
    "    void (store ty (offset (fst (addSlot index ty)) area) value)",
    "  freeze (pure area)",
    "  pure area"]
  let named := String.intercalate "\n" [
    "vaStart :: Value -> [CType] -> R Value -> R Value",
    "vaStart area named list = do",
    "  pointer <- list",
    "  let start = foldl (\\index ty -> snd (addSlot index ty)) 0 named",
    "  store PointerType pointer (offset start area) >> pure (Number 0)"]
  let copied := String.intercalate "\n" [
    "vaCopy :: R Value -> R Value -> R Value",
    "vaCopy destination source = do",
    "  pointer <- destination",
    "  cursor <- source >>= load PointerType",
    "  store PointerType pointer cursor >> pure (Number 0)"]
  let fetch := String.intercalate "\n" [
    "vaArg :: CType -> R Value -> R Value",
    "vaArg ty list = do",
    "  pointer <- list",
    "  cursor <- load PointerType pointer",
    "  let (start, next) = case ty of",
    "        IntegerType 128 _ -> alignedSlot (number cursor) ty 16",
    "        _ -> addSlot (number cursor) ty",
    "  value <- load ty (offset (start - number cursor) cursor)",
    "  void (store PointerType pointer (offset (next - number cursor) cursor))",
    "  pure value"]
  let available := String.intercalate "\n" [
    "vaAvailable :: R Value -> R Value",
    "vaAvailable list = do",
    "  cursor <- list >>= load PointerType",
    "  case cursor of",
    "    Pointer NoCapability _ -> pure (boolean False)",
    "    Pointer capability raw -> do",
    "      object <- readObject capability",
    "      pure (boolean (live object && raw >= base object && raw + 8 <= base object + toInteger (extent object)))",
    "    _ -> pure (boolean False)"]
  [size, alignment, placement, area, named, copied, fetch, available].all sections.contains

def validates_invocation (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
  let route := String.intercalate "\n" [
    "invoke :: Maybe CType -> R Value -> [R Value] -> R Value",
    "invoke expected callee arguments = do",
    "  target <- callee",
    "  values <- sequence arguments",
    "  result <- case target of",
    "    Function raw name -> do",
    "      canonical <- gets (S.lookup name . symbols)",
    "      unless (canonical == Just raw) (panic \"call through an invalid function pointer\")",
    "      defined <- gets (S.lookup name . functions)",
    "      case defined of",
    "        Just action -> action values",
    "        Nothing -> do"]
  let cast := String.intercalate "\n" [
    "cast :: CType -> Value -> Value",
    "cast (IntegerType w s) v = Number (normalise w s (number v))"]
  let marshal := String.intercalate "\n" [
    "marshal :: CType -> Value -> Value",
    "marshal (IntegerType 128 _) value = Wide (normalise 128 False (number value))",
    "marshal (IntegerType width _) value = Number (normalise width False (number value))"]
  let result := String.intercalate "\n" [
    "    _ -> panic \"call through an invalid function pointer\"",
    "  case (expected, result) of",
    "    (Nothing, _) -> pure (Number 0)",
    "    (Just _, NoValue) -> panic \"callee returned no value to a non-void callsite\"",
    "    (Just (AggregateType size _), Aggregate actual _ _ _) | size == actual -> pure result",
    "    (Just (AggregateType _ _), _) -> panic \"callee returned an incompatible aggregate value\"",
    "    (Just _, Aggregate _ _ _ _) -> panic \"callee returned an aggregate to a scalar callsite\"",
    "    (Just ty, value) -> pure (cast ty value)"]
  [route, cast, marshal].all (fun equation => (generated.splitOn equation).length == 2) &&
    sections.any (fun block => block.startsWith route && block.endsWith result)

def validates_synchronisation (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
  let update := String.intercalate "\n" [
    "changeSync :: Int -> Value -> Synchronisation -> (Synchronisation -> R (Synchronisation, a)) -> R a",
    "changeSync width pointer initial change = do",
    "  (ident, object, displacement) <- checked width pointer",
    "  when (number pointer `mod` 8 /= 0) (panic \"unaligned pthread object\")",
    "  when (readOnly object) (panic \"pthread operation on read-only memory\")",
    "  let cell = M.findWithDefault initial displacement (synchronisation object)",
    "  (updated, value) <- change cell",
    "  current <- readObject ident",
    "  writeObject ident (current { synchronisation = M.insert displacement updated (synchronisation current) })",
    "  pure value"]
  let acquire := String.intercalate "\n" [
    "acquireMutex :: Bool -> Value -> R Value",
    "acquireMutex tryOnly pointer = do",
    "  caller <- gets (number . currentThread)",
    "  waiter <- liftIO newEmptyMVar",
    "  result <- locked $ changeSync mutexWidth pointer emptyMutex $ \\cell ->",
    "    case cell of",
    "      Mutex Nothing waiting -> pure (Mutex (Just caller) waiting, Left 0)",
    "      Mutex (Just _) _ | tryOnly -> pure (cell, Left 16)",
    "      Mutex (Just owner) waiting",
    "        | owner == caller -> pure (cell, Left 35)",
    "        | otherwise -> pure (Mutex (Just owner) (waiting Q.|> (caller, waiter)), Right waiter)",
    "      _ -> pure (cell, Left 22)",
    "  case result of",
    "    Left status -> pure (Number status)",
    "    Right signal -> liftIO (takeMVar signal) >> pure (Number 0)"]
  let release := String.intercalate "\n" [
    "releaseMutex :: Value -> R (Either Integer (Maybe (MVar ())))",
    "releaseMutex pointer = do",
    "  caller <- gets (number . currentThread)",
    "  changeSync mutexWidth pointer emptyMutex $ \\cell ->",
    "    case cell of",
    "      Mutex (Just owner) waiting | owner == caller ->",
    "        case Q.viewl waiting of",
    "          Q.EmptyL -> pure (emptyMutex, Right Nothing)",
    "          (next, waiter) Q.:< remaining -> pure (Mutex (Just next) remaining, Right (Just waiter))",
    "      Mutex _ _ -> pure (cell, Left 1)",
    "      _ -> pure (cell, Left 22)"]
  let handoff := String.intercalate "\n" [
    "finishRelease :: Either Integer (Maybe (MVar ())) -> R Value",
    "finishRelease result = case result of",
    "  Left status -> pure (Number status)",
    "  Right signal -> liftIO (mapM_ (\\waiter -> putMVar waiter ()) signal) >> pure (Number 0)"]
  let await := String.intercalate "\n" [
    "waitCondition :: Value -> Value -> R Value",
    "waitCondition condition mutex",
    "  | number condition == number mutex = pure (Number 22)",
    "  | otherwise = do",
    "      waiter <- liftIO newEmptyMVar",
    "      released <- locked $ changeSync conditionWidth condition emptyCondition $ \\cell ->",
    "        case cell of",
    "          Condition waiting -> do",
    "            result <- releaseMutex mutex",
    "            case result of",
    "              Left _ -> pure (cell, result)",
    "              Right _ -> pure (Condition (waiting Q.|> waiter), result)",
    "          _ -> pure (cell, Left 22)",
    "      case released of",
    "        Left status -> pure (Number status)",
    "        Right _ -> do",
    "          void (finishRelease released)",
    "          liftIO (takeMVar waiter)",
    "          acquireMutex False mutex"]
  let signal := String.intercalate "\n" [
    "notifyCondition :: Bool -> Value -> R Value",
    "notifyCondition allWaiters pointer = do",
    "  result <- locked $ changeSync conditionWidth pointer emptyCondition $ \\cell ->",
    "    case cell of",
    "      Condition waiting",
    "        | allWaiters -> pure (emptyCondition, Just waiting)",
    "        | otherwise -> case Q.viewl waiting of",
    "            Q.EmptyL -> pure (cell, Just Q.empty)",
    "            waiter Q.:< remaining -> pure (Condition remaining, Just (Q.singleton waiter))",
    "      _ -> pure (cell, Nothing)",
    "  case result of",
    "    Nothing -> pure (Number 22)",
    "    Just signals -> liftIO (mapM_ (\\waiter -> putMVar waiter ()) signals) >> pure (Number 0)"]
  [update, acquire, release, handoff, await, signal].all sections.contains

def validates_release (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
  let publish := String.intercalate "\n" [
    "writeObject :: Capability -> Object -> R ()",
    "writeObject NoCapability _ = panic \"access through a pointer with no allocation capability\"",
    "writeObject (Capability _ reference) object = liftIO (writeIORef reference object)"]
  let lock := String.intercalate "\n" [
    "locked :: R a -> R a",
    "locked action = R $ ExceptT $ StateT $ \\world ->",
    "  case memoryGate world of",
    "    Nothing -> runWorld world action",
    "    Just gate -> withMVar gate (\\_ -> runWorld world action)"]
  let release := String.intercalate "\n" [
    "release :: Value -> R ()",
    "release pointer = locked (releaseCell pointer)"]
  let transition := String.intercalate "\n" [
    "releaseCell :: Value -> R ()",
    "releaseCell (Pointer NoCapability 0) = pure ()",
    "releaseCell pointer@(Pointer ident _) = do",
    "  (_, object, displacement) <- checked 0 pointer",
    "  unless (storage object == \"heap\" && displacement == 0) (panic \"free requires the start of a heap allocation\")",
    "  writeObject ident (object { live = False, bytes = M.empty, shadow = M.empty, atomicSlots = I.empty, synchronisation = M.empty })",
    "  event (\"free #\" ++ show ident ++ \"; all aliases invalidated\")",
    "releaseCell _ = panic \"free requires a data pointer\""]
  [publish, lock, release, transition].all sections.contains

def validates_allocation (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
  let transition := String.intercalate "\n" [
    "allocate :: String -> Int -> R Value",
    "allocate kind size = do",
    "  let alignment = if kind == \"global\" then 8 else 16",
    "  when (size < 0 || size > maxBound - (alignment - 1)) (panic \"allocation size exceeds the host representation\")",
    "  counter <- gets allocationCounter",
    "  loc <- gets location",
    "  let rounded = ((size + (alignment - 1)) `div` alignment) * alignment",
    "  entry <- liftIO $ atomicModifyIORef' counter $ \\old@(ident, address) ->",
    "    let start = ((address + 15) `div` 16) * 16 in",
    "    if ident == maxBound || start + toInteger rounded >= 4611686018427387904 then (old, Nothing)",
    "    else ((ident + 1, start + toInteger (max rounded 1) + 16), Just (ident, start))",
    "  (ident, start) <- maybe (panic \"virtual address space exhausted\") pure entry",
    "  let object = Object start rounded True kind M.empty M.empty I.empty M.empty [] loc",
    "  reference <- liftIO (newIORef object)",
    "  event (\"allocate #\" ++ show ident ++ \" \" ++ show rounded ++ \" bytes (\" ++ kind ++ \")\")",
    "  pure (Pointer (Capability ident reference) start)"]
  sections.contains transition && (generated.splitOn "\n").contains "  counter <- newIORef (1, 4096)"

def validates_copy (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
  let readonly := String.intercalate "\n" [
    "readOnly :: Object -> Bool",
    "readOnly object = storage object `elem` [\"literal\", \"constant\"]"]
  let range := String.intercalate "\n" [
    "aggregateBytes :: Int -> Int -> M.IntMap a -> M.IntMap a",
    "aggregateBytes start count values =",
    "  M.mapKeysMonotonic (subtract start) (M.takeWhileAntitone (< start + count) (M.dropWhileAntitone (< start) values))"]
  let shadow := String.intercalate "\n" [
    "aggregateShadow :: Int -> Int -> M.IntMap Value -> M.IntMap Value",
    "aggregateShadow start count = aggregateBytes start (max 0 (count - 7))"]
  let copy := String.intercalate "\n" [
    "copyMemory :: Value -> Value -> Int -> R Value",
    "copyMemory destination _ 0 = pure destination",
    "copyMemory destination source count = locked $ do",
    "  when (count < 0) (panic \"invalid memory copy length\")",
    "  (_, src, srcOffset) <- checked count source",
    "  (ident, dst, dstOffset) <- checked count destination",
    "  when (readOnly dst) (panic \"write to read-only memory\")",
    "  let end = dstOffset + count",
    "      payload = M.mapKeysMonotonic (+ dstOffset) (aggregateBytes srcOffset count (bytes src))",
    "      untouchedBytes = M.union (M.takeWhileAntitone (< dstOffset) (bytes dst)) (M.dropWhileAntitone (< end) (bytes dst))",
    "      aligned = srcOffset `mod` 8 == dstOffset `mod` 8",
    "      caps = if aligned then M.mapKeysMonotonic (+ dstOffset) (aggregateShadow srcOffset count (shadow src)) else M.empty",
    "      outside slot = slot <= dstOffset - 8 || slot >= end",
    "  writeObject ident (dst { bytes = M.union payload untouchedBytes",
    "                         , shadow = M.union caps (M.filterWithKey (\\slot _ -> outside slot) (shadow dst))",
    "                         , atomicSlots = I.filter outside (atomicSlots dst) })",
    "  event (\"copy \" ++ show count ++ \" bytes to #\" ++ show ident ++ \"+\" ++ show dstOffset)",
    "  pure destination"]
  let builtin := ["memcpy", "memmove"].map fun name =>
    "builtin \"" ++ name ++ "\" [destination, source, count] = hostSize (number count) >>= copyMemory destination source"
  [readonly, range, shadow, copy].all sections.contains && builtin.all (generated.splitOn "\n").contains

def validates_scalar_memory (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
  let lines := generated.splitOn "\n"
  let read := String.intercalate "\n" [
    "readScalar :: Int -> Int -> M.IntMap Integer -> Integer",
    "readScalar displacement width payload =",
    "  sum [M.findWithDefault 0 (displacement + i) payload * 256 ^ i | i <- [0 .. width - 1]]"]
  let write := String.intercalate "\n" [
    "writeScalar :: Int -> Int -> Integer -> M.IntMap Integer -> M.IntMap Integer",
    "writeScalar displacement width raw payload =",
    "  foldl (\\m i -> M.insert (displacement + i) ((raw `div` (256 ^ i)) `mod` 256) m) payload [0 .. width - 1]"]
  let uses := ["  let raw = readScalar displacement (widthOf ty) (bytes object)",
    "        IntegerType width signed -> Number (normalise width signed raw)",
    "      updated = writeScalar displacement (widthOf ty) raw (bytes object)"]
  [read, write].all sections.contains && uses.all lines.contains && has_normalisation lines

def validates_freeze (generated : String) : Bool :=
  let freeze := String.intercalate "\n" [
    "freeze :: R Value -> R ()",
    "freeze action = do",
    "  pointer <- action",
    "  case pointer of",
    "    Pointer capability _ -> locked $ do",
    "      object <- readObject capability",
    "      writeObject capability (object { storage = \"constant\" })",
    "    _ -> panic \"read-only storage requires a data pointer\""]
  let scalar_guard := String.intercalate "\n" [
    "storeCell declared pointer value = do",
    "  let ty = case declared of AtomicType inner -> inner; other -> other",
    "  (ident, object, displacement) <- checked (widthOf declared) pointer",
    "  when (readOnly object) (panic \"write to read-only memory\")"]
  (generated.splitOn "\n\n").contains freeze && (generated.splitOn scalar_guard).length == 2

private abbrev Scope := List (String × Nat)

private def read_local (scope : Scope) : Nat → Json → Except String Nat
  | 0, _ => .error "incomplete closed assignment target"
  | depth + 1, node =>
    match field_text node "kind", child_nodes node with
    | "ParenExpr", [child] => read_local scope depth child
    | "DeclRefExpr", [] => do
      unless type_spelling node == "unsigned long" do
        throw "closed assignment requires an unsigned long local"
      let ident := field_text (json_field node "referencedDecl") "id"
      require (List.lookup ident scope) "closed assignment requires an in-scope local"
    | _, _ => .error "closed assignment requires an unsigned long local"

private def sequence_commands : List (Command Source) → Command Source
  | [] => .skip
  | last :: rest => rest.foldl (fun tail first => .sequence first tail) last

private def read_command (lookup_helper : HelperScope) (entry : Bool) :
    Nat → Scope → Nat → Json → Except String (Command Source × Nat)
  | 0, _, _, _ => .error "incomplete closed statement"
  | depth + 1, scope, rank, node => do
    match field_text node "kind", child_nodes node with
    | "CompoundStmt", statements =>
      let mut scope := scope
      let mut rank := rank
      let mut reversed := []
      for statement in statements do
        if field_text statement "kind" == "DeclStmt" then
          let mut declarations := []
          for declaration in child_nodes statement do
            let ident := field_text declaration "id"
            unless field_text declaration "kind" == "VarDecl" && type_spelling declaration == "unsigned long" &&
                (field_text declaration "storageClass").isEmpty && field_text declaration "init" == "c" &&
                !ident.isEmpty && (List.lookup ident scope).isNone do
              throw "closed declaration requires an initialised unsigned long local"
            let [expression] := child_nodes declaration | throw "missing closed local initialiser"
            let value ← read_expression lookup_helper (fun ident => List.lookup ident scope) depth expression
            declarations := .store rank value :: declarations
            scope := (ident, rank) :: scope
            rank := rank + 1
          reversed := sequence_commands declarations :: reversed
        else
          let (command, next) ← read_command lookup_helper entry depth scope rank statement
          rank := next
          reversed := command :: reversed
      pure (sequence_commands reversed, rank)
    | "NullStmt", [] => pure (.skip, rank)
    | "BinaryOperator", [left, right] =>
      unless field_text node "opcode" == "=" do
        throw "closed statement requires simple assignment"
      let slot ← read_local scope depth left
      let value ← read_expression lookup_helper (fun ident => List.lookup ident scope) depth right
      pure (.store slot value, rank)
    | "IfStmt", [guard, yes] =>
      let condition ← read_expression lookup_helper (fun ident => List.lookup ident scope) depth guard
      let (chosen, next) ← read_command lookup_helper entry depth scope rank yes
      pure (.select condition chosen .skip, next)
    | "IfStmt", [guard, yes, no] =>
      let condition ← read_expression lookup_helper (fun ident => List.lookup ident scope) depth guard
      let (chosen, next) ← read_command lookup_helper entry depth scope rank yes
      let (alternative, next) ← read_command lookup_helper entry depth scope next no
      pure (.select condition chosen alternative, next)
    | "WhileStmt", [guard, body] =>
      let condition ← read_expression lookup_helper (fun ident => List.lookup ident scope) depth guard
      let (iteration, next) ← read_command lookup_helper entry depth scope rank body
      pure (.loop condition iteration, next)
    | "ReturnStmt", [value] =>
      let expression ← if entry then do
        unless field_text value "kind" == "CStyleCastExpr" && field_text value "castKind" == "IntegralCast" &&
            type_spelling value == "int" do
          throw "closed return requires an unsigned long expression cast to int"
        let [expression] := child_nodes value | throw "missing closed return expression"
        pure expression
      else pure value
      let value ← read_expression lookup_helper (fun ident => List.lookup ident scope) depth expression
      pure (.result value, rank)
    | _, _ => throw "unsupported closed statement"

private def helper_dependencies : Nat → Json → List String → List String
  | 0, _, tail => tail
  | depth + 1, node, tail =>
    let children := child_nodes node
    let nested := children.foldr (helper_dependencies depth) tail
    match field_text node "kind", children with
    | "CallExpr", target :: _ => direct_callee depth target :: nested
    | _, _ => nested

private structure HelperOrder where
  visited : Std.HashMap String Bool
  reversed : List Json
  recursive : Bool

private def visit_helper (definitions : Std.HashMap String Json) (source_depth : Nat) :
    Nat → HelperOrder → String → Except String HelperOrder
  | 0, _, _ => .error "incomplete closed helper graph"
  | depth + 1, state, name => do
    match state.visited[name]? with
    | some true => pure state
    | some false => pure { state with recursive := true }
    | none =>
      let definition ← require definitions[name]? "closed call requires a defined unsigned long helper"
      let mut next := { state with visited := state.visited.insert name false }
      for dependency in helper_dependencies source_depth definition [] do
        next ← visit_helper definitions source_depth depth next dependency
      pure { next with visited := next.visited.insert name true, reversed := definition :: next.reversed }

private def order_helpers (helpers : List Json) (source_depth : Nat) : Except String (List Json × Bool) := do
  let mut definitions : Std.HashMap String Json := ∅
  for definition in helpers do
    let name := field_text definition "name"
    if name.isEmpty || definitions.contains name then
      throw "invalid closed helper identity"
    definitions := definitions.insert name definition
  let mut seen : HelperOrder := ⟨∅, [], false⟩
  for definition in helpers do
    seen ← visit_helper definitions source_depth (helpers.length + 1) seen (field_text definition "name")
  pure (seen.reversed.reverse, seen.recursive)

inductive ClosedProgram where
  | direct (helpers : List (Helper Source)) (body : Command Source)
  | framed (helpers : List (Helper (Command Source))) (body : Command Source)

private def single_return (block : Json) : Bool :=
  match child_nodes block with
  | [statement] => field_text statement "kind" == "ReturnStmt" && (child_nodes statement).length == 1
  | _ => false

private def closed_tree (budget : Nat) (tree : Json) : Except String ClosedProgram := do
  unless field_text tree "kind" == "TranslationUnitDecl" do
    throw "expected a translation unit"
  let declarations := (child_nodes tree).filter fun node =>
    field_text node "kind" != "EmptyDecl" &&
      !(field_text node "kind" == "TypedefDecl" && json_field node "isImplicit" == .bool true)
  unless declarations.all (fun node => field_text node "kind" == "FunctionDecl") do
    throw "closed compilation requires function declarations"
  let definitions := declarations.filter fun node => (child_nodes node).any (fun child => field_text child "kind" == "CompoundStmt")
  let [main] := definitions.filter (fun node => field_text node "name" == "main") |
    throw "closed program must define int main(void)"
  unless type_spelling main == "int (void)" do
    throw "closed program must define int main(void)"
  let [body] := child_nodes main | throw "invalid closed main definition"
  unless field_text body "kind" == "CompoundStmt" do
    throw "invalid closed main body"
  let (ordered, recursive) ← order_helpers (definitions.filter (fun node => field_text node "name" != "main")) budget
  let headers ← ordered.mapM fun definition => do
    let name := field_text definition "name"
    let (inputs, blocks) := (child_nodes definition).partition (fun node => field_text node "kind" == "ParmVarDecl")
    let arity := inputs.length
    let parameters := if arity == 0 then "void" else String.intercalate ", " (List.replicate arity "unsigned long")
    unless inputs.all (fun node => type_spelling node == "unsigned long") &&
        type_spelling definition == ("unsigned long (" ++ parameters ++ ")") do
      throw "closed helper requires an unsigned long signature"
    let [block] := blocks | throw "invalid closed helper definition"
    unless field_text block "kind" == "CompoundStmt" do
      throw "invalid closed helper body"
    let identifiers := inputs.map (fun node => field_text node "id")
    if identifiers.any (·.isEmpty) || !decide identifiers.Nodup then
      throw "invalid closed helper parameters"
    pure (name, identifiers, block)
  let framed := recursive || headers.any (fun (_, _, block) => !single_return block)
  let available := headers.zipIdx.map (fun ((name, identifiers, _), slot) => (name, (slot, identifiers.length)))
  let mut linked : List (String × (Nat × Nat)) := []
  let mut helpers : List (Helper (Command Source)) := []
  for ((name, identifiers, block), slot) in headers.zipIdx do
    let scope := if framed then available else linked
    let arity := identifiers.length
    let (code, _) ← read_command (fun callee => List.lookup callee scope) false budget identifiers.zipIdx arity block
    helpers := ⟨arity, code⟩ :: helpers
    linked := (name, (slot, arity)) :: linked
  let (entry, _) ← read_command (fun name => List.lookup name linked) true budget [] 0 body
  if framed then pure (.framed helpers.reverse entry)
  else
    let direct ← helpers.reverse.mapM fun helper => match helper.body with
      | .result value => pure ⟨helper.arity, value⟩
      | _ => throw "closed helper requires one return statement"
    pure (.direct direct entry)

def closed_source (frontend : String) : Except String ClosedProgram := do
  closed_tree frontend.length (← Json.parse frontend)

private def exit_definition : List String := ["",
  "normalise :: Int -> Bool -> Integer -> Integer",
  "normalise width _ value = value `mod` (2 ^ width)", "",
  "exitStatus :: Integer -> ExitCode",
  "exitStatus value = case fromInteger (value `mod` 256) of",
  "  0 -> ExitSuccess", "  code -> ExitFailure code", ""]

private def render_slot_expression (strict : Bool) (expression : Target) : String :=
  "(\\slots -> " ++ render_expression (fun index => "(readSlot " ++ toString index ++ " slots)") strict expression ++ ")"

private def render_command (strict : Bool) : Command Target → String
  | .skip => "Next"
  | .store slot expression => "storeSlot " ++ toString slot ++ " " ++ render_slot_expression strict expression
  | .sequence first second => "thenSlot (" ++ render_command strict first ++ ") (" ++ render_command strict second ++ ")"
  | .select guard yes no => "chooseSlot " ++ render_slot_expression strict guard ++ " (" ++
      render_command strict yes ++ ") (" ++ render_command strict no ++ ")"
  | .loop guard body => "whileSlot " ++ render_slot_expression strict guard ++ " (" ++ render_command strict body ++ ")"
  | .result expression => "returnSlot " ++ render_slot_expression strict expression

private def render_helper (slot : Nat) (helper : Helper Target) : List String :=
  let name := "h_" ++ toString slot
  let signature := name ++ " :: " ++ String.intercalate " -> " (List.replicate (helper.arity + 1) "Integer")
  let parameters := (List.range helper.arity).map (fun index => "x" ++ toString index)
  let equation := String.intercalate " " (name :: parameters ++ ["=", render_target helper.body])
  [signature, equation, ""]

private def program_header := ["module Main where", "", "import Data.Bits", "import System.Exit"]

private def slot_runtime : List String := [
    "type Locals = Slots.IntMap Integer",
    "data SlotFlow = Next !Locals | Returned !Integer",
    "type Action = Locals -> SlotFlow", "",
    "readSlot :: Int -> Locals -> Integer",
    "readSlot = Slots.findWithDefault 0", "",
    "storeSlot :: Int -> (Locals -> Integer) -> Action",
    "storeSlot slot value locals = Next (Slots.insert slot (value locals) locals)", "",
    "thenSlot :: Action -> Action -> Action",
    "thenSlot first second locals = case first locals of",
    "  Next updated -> second updated",
    "  result -> result", "",
    "chooseSlot :: (Locals -> Integer) -> Action -> Action -> Action",
    "chooseSlot guard yes no locals = if guard locals == 0 then no locals else yes locals", "",
    "whileSlot :: (Locals -> Integer) -> Action -> Action",
    "whileSlot guard body = loop",
    "  where",
    "    loop locals",
    "      | guard locals == 0 = Next locals",
    "      | otherwise = case body locals of",
    "          Next updated -> loop updated",
    "          result -> result", "",
    "returnSlot :: (Locals -> Integer) -> Action",
    "returnSlot value locals = Returned (value locals)", "",
    "runSlots :: Action -> Integer",
    "runSlots action = case action Slots.empty of",
    "  Next _ -> 0",
    "  Returned value -> value", ""]

private def slot_entry (strict : Bool) (body : Command Target) : List String :=
  ["main :: IO ()", "main = exitWith (exitStatus (runSlots (" ++ render_command strict body ++ ")))", ""]

def render_program (helpers : List (Helper Target)) (body : Command Target) : String :=
  let definitions := exit_definition ++ (helpers.zipIdx.flatMap fun (helper, slot) => render_helper slot helper)
  match body with
  | .result expression => String.intercalate "\n" (program_header ++ definitions ++ [
    "main :: IO ()", "main = exitWith (exitStatus (" ++ render_expression (fun _ => "0") false expression ++ "))", ""])
  | _ => String.intercalate "\n" (program_header ++ ["import qualified Data.IntMap.Strict as Slots"] ++ definitions ++
      slot_runtime ++ slot_entry false body)

private def render_framed_helper (slot : Nat) (helper : Helper (Command Target)) : List String :=
  let name := "h_" ++ toString slot
  let signature := name ++ " :: " ++ String.intercalate " -> " (List.replicate (helper.arity + 1) "Integer")
  let parameters := (List.range helper.arity).map (fun index => "x" ++ toString index)
  let action := "runHelper [" ++ String.intercalate ", " parameters ++ "] (" ++ render_command true helper.body ++ ")"
  [signature, String.intercalate " " (name :: parameters ++ ["=", action]), ""]

def render_framed_program (helpers : List (Helper (Command Target))) (body : Command Target) : String :=
  let definitions := helpers.zipIdx.flatMap fun (helper, slot) => render_framed_helper slot helper
  let runtime := [
    "strictOperands :: (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer",
    "strictOperands operation left right = left `seq` right `seq` operation left right", "",
    "runHelper :: [Integer] -> Action -> Integer",
    "runHelper values action = foldr seq () values `seq` case action (Slots.fromList (zip [0 ..] values)) of",
    "  Next _ -> error \"closed helper fell through\"",
    "  Returned value -> value", ""]
  String.intercalate "\n" (program_header ++ ["import qualified Data.IntMap.Strict as Slots"] ++ exit_definition ++
    definitions ++ slot_runtime ++ runtime ++ slot_entry true body)

private def body_calls_in_scope (arities : Array Nat) : Command Source → Bool
  | .skip => true
  | .store _ expression | .result expression => calls_in_scope arities (fun _ => true) expression
  | .sequence first second => body_calls_in_scope arities first && body_calls_in_scope arities second
  | .select condition yes no => calls_in_scope arities (fun _ => true) condition &&
      (body_calls_in_scope arities yes && body_calls_in_scope arities no)
  | .loop condition body => calls_in_scope arities (fun _ => true) condition && body_calls_in_scope arities body

def check_frame_helpers (arities : Array Nat) : List (Helper (Command Source)) → Bool
  | [] => true
  | helper :: rest => returns_value helper.body && (check_commands helper.body &&
    (body_calls_in_scope arities helper.body && check_frame_helpers arities rest))

theorem checked_frame_returns (arities : Array Nat) (helpers : List (Helper (Command Source)))
    (accepted : check_frame_helpers arities helpers = true) (helper : Helper (Command Source))
    (member : helper ∈ helpers) : returns_value helper.body = true := by
  induction helpers with
  | nil => simp at member
  | cons first rest checked =>
    simp only [check_frame_helpers, Bool.and_eq_true] at accepted
    rcases List.mem_cons.mp member with equality | remaining
    · subst helper
      exact accepted.1
    · exact checked accepted.2.2.2 remaining

def validates_framed_program (helpers : List (Helper (Command Source))) (body : Command Source) (generated : String) : Bool :=
  check_frame_helpers (helpers.toArray.map Helper.arity) helpers && (check_commands body &&
    (body_calls_in_scope (helpers.toArray.map Helper.arity) body &&
      generated == render_framed_program (helpers.map lower_frame) (body.map lower)))

theorem framed_program_certificate_sound (helpers : List (Helper (Command Source))) (body : Command Source)
    (generated : String) (accepted : validates_framed_program helpers body generated = true) :
    generated = render_framed_program (helpers.map lower_frame) (body.map lower) ∧
      (∀ helper ∈ helpers, returns_value helper.body = true) ∧
      (∀ status, (∃ fuel, recursive_target_exit (helpers.toArray.map lower_frame) (body.map lower) fuel = some status) ↔
        source_observes_exit helpers.toArray body status) := by
  simp only [validates_framed_program, Bool.and_eq_true, beq_iff_eq] at accepted
  exact ⟨accepted.2.2.2, checked_frame_returns _ helpers accepted.1, recursive_target_refines helpers.toArray body⟩

def validates_program (helpers : List (Helper Source)) (body : Command Source) (generated : String) : Bool :=
  check_helpers #[] helpers && (check_commands body &&
    (body_calls_in_scope (helpers.toArray.map Helper.arity) body && generated == render_program (helpers.map Helper.lower) (body.map lower)))

theorem program_certificate_sound (helpers : List (Helper Source)) (body : Command Source) (generated : String)
    (accepted : validates_program helpers body generated = true) :
    ∃ lowered_helpers : List (Helper Target), ∃ target : Command Target, generated = render_program lowered_helpers target ∧
      LinkedHelperEquations lowered_helpers (link_helpers target_eval_with 0 lowered_helpers no_calls) ∧
      (∀ status, target_observes_with (link_helpers target_eval_with 0 lowered_helpers no_calls) target status ↔
        source_observes_with (link_helpers source_eval_with 0 helpers no_calls) body status) ∧
      (∀ outcome, Executes read_sparse write_sparse
        (target_commands_with (link_helpers target_eval_with 0 lowered_helpers no_calls) target) ∅ outcome →
          outcome.bounded read_sparse) := by
  simp only [validates_program, Bool.and_eq_true, beq_iff_eq] at accepted
  obtain ⟨linked, bounded, _, emitted⟩ := accepted
  exact ⟨helpers.map Helper.lower, body.map lower, emitted, lowered_helper_equations helpers linked, linked_program_correct helpers body,
    linked_execution_preserves_words helpers body linked bounded⟩

theorem certified_helper_uses_bound_arguments (helpers : List (Helper Source)) (body : Command Source)
    (generated : String) (accepted : validates_program helpers body generated = true)
    (slot : Nat) (helper : Helper Source) (found : helpers[slot]? = some helper) (inputs other : List Int)
    (bound_arguments : ∀ index, index < helper.arity → inputs[index]? = other[index]?) :
    let linked := link_helpers target_eval_with 0 (helpers.map Helper.lower) no_calls
    linked slot inputs = linked slot other := by
  simp only [validates_program, Bool.and_eq_true] at accepted
  exact lowered_helper_uses_bound_arguments helpers accepted.1 slot helper found inputs other bound_arguments

def validate_program (frontend generated : String) : Except String Unit :=
  match closed_source frontend with
  | .error message => .error message
  | .ok (.direct helpers body) =>
    if validates_program helpers body generated then .ok ()
    else .error "emitted program differs from verified lowering"
  | .ok (.framed helpers body) =>
    if !check_frame_helpers (helpers.toArray.map Helper.arity) helpers then
      .error "closed helper can fall through or use an out-of-scope call"
    else if validates_framed_program helpers body generated then .ok ()
    else .error "emitted program differs from verified framed lowering"

def ClosedProgram.haskell : ClosedProgram → String
  | .direct helpers body => render_program (helpers.map Helper.lower) (body.map lower)
  | .framed helpers body => render_framed_program (helpers.map lower_frame) (body.map lower)

def ClosedProgram.filc_exit : ClosedProgram → Int → Prop
  | .direct helpers body => source_observes_with (link_helpers source_eval_with 0 helpers no_calls) body
  | .framed helpers body => source_observes_exit helpers.toArray body

def ClosedProgram.haskell_exit : ClosedProgram → Int → Prop
  | .direct helpers body =>
    target_observes_with (link_helpers target_eval_with 0 (helpers.map Helper.lower) no_calls) (body.map lower)
  | .framed helpers body => fun status =>
    ∃ fuel, recursive_target_exit (helpers.toArray.map lower_frame) (body.map lower) fuel = some status

theorem checked_closed_source (frontend generated : String) (accepted : validate_program frontend generated = .ok ()) :
    ∃ program, closed_source frontend = .ok program ∧ generated = program.haskell := by
  cases parsed : closed_source frontend with
  | error why => simp [validate_program, parsed] at accepted
  | ok program =>
    refine ⟨program, rfl, ?_⟩
    cases program with
    | direct helpers body =>
      by_cases valid : validates_program helpers body generated = true
      · simp only [validates_program, Bool.and_eq_true, beq_iff_eq] at valid
        exact valid.2.2.2
      · simp [validate_program, parsed, valid] at accepted
    | framed helpers body =>
      by_cases checked : check_frame_helpers (helpers.toArray.map Helper.arity) helpers = true
      · by_cases valid : validates_framed_program helpers body generated = true
        · exact (framed_program_certificate_sound helpers body generated valid).1
        · simp at checked
          simp [validate_program, parsed, checked, valid] at accepted
      · have rejected := Bool.eq_false_iff.mpr checked
        simp at rejected
        simp [validate_program, parsed, rejected] at accepted

theorem closed_executable_exit_refines (input : Input) (artifact : Executable) (json generated : String)
    (frontend : Input → Except String String) (ghc : String → Except String Executable)
    (native_exit : Input → Int → Prop) (executable_exit : Executable → Int → Prop)
    (dumped : frontend input = .ok json) (built : ghc generated = .ok artifact)
    (certified : validate_program json generated = .ok ())
    (frontend_adequate : ∀ program : ClosedProgram, frontend input = .ok json → closed_source json = .ok program →
      ∀ status, native_exit input status ↔ program.filc_exit status)
    (ghc_host_adequate : ∀ program : ClosedProgram, ghc program.haskell = .ok artifact →
      ∀ status, executable_exit artifact status ↔ program.haskell_exit status) :
    ∀ status, executable_exit artifact status ↔ native_exit input status := by
  obtain ⟨program, parsed, rendered⟩ := checked_closed_source json generated certified
  have target := ghc_host_adequate program (rendered ▸ built)
  have source := frontend_adequate program dumped parsed
  intro status
  have model : program.haskell_exit status ↔ program.filc_exit status := by
    cases program with
    | direct helpers body => exact linked_program_correct helpers body status
    | framed helpers body => exact recursive_target_refines helpers.toArray body status
  exact (target status).trans (model.trans (source status).symm)

def validate_closed_text (input generated : String) : Except String Source := do
  let body ← Surface.parse input
  unless generated == render_program [] (.result (lower body)) do
    throw "emitted program differs from the verified C source lowering"
  return body

theorem checked_closed_text (input generated : String) (body : Source)
    (accepted : validate_closed_text input generated = .ok body) :
    (∃ tokens, Surface.Tokens input.toList tokens ∧ Surface.ProgramSyntax tokens body) ∧
      generated = render_program [] (.result (lower body)) ∧
      (∀ status, (ClosedProgram.direct [] (.result body)).haskell_exit status ↔
        (ClosedProgram.direct [] (.result body)).filc_exit status) := by
  unfold validate_closed_text at accepted
  cases parsed : Surface.parse input with
  | error reason => simp [parsed, bind, Except.bind] at accepted
  | ok decoded =>
    by_cases same : generated == render_program [] (.result (lower decoded))
    · simp [parsed, same, bind, Except.bind, pure, Except.pure] at accepted
      subst body
      exact ⟨(Surface.parse_correct input decoded).mp parsed, beq_iff_eq.mp same,
        linked_program_correct [] (.result decoded)⟩
    · simp [parsed, same, bind, Except.bind] at accepted

def closed_text_source_exit (input : String) (status : Int) : Prop :=
  ∃ tokens body, Surface.Tokens input.toList tokens ∧ Surface.ProgramSyntax tokens body ∧
    (ClosedProgram.direct [] (.result body)).filc_exit status

theorem closed_text_source_observations (input generated : String) (body : Source)
    (accepted : validate_closed_text input generated = .ok body) (status : Int) :
    (ClosedProgram.direct [] (.result body)).haskell_exit status ↔ closed_text_source_exit input status := by
  obtain ⟨⟨tokens, lexed, syntaxProof⟩, _, lowers⟩ := checked_closed_text input generated body accepted
  constructor
  · intro target
    exact ⟨tokens, body, lexed, syntaxProof, (lowers status).mp target⟩
  · rintro ⟨otherTokens, otherBody, otherLexed, otherSyntax, source⟩
    have parsed := (Surface.parse_correct input body).mpr ⟨tokens, lexed, syntaxProof⟩
    have otherParsed := (Surface.parse_correct input otherBody).mpr ⟨otherTokens, otherLexed, otherSyntax⟩
    have same := Except.ok.inj (parsed.symm.trans otherParsed)
    subst otherBody
    exact (lowers status).mpr source

def compile_closed_text (input : String) : Except String String := do
  let body ← Surface.parse input
  return render_program [] (.result (lower body))

theorem compile_closed_text_sound (input generated : String)
    (compiled : compile_closed_text input = .ok generated) :
    ∃ body, validate_closed_text input generated = .ok body ∧
      ∀ status, (ClosedProgram.direct [] (.result body)).haskell_exit status ↔ closed_text_source_exit input status := by
  cases parsed : Surface.parse input with
  | error reason => simp [compile_closed_text, parsed, bind, Except.bind] at compiled
  | ok body =>
    have rendered : render_program [] (.result (lower body)) = generated := by
      simpa [compile_closed_text, parsed, bind, Except.bind, pure, Except.pure] using compiled
    have accepted : validate_closed_text input generated = .ok body := by
      simp [validate_closed_text, parsed, rendered, bind, Except.bind, pure, Except.pure]
    exact ⟨body, accepted, closed_text_source_observations input generated body accepted⟩

theorem closed_native_haskell_agree (input generated : String) (body : Source) (file : List UInt8)
    (checked : validate_closed_text input generated = .ok body)
    (verified : Native.verify input file = .ok ()) (registers : Native.Registers) (status : Int) :
    (Int.ofNat <$> Native.execute file registers) = some status ↔
      (ClosedProgram.direct [] (.result body)).haskell_exit status := by
  exact (Native.verify_correct _ _ verified registers status).trans
    (closed_text_source_observations input generated body checked status).symm

theorem closed_text_executable_exit (input generated : String) (body : Source) (artifact : Executable)
    (ghc : String → Except String Executable) (executable_exit : Executable → Int → Prop)
    (accepted : validate_closed_text input generated = .ok body) (built : ghc generated = .ok artifact)
    (host_adequate : ghc (render_program [] (.result (lower body))) = .ok artifact →
      ∀ status, executable_exit artifact status ↔ (ClosedProgram.direct [] (.result body)).haskell_exit status) :
    ∀ status, executable_exit artifact status ↔ closed_text_source_exit input status := by
  obtain ⟨_, rendered, _⟩ := checked_closed_text input generated body accepted
  intro status
  exact (host_adequate (rendered ▸ built) status).trans (closed_text_source_observations input generated body accepted status)

def validates_process (generated : String) : Bool :=
  let nearestCoefficient := String.intercalate "\n" [
    "nearestCoefficient :: Rational -> Integer",
    "nearestCoefficient value =",
    "  if 2 * r < d || (2 * r == d && even q) then q else q + 1",
    "  where",
    "    d = denominator value",
    "    (q, r) = numerator value `divMod` d"]
  let decimalDigits := String.intercalate "\n" [
    "decimalDigits :: Int -> Bool -> Integer -> String",
    "decimalDigits precision negative coefficient",
    "  | precision == 0 = sign ++ digits",
    "  | otherwise = sign ++ integer ++ \".\" ++ fractional",
    "  where",
    "    sign = if negative then \"-\" else \"\"",
    "    digits = show coefficient",
    "    padded = replicate (max 0 (precision - length digits + 1)) '0' ++ digits",
    "    (integer, fractional) = splitAt (length padded - precision) padded"]
  let fixedExtended := String.intercalate "\n" [
    "fixedExtended :: Int -> ExtendedReal -> String",
    "fixedExtended _ (Infinite negative) = if negative then \"-inf\" else \"inf\"",
    "fixedExtended _ (NotANumber raw) = if testBit raw 79 then \"-nan\" else \"nan\"",
    "fixedExtended precision (Finite negative value) =",
    "  decimalDigits precision negative (nearestCoefficient (value * 10 ^ precision))"]
  let scientificExtended := String.intercalate "\n" [
    "scientificExtended :: Int -> ExtendedReal -> String",
    "scientificExtended precision (Finite negative magnitude) =",
    "  decimalDigits precision negative coefficient ++",
    "  \"e\" ++ (if power < 0 then \"-\" else \"+\") ++ replicate (max 0 (2 - length digits)) '0' ++ digits",
    "  where",
    "    guess = length (show (numerator magnitude)) - length (show (denominator magnitude))",
    "    decimalPower",
    "      | magnitude == 0 = 0",
    "      | magnitude < 10 ^^ guess = guess - 1",
    "      | otherwise = guess",
    "    scale = 10 ^ precision",
    "    rounded = nearestCoefficient (magnitude * fromInteger scale / 10 ^^ decimalPower)",
    "    (coefficient, power) = if rounded == 10 * scale then (scale, decimalPower + 1) else (rounded, decimalPower)",
    "    digits = show (abs power)",
    "scientificExtended precision value = fixedExtended precision value"]
  let bufferOutput := String.intercalate "\n" [
    "bufferOutput :: Bool -> OutputBuffer -> B.ByteString -> (Maybe B.ByteString, OutputBuffer)",
    "bufferOutput terminal before@(OutputBuffer line size chunks) input",
    "  | B.null input = (Nothing, before)",
    "  | B.length input > 1024 - size = flush input B.empty",
    "  | line, Just index <- B.elemIndexEnd '\\n' input =",
    "      let (prefix, suffix) = B.splitAt (index + 1) input in flush prefix suffix",
    "  | otherwise = (Nothing, OutputBuffer line (size + B.length input) (input : chunks))",
    "  where",
    "    flush prefix suffix = (Just (B.concat (reverse (prefix : chunks))),",
    "      OutputBuffer terminal (B.length suffix) [suffix | not (B.null suffix)])"]
  let sendOutput := String.intercalate "\n" [
    "sendOutput :: B.ByteString -> IO (Either IOError ())",
    "sendOutput bytes = tryIOError (B.hPut stdout bytes >> hFlush stdout)"]
  let writeOutput := String.intercalate "\n" [
    "writeOutput :: [B.ByteString] -> R Bool",
    "writeOutput inputs = do",
    "  (terminal, lock) <- gets outputStream",
    "  let write buffer [] = pure (buffer, True)",
    "      write buffer (chunk : rest) = case bufferOutput terminal buffer chunk of",
    "        (Nothing, next) -> write next rest",
    "        (Just bytes, next) -> do",
    "          sent <- sendOutput bytes",
    "          case sent of",
    "            Left _ -> pure (OutputBuffer terminal 0 [], False)",
    "            Right () -> write next rest",
    "  liftIO (modifyMVar lock (\\buffer -> write buffer inputs))"]
  let printBytes := String.intercalate "\n" [
    "printBytes :: String -> R Value",
    "printBytes text = do",
    "  sent <- writeOutput [B.pack text]",
    "  pure (Number (if sent then toInteger (length text) else -1))"]
  let output_calls := String.intercalate "\n" [
    "builtin \"puts\" [p] = do",
    "  text <- readString p",
    "  sent <- writeOutput [B.pack text, B.singleton '\\n']",
    "  pure (Number (if sent then 0 else -1))",
    "builtin \"putchar\" [v] = do",
    "  let byte = number v `mod` 256",
    "  sent <- writeOutput [B.singleton (chr (fromInteger byte))]",
    "  pure (Number (if sent then byte else -1))",
    "builtin \"printf\" (p : values) = readString p >>= \\pattern -> format takeValue pattern values >>= printBytes",
    "builtin \"vprintf\" [p, list] = readString p >>= \\pattern -> format takeVariadic pattern list >>= printBytes"]
  let transformer := String.intercalate "\n" [
    "newtype R a = R { unR :: ExceptT Fault (StateT World IO) a }",
    "  deriving (Functor, Applicative, Monad, MonadIO, MonadState World, MonadError Fault)",
    "",
    "runWorld :: World -> R a -> IO (Either Fault a, World)",
    "runWorld world action = runStateT (runExceptT (unR action)) world"]
  let finish := "builtin \"exit\" [code] = throwError (Finish (fromInteger (number code `mod` 256)))"
  let stream_seed := String.intercalate "\n" [
    "  table <- newIORef (1, M.empty)",
    "  terminal <- either (const False) id <$> tryIOError (hIsTerminalDevice stdout)",
    "  output <- newMVar (OutputBuffer True 0 [])"]
  let stream_lookup := String.intercalate "\n" [
    "stream :: Value -> R Handle",
    "stream (Stream ident raw) = do",
    "  unless (raw == 4611686018427387904 + toInteger ident) (panic \"closed or invalid file stream\")",
    "  table <- gets streamTable >>= liftIO . readIORef",
    "  let handle = M.lookup ident (snd table)",
    "  maybe (panic \"closed or invalid file stream\") pure handle",
    "stream _ = panic \"file operation requires a valid stream\""]
  let register := String.intercalate "\n" [
    "  opened <- liftIO (tryIOError (openBinaryFile name selected))",
    "  case opened of",
    "    Left _ -> pure nullPointer",
    "    Right handle -> do",
    "      entry <- liftIO $ atomicModifyIORef' table $ \\old@(ident, entries) ->",
    "        if toInteger ident >= 4611686018427387904 then (old, Nothing)",
    "        else ((ident + 1, M.insert ident handle entries), Just ident)",
    "      ident <- case entry of",
    "        Nothing -> io (hClose handle) >> panic \"stream identity space exhausted\"",
    "        Just available -> pure available",
    "      pure (Stream ident (4611686018427387904 + toInteger ident))"]
  let close := String.intercalate "\n" [
    "builtin \"fclose\" [Stream ident raw] = do",
    "  unless (raw == 4611686018427387904 + toInteger ident) (panic \"closed or invalid file stream\")",
    "  table <- gets streamTable",
    "  result <- liftIO $ E.mask_ $ do",
    "    claimed <- atomicModifyIORef' table $ \\(next, entries) ->",
    "      let (handle, remaining) = M.updateLookupWithKey (\\_ _ -> Nothing) ident entries",
    "      in ((next, remaining), handle)",
    "    traverse (tryIOError . hClose) claimed",
    "  case result of",
    "    Nothing -> panic \"closed or invalid file stream\"",
    "    Just closed -> pure (Number (either (const (-1)) (const 0) closed))"]
  let file_read := String.intercalate "\n" [
    "builtin \"fread\" [destination, size, count, value] = do",
    "  total <- transferSize size count",
    "  handle <- stream value",
    "  if total == 0 then pure (Number 0) else do",
    "    (_, object, _) <- checked total destination",
    "    when (readOnly object) (panic \"file read into read-only memory\")",
    "    payload <- io (B.hGet handle total)",
    "    locked $ do",
    "      (ident, updatedObject, displacement) <- checked total destination",
    "      when (readOnly updatedObject) (panic \"file read into read-only memory\")",
    "      let updated = B.foldl' (\\(i, m) byte -> (i + 1, M.insert i (toInteger (ord byte)) m)) (displacement, bytes updatedObject) payload",
    "      writeObject ident (updatedObject { bytes = snd updated })",
    "      event (\"read \" ++ show (B.length payload) ++ \" bytes into #\" ++ show ident)",
    "    pure (Number (toInteger (B.length payload) `div` number size))"]
  let file_write := String.intercalate "\n" [
    "builtin \"fwrite\" [source, size, count, value] = do",
    "  total <- transferSize size count",
    "  handle <- stream value",
    "  if total == 0 then pure (Number 0) else do",
    "    (_, object, displacement) <- checked total source",
    "    let payload = B.pack [chr (fromInteger (M.findWithDefault 0 (displacement + i) (bytes object))) | i <- [0 .. total - 1]]",
    "    io (B.hPut handle payload)",
    "    event (\"write \" ++ show total ++ \" bytes\")",
    "    pure count"]
  let epilogue := String.intercalate "\n" [
    "  outcome <- E.try (runWorld initial action)",
    "  let (result, final) = either (\\fault -> (Left fault, initial)) id outcome",
    "  handles <- snd <$> readIORef table",
    "  forM_ (M.elems handles) (void . tryIOError . hClose)",
    "  let flushOutput = modifyMVar_ output $ \\(OutputBuffer line _ chunks) -> do",
    "        void (sendOutput (B.concat (reverse chunks)))",
    "        pure (OutputBuffer line 0 [])",
    "  case result of",
    "    Right _ -> flushOutput",
    "    Left (Finish _) -> flushOutput",
    "    _ -> pure ()",
    "  case result of",
    "    Right value -> let code = fromInteger (number value `mod` 256) in exitWith (if code == 0 then ExitSuccess else ExitFailure code)",
    "    Left (Finish code) -> exitWith (if code == 0 then ExitSuccess else ExitFailure code)",
    "    Left (Transfer _) -> hPutStrLn stderr \"heresy panic: control transfer escaped its function\" >> exitWith (ExitFailure 70)",
    "    Left (Panic message) -> do",
    "      hPutStrLn stderr (\"heresy panic: \" ++ message)",
    "      unless (enabled || null (recent final)) $ hPutStrLn stderr (intercalate \"\\n\" (reverse (recent final)))",
    "      exitWith (ExitFailure 70)"]
  [bufferOutput, sendOutput, writeOutput, printBytes, output_calls, nearestCoefficient, decimalDigits, fixedExtended, scientificExtended, transformer, finish, stream_seed, stream_lookup, register, close, file_read, file_write, epilogue].all
    (fun equation => (generated.splitOn ("\n" ++ equation ++ "\n")).length == 2)

def validates_aggregate_memory (generated : String) : Bool :=
  let load := "        AggregateType size alignment -> Aggregate size alignment (aggregateBytes displacement size (bytes object)) (aggregateShadow displacement size (shadow object))"
  let store := String.intercalate "\n" [
    "storeCell (AggregateType size _) pointer value@(Aggregate actual _ payload caps) | size == actual = do",
    "  (ident, object, displacement) <- checked size pointer",
    "  when (readOnly object) (panic \"write to read-only memory\")",
    "  when (not (M.null caps) && number pointer `mod` 8 /= 0) (panic \"unaligned aggregate pointer store\")",
    "  let replace start count new old =",
    "        let before = M.takeWhileAntitone (< start) old",
    "            after = M.dropWhileAntitone (< start + count) old",
    "        in M.unions [before, M.mapKeysMonotonic (+ start) new, after]",
    "      firstWord = ((displacement + 7) `div` 8) * 8",
    "      pastWords = max firstWord (displacement + size - 7)",
    "      updated = replace displacement size payload (bytes object)",
    "      retained = M.union (M.takeWhileAntitone (< firstWord) (shadow object)) (M.dropWhileAntitone (< pastWords) (shadow object))",
    "      capabilities = M.union (M.mapKeysMonotonic (+ displacement) caps) retained",
    "      modes = I.filter (\\i -> i < firstWord || i >= pastWords) (atomicSlots object)",
    "  writeObject ident (object { bytes = updated, shadow = capabilities, atomicSlots = modes })",
    "  pure value"]
  [load, store].all (fun equation => (generated.splitOn ("\n" ++ equation ++ "\n")).length == 2)

def validates_atomic_memory (generated : String) : Bool :=
  let transfer := String.intercalate "\n" [
    "atomicTransfer :: String -> CType -> R Value -> [R Value] -> R Value",
    "atomicTransfer op ty target operands = do",
    "  pointer <- target",
    "  values <- sequence operands",
    "  let ordinary = plainType ty",
    "  locked $ do",
    "    _ <- case (op, values) of",
    "      (\"load\", [_, destination]) -> loadCell ty pointer >>= storeCell ordinary destination",
    "      (\"store\", [_, source]) -> loadCell ordinary source >>= storeCell ty pointer",
    "      (\"exchange\", [_, source, destination]) -> do",
    "        desired <- loadCell ordinary source",
    "        old <- loadCell ty pointer",
    "        void (storeCell ty pointer desired)",
    "        storeCell ordinary destination old",
    "      _ -> panic \"invalid atomic transfer operands\"",
    "    pure (Number 0)"]
  let compare := String.intercalate "\n" [
    "atomicCompare :: Bool -> CType -> R Value -> R Value -> R Value -> R Value -> R Value -> R Value",
    "atomicCompare indirect ty target successOrder expected failureOrder desired = do",
    "  pointer <- target",
    "  void successOrder",
    "  expectation <- expected",
    "  void failureOrder",
    "  desiredValue <- desired",
    "  locked $ do",
    "    let ordinary = plainType ty",
    "        bits value = case value of Aggregate _ _ payload _ -> decodeBytes payload; _ -> number value",
    "    replacement <- if indirect then loadCell ordinary desiredValue else pure desiredValue",
    "    old <- loadCell ty pointer",
    "    wanted <- loadCell ordinary expectation",
    "    (_, object, _) <- checked (widthOf ty) pointer",
    "    when (readOnly object) (panic \"write to read-only memory\")",
    "    matches <- case (ty, old, wanted) of",
    "      (AtomicAggregate _ _ AtomicCopy, Aggregate _ _ actual _, Aggregate _ _ expectedBytes _) ->",
    "        pure (M.filter (/= 0) actual == M.filter (/= 0) expectedBytes)",
    "      (AtomicAggregate width _ AtomicBytes, _, _) | width /= widthOf ordinary -> do",
    "        observed <- loadCell (IntegerType (8 * width) False) pointer",
    "        pure (number observed == bits wanted)",
    "      _ -> pure (bits old == bits wanted)",
    "    if matches then storeCell ty pointer replacement >> pure (boolean True) else do",
    "      case ty of",
    "        AtomicAggregate width _ AtomicBytes ->",
    "          when (width == widthOf ordinary) $",
    "            void (storeCell (IntegerType (8 * width) False) expectation (Number (bits old)))",
    "        _ -> void (storeCell ordinary expectation old)",
    "      pure (boolean False)"]
  [transfer, compare].all (generated.splitOn "\n\n").contains

def validates_pointer_memory (generated : String) : Bool :=
  let width := "widthOf PointerType = 8"
  let checked_load := String.intercalate "\n" [
    "loadCell declared pointer = do",
    "  let ty = case declared of AtomicType inner -> inner; other -> other",
    "  (ident, object, displacement) <- checked (widthOf declared) pointer",
    "  when (ty == PointerType && number pointer `mod` 8 /= 0) (panic \"unaligned pointer load\")",
    "  let raw = readScalar displacement (widthOf ty) (bytes object)"]
  let load := String.intercalate "\n" [
    "        PointerType -> case M.lookup displacement (shadow object) of",
    "          Just stored | declared == AtomicType PointerType && I.member displacement (atomicSlots object) -> stored",
    "          Just (Pointer cap _) -> Pointer cap raw",
    "          Just (Function _ name) -> Function raw name",
    "          Just (Stream streamId _) -> Stream streamId raw",
    "          _ -> Pointer NoCapability raw"]
  let checked_store := String.intercalate "\n" [
    "storeCell declared pointer value = do",
    "  let ty = case declared of AtomicType inner -> inner; other -> other",
    "  (ident, object, displacement) <- checked (widthOf declared) pointer",
    "  when (readOnly object) (panic \"write to read-only memory\")",
    "  when (ty == PointerType && number pointer `mod` 8 /= 0) (panic \"unaligned pointer store\")",
    "  let converted = cast ty value"]
  let store := String.intercalate "\n" [
    "      updated = writeScalar displacement (widthOf ty) raw (bytes object)",
    "      caps = if ty == PointerType then M.insert displacement converted (shadow object) else shadow object"]
  [width, checked_load, load, checked_store, store].all (fun equation => (generated.splitOn ("\n" ++ equation ++ "\n")).length == 2)

private structure OrdinaryShape where
  element : String
  width : Nat
  dimensions : List String

private inductive OrdinaryStorage where
  | scalar (ty : Ordinary.TypeCode)
  | array (element : String) (ty : Ordinary.TypeCode) (count : Nat)
  | record (layout : Ordinary.RecordLayout)
  | dynamicArray (shape : OrdinaryShape)
  | vaList

private def OrdinaryStorage.width : OrdinaryStorage → Nat
  | .scalar ty => ty.width
  | .array _ ty count => count * ty.width
  | .record layout => layout.width
  | .dynamicArray _ => 0
  | .vaList => 24

private def OrdinaryStorage.frame_width : OrdinaryStorage → Option Nat
  | .dynamicArray _ => none
  | storage => some storage.width

private def ordinary_record_code (layout : Ordinary.RecordLayout) : Option Ordinary.TypeCode :=
  match layout.width with
  | 0 => none
  | last + 1 => some (.aggregate last layout.alignment)

private def OrdinaryStorage.value_type : OrdinaryStorage → Option Ordinary.TypeCode
  | .scalar ty => some ty
  | .record layout => ordinary_record_code layout
  | _ => none

private structure OrdinaryPointerShape where
  probe : String
  shape : OrdinaryShape
  skip : Nat
  bounds : Option (List (Sum Nat Json))

private structure OrdinaryLocal where
  ident : String
  name : String
  spelling : String
  storage : OrdinaryStorage
  kind : String
  slot : Nat
  pointerShape : Option OrdinaryPointerShape := none

private structure OrdinarySignature where
  name : String
  symbol : String
  spelling : String
  result : String
  ty : Option Ordinary.TypeCode
  parameters : List OrdinaryLocal
  declarations : List String
  entry : Json
  records : List Ordinary.RecordLayout
  variadic : Bool := false
  functions : List String := []

private structure OrdinaryUnit where
  namespaceName : String
  budget : Nat
  tree : Json
  declarations : List Json
  objects : List Json
  records : List Ordinary.RecordLayout
  labels : List (String × String)
  usesStreams : Bool
  spawns : Bool
  statics : List (String × Json) := []

private structure OrdinaryCallback where
  alias : String
  reference : String
  result : String
  deriving BEq

private structure OrdinaryObject where
  name : String
  symbol : String
  spelling : String
  storage : OrdinaryStorage
  definition : Json
  identities : List String
  recordTarget : Option Ordinary.RecordLayout
  records : List Ordinary.RecordLayout
  readOnly : Bool := false
  callback : Option OrdinaryCallback := none
  owner : Option String := none

private def array_pointer_parts (spelling : String) : Option (String × String) := do
  let [element, suffix] := spelling.splitOn " (*)" | none
  guard (suffix.startsWith "[" && suffix.endsWith "]")
  return (element, suffix)

private def array_slot_pointee (spelling : String) : Option String := do
  let [base, suffix] := spelling.splitOn " (" | none
  let [stars, dimensions] := suffix.splitOn ")" | none
  guard (stars.length ≥ 2 && stars.toList.all (· == '*') && dimensions.startsWith "[" && dimensions.endsWith "]")
  return base ++ " (" ++ stars.drop 1 ++ ")" ++ dimensions

private def ordinary_integer_type : String → Option Ordinary.TypeCode
  | "const unsigned char" | "unsigned char" => some .byte
  | "const signed char" | "const char" | "char" | "signed char" => some .signedByte
  | "int" => some .integer
  | "unsigned int" => some .unsignedInt
  | "short" | "short int" | "signed short" => some .short
  | "unsigned short" | "unsigned short int" => some .unsignedShort
  | "long" | "long int" | "long long" | "long long int" => some .long
  | "unsigned long" | "unsigned long int" | "unsigned long long" | "unsigned long long int" => some .size
  | "__int128" => some .wide
  | "unsigned __int128" => some .unsignedWide
  | _ => none

private def atomic_underlying (spelling : String) : Option String := do
  guard (spelling.startsWith "_Atomic(" && spelling.endsWith ")")
  return (spelling.drop 8).take (spelling.length - 9)

private def simple_data_pointee (spelling : String) : Option String := do
  if spelling.endsWith " *" then
    let base := spelling.take (spelling.length - 2)
    if (atomic_underlying base).isSome then return base
  let [base, stars] := spelling.splitOn " *" | none
  guard (stars.toList.all (· == '*'))
  let plain := if base.startsWith "const " then base.drop 6 else base
  guard (["void", "float", "double", "long double"].contains plain || (ordinary_integer_type plain).isSome ||
    plain.startsWith "struct " || plain.startsWith "union ")
  return if stars.isEmpty then base else spelling.take (spelling.length - 1)

private def data_pointee (spelling : String) : Option String := do
  if spelling.endsWith "*const *" then
    let base := (spelling.take (spelling.length - 2))
    guard ((simple_data_pointee (base.take (base.length - 5))).isSome)
    return base
  if spelling.endsWith "*const" then return ← simple_data_pointee (spelling.take (spelling.length - 5))
  simple_data_pointee spelling

private def function_prototype (spelling : String) : Option (String × List String) := do
  let [result, tail] := (spelling.replace "(*const)" "(*)").splitOn "(*)(" | none
  guard (tail.endsWith ")")
  let result := result.trim
  let text := tail.take (tail.length - 1)
  let args := if text == "void" then [] else text.splitOn ", "
  let scalar := fun name => (ordinary_integer_type name).isSome || (data_pointee name).isSome
  guard ((result == "void" || scalar result) && args.all scalar)
  return (result, args)

private def function_slot_pointee (spelling : String) : Option String := do
  if let [head, args] := spelling.splitOn "(*const *)(" then
    if (function_prototype (head ++ "(*)(" ++ args)).isSome then return head ++ "(*const)(" ++ args
  let [result, stars, arguments] := spelling.splitOn "(" | none
  guard (stars.endsWith ")" && stars.length ≥ 3 && (stars.take (stars.length - 1)).toList.all (· == '*'))
  guard ((function_prototype (result ++ "(*)(" ++ arguments)).isSome)
  return result ++ "(" ++ stars.drop 1 ++ "(" ++ arguments

private def callback_array_pointee (spelling : String) : Option String := do
  let [head, tail] := spelling.splitOn "(*(*)" | none
  let [bounds, args] := tail.splitOn ")(" | none
  guard (bounds.startsWith "[" && bounds.endsWith "]" && (function_prototype (head ++ "(*)(" ++ args)).isSome)
  return head ++ "(*" ++ bounds ++ ")(" ++ args

private def ordinary_type (spelling : String) : Option Ordinary.TypeCode :=
  if spelling == "_Complex float" then some .complex32
  else if spelling == "_Complex double" then some .complex64
  else if spelling == "_Complex long double" then some .complex80
  else if spelling == "float" then some .binary32
  else if spelling == "double" then some .binary64
  else if spelling == "long double" then some .extended
  else if (data_pointee spelling).isSome || (array_pointer_parts spelling).isSome || (callback_array_pointee spelling).isSome ||
      (function_prototype spelling).isSome || (array_slot_pointee spelling).isSome || (function_slot_pointee spelling).isSome then some .pointer
  else ordinary_integer_type spelling

private def ordinary_pointee (spelling : String) : String :=
  match array_pointer_parts spelling with
  | some (element, dimensions) => element ++ dimensions
  | none => ((data_pointee spelling) <|> callback_array_pointee spelling <|> array_slot_pointee spelling <|> function_slot_pointee spelling).getD ""

private def fixed_dimensions (spelling : String) : Option (String × List Nat) := do
  let base :: bounds := spelling.splitOn "[" | none
  guard (!bounds.isEmpty)
  let sizes ← bounds.mapM fun bound => do
    guard (bound.endsWith "]")
    let size ← (bound.take (bound.length - 1)).toNat?
    guard (0 < size)
    return size
  return (base.trim, sizes)

private def callback_array (spelling : String) : Option (String × String × List Nat × String) := do
  let [head, suffix] := spelling.splitOn "(*" | none
  let [shape, args] := suffix.splitOn ")(" | none
  let (qualifier, sizes) ← fixed_dimensions shape
  guard ((qualifier.isEmpty || qualifier == "const") && (function_prototype (head ++ "(*)(" ++ args)).isSome)
  return (head, qualifier, sizes, args)

private def ordinary_array (spelling : String) : Option (String × Nat) := do
  if let some (head, qualifier, count :: inner, args) := callback_array spelling then
    let bounds := String.join (inner.map (fun size => "[" ++ toString size ++ "]"))
    return (head ++ "(*" ++ qualifier ++ bounds ++ ")(" ++ args, count)
  let (base, count :: inner) ← fixed_dimensions spelling | none
  return (base ++ String.join (inner.map (fun size => "[" ++ toString size ++ "]")), count)

private def ordinary_value_type (records : List Ordinary.RecordLayout) (spelling : String) : Option Ordinary.TypeCode :=
  ordinary_type spelling <|> ((records.find? (·.spelling == spelling)).bind ordinary_record_code)

private def record_has_pointer (records : List Ordinary.RecordLayout) : Nat → String → Bool
  | 0, _ => false
  | depth + 1, spelling =>
    if ordinary_type spelling == some .pointer then true else
    let base := (fixed_dimensions spelling).map Prod.fst |>.getD spelling
    ordinary_type base == some .pointer || (records.find? (·.spelling == base)).any fun record =>
      record.fields.any (fun field => record_has_pointer records depth field.spec.spelling)

private def atomic_record (records : List Ordinary.RecordLayout) (spelling : String) (promote : Bool) :
    Option Ordinary.TypeCode := do
  let record ← records.find? (·.spelling == spelling)
  guard (0 < record.width)
  let rounded := ([1, 2, 4, 8, 16].find? (record.width ≤ ·)).getD record.width
  let width := if promote then rounded else record.width
  let mode := if width > 16 || (!promote && (rounded != width || record.alignment < width)) then Ordinary.AtomicMode.copy
    else if width == 8 && record.width == 8 && record_has_pointer records (records.length + 1) spelling then .capability
    else .bytes
  return .atomicRecord (record.width - 1) record.alignment (width - 1) mode

private def ordinary_element (records : List Ordinary.RecordLayout) (spelling : String) : Option Ordinary.TypeCode := do
  let spelling := if spelling.startsWith "volatile " then spelling.drop 9 else spelling
  let spelling := if spelling.endsWith "*volatile" then spelling.dropRight 8 else spelling.replace "*volatile[" "*["
  if let some ty := ordinary_value_type records spelling then return ty
  if let some (_, _, bounds, _) := callback_array spelling then
    let width := bounds.foldl (· * ·) 8
    guard (0 < width && width ≤ 9223372036854775800)
    return .aggregate (width - 1) 8
  let (base, bounds) ← fixed_dimensions spelling
  let ty ← ordinary_value_type records base
  let width := bounds.foldl (· * ·) ty.width
  guard (0 < width && width ≤ 9223372036854775800)
  return .aggregate (width - 1) ty.alignment

private def ordinary_ident (node : Json) : String :=
  field_text (json_field node "referencedDecl") "id"

private def ordinary_name (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun c => c.isAlphanum || c == '_' || c.toNat ≥ 128)

private def ordinary_packed_record (spelling : String) (node : Json) : Option Ordinary.RecordLayout := do
  let [size, alignment, dump] := (← (json_field node "heresyLayout").getArr?.toOption).toList | none
  let width ← size.getNat?.toOption
  guard (alignment.getNat?.toOption == some 1 && width > 0)
  let children := child_nodes node
  let [packedAttr] := children.filter (fun part => field_text part "kind" == "PackedAttr") | none
  guard ((child_nodes packedAttr).isEmpty)
  let members := children.filter (fun part => field_text part "kind" != "PackedAttr")
  let entries := (← dump.getArr?.toOption).toList
  guard (entries.length == members.length)
  let mut fields : List Ordinary.Field := []
  let mut cursor := 0
  for (member, entry) in members.zip entries do
    let [offset, count] := (← entry.getArr?.toOption).toList | none
    let offset ← offset.getNat?.toOption
    let name := field_text member "name"
    let id := field_text member "id"
    let ty ← ordinary_integer_type (type_spelling member)
    guard (field_text member "kind" == "FieldDecl" && !id.isEmpty)
    let mut start := cursor
    let mut bitWidth := none
    if json_field member "isBitfield" == .bool true then
      let [constant] := child_nodes member | none
      guard (field_text constant "kind" == "ConstantExpr" && (ordinary_integer_type (type_spelling constant)).isSome)
      let bits ← (field_text constant "value").toNat?
      guard (count.getNat?.toOption == some bits && bits ≤ 8 * ty.width)
      if bits == 0 then
        guard (name.isEmpty)
        start := (aligned_slot cursor 0 (8 * ty.alignment)).1
      else
        bitWidth := some (bits - 1)
      cursor := start + bits
    else
      guard (ordinary_name name && count == .null && (child_nodes member).isEmpty)
      start := (aligned_slot cursor 0 8).1
      cursor := start + 8 * ty.width
    guard (offset == start)
    if !name.isEmpty then
      guard (ordinary_name name)
      fields := ⟨⟨id, name, type_spelling member, ty, bitWidth⟩, start / 8, start % 8⟩ :: fields
  guard ((cursor + 7) / 8 == width && decide ((fields.map (·.spec.identity)).Nodup) &&
    decide ((fields.map (·.spec.name)).Nodup))
  Ordinary.checked_packed_layout spelling fields.reverse width

private def ordinary_record (records : List Ordinary.RecordLayout) (node : Json) : Option Ordinary.RecordLayout := do
  let name := field_text node "name"
  let tag := field_text node "tagUsed"
  let named := ordinary_name name || (name.startsWith "@" && (name.drop 1).toNat?.isSome)
  guard (field_text node "kind" == "RecordDecl" && ["struct", "union"].contains tag &&
    json_field node "completeDefinition" == .bool true && named && !(child_nodes node).isEmpty)
  if (child_nodes node).any (fun part => field_text part "kind" == "PackedAttr") then
    guard (tag == "struct")
    let layout ← ordinary_packed_record (tag ++ " " ++ name) node
    let original := field_text node "heresyRecordTag"
    return { layout with original := if ordinary_name original then tag ++ " " ++ original else "" }
  let members := (child_nodes node).filter (fun part => field_text part "kind" != "RecordDecl")
  guard (members.all (fun member => field_text member "kind" == "FieldDecl" ||
    (field_text member "kind" == "IndirectFieldDecl" && json_field member "isImplicit" == .bool true &&
      ordinary_name (field_text member "name") && (child_nodes member).isEmpty)))
  let fields ← (members.filter (fun part => field_text part "kind" == "FieldDecl")).mapM fun member => do
    let identity := field_text member "id"
    let name := field_text member "name"
    let spelling := type_spelling member
    let ty ← ordinary_element records spelling
    let anonymous := name.isEmpty && json_field member "isImplicit" == .bool true &&
      records.any (·.spelling == spelling)
    guard ((ordinary_name name || anonymous) && !identity.isEmpty)
    let bits ← if json_field member "isBitfield" == .bool true then do
      let [constant] := child_nodes member | none
      guard (field_text constant "kind" == "ConstantExpr" && (ordinary_integer_type spelling).isSome)
      let width ← (field_text constant "value").toNat?
      guard (0 < width && width ≤ 8 * ty.width)
      pure (some (width - 1))
    else do
      guard ((child_nodes member).isEmpty)
      pure none
    pure (⟨identity, name, spelling, ty, bits⟩ : Ordinary.FieldSpec)
  guard (!fields.isEmpty && decide ((fields.map (·.identity)).Nodup) &&
    decide (((fields.map (·.name)).filter (!·.isEmpty)).Nodup))
  let spelling := tag ++ " " ++ name
  let layout := if tag == "union" then Ordinary.union_layout spelling fields
    else if fields.any (·.bits.isSome) then Ordinary.bit_record_layout spelling fields
    else Ordinary.record_layout spelling fields
  let original := field_text node "heresyRecordTag"
  return { layout with original := if ordinary_name original then tag ++ " " ++ original else "" }

private def collect_records : Nat → List Ordinary.RecordLayout → Json → Except String (List Ordinary.RecordLayout)
  | 0, _, _ => .error "ordinary record nesting exceeds the frontend budget"
  | depth + 1, records, node => do
    let nested := (child_nodes node).filter fun child => field_text child "kind" == "RecordDecl"
    let records ← nested.foldlM (collect_records depth) records
    return match ordinary_record records node with
      | some layout => layout :: records
      | none => records

private def inline_record (records : List Ordinary.RecordLayout) (uses : List Json) (entry : Json) :
    Option Ordinary.RecordLayout := do
  let [key, size, alignment, dump] := (← entry.getArr?.toOption).toList | none
  let spelling ← key.getStr?.toOption
  let [tag, index] := spelling.splitOn " @layout" | none
  guard (["struct", "union"].contains tag && index.toNat?.isSome)
  let width ← size.getNat?.toOption
  let align ← alignment.getNat?.toOption
  let union := tag == "union"
  let mut cursor := 0
  let mut natural := 1
  let mut fields : List Ordinary.Field := []
  for (item, i) in (← dump.getArr?.toOption).toList.zipIdx do
    let [label, type, position, count] := (← item.getArr?.toOption).toList | none
    let name ← label.getStr?.toOption
    let member ← type.getStr?.toOption
    let ty ← ordinary_element records member
    let offset ← position.getNat?.toOption
    let bits ← if count == .null then pure none else some <$> count.getNat?.toOption
    let unit := 8 * ty.alignment
    let start := if union then 0 else match bits with
      | some (n + 1) => if cursor % unit + n + 1 ≤ 8 * ty.width then cursor else (aligned_slot cursor 0 unit).1
      | _ => (aligned_slot cursor 0 unit).1
    guard (offset == start)
    let span := bits.getD (8 * ty.width)
    cursor := max cursor (start + span)
    if bits.isSome then
      guard ((ordinary_integer_type member).isSome && span ≤ 8 * ty.width && (span > 0 || name.isEmpty))
    if !(name.isEmpty && bits.isSome) then
      guard (ordinary_name name || (name.isEmpty && records.any (·.spelling == member)))
      natural := max natural ty.alignment
      let referenced := uses.filterMap fun node => Id.run do
        if field_text node "kind" == "InitListExpr" && type_spelling node == spelling then
          let field := json_field node "field"
          if field_text field "name" == name && type_spelling field == member then return some (field_text field "id")
        let [base] := child_nodes node | return none
        let baseType := if json_field node "isArrow" == .bool true then ordinary_pointee (type_spelling base) else type_spelling base
        if field_text node "kind" == "MemberExpr" && baseType == spelling && field_text node "name" == name &&
            type_spelling node == member then return some (field_text node "referencedMemberDecl")
        return none
      let identities := referenced.eraseDups
      guard (identities.length ≤ 1)
      let identity := identities.head?.getD (spelling ++ "#" ++ toString i)
      guard (!identity.isEmpty)
      fields := ⟨⟨identity, name, member, ty, bits.map (· - 1)⟩, start / 8, start % 8⟩ :: fields
  guard (natural == align && width > 0 && (aligned_slot ((cursor + 7) / 8) 0 align).1 == width &&
    fields.all (fun field => field.offset + field.access.width ≤ width) &&
    decide ((fields.map (·.spec.identity)).Nodup) && decide (((fields.map (·.spec.name)).filter (!·.isEmpty)).Nodup))
  return ⟨spelling, fields.reverse, width, align, union, ""⟩

private def ordinary_storage (records : List Ordinary.RecordLayout) (spelling : String) : Option OrdinaryStorage :=
  if let some inner := atomic_underlying spelling then do
    let ty ← ordinary_integer_type inner <|> ((data_pointee inner).map fun _ => .pointer) <|> atomic_record records inner true
    return .scalar ty
  else if spelling == "struct __va_list_tag[1]" then some .vaList
  else if (array_pointer_parts spelling).isSome || (array_slot_pointee spelling).isSome || (callback_array_pointee spelling).isSome then some (.scalar .pointer)
  else if let some (element, count) := ordinary_array spelling then do
    return .array element (← ordinary_element records element) count
  else if let some ty := ordinary_type spelling then some (.scalar ty)
  else (records.find? (·.spelling == spelling)).map .record

private def ordinary_record_compatible (left right : List Ordinary.RecordLayout) :
    Nat → Ordinary.RecordLayout → Ordinary.RecordLayout → Bool
  | 0, _, _ => false
  | depth + 1, first, other =>
    first.isUnion == other.isUnion && first.width == other.width && first.alignment == other.alignment &&
    first.fields.length == other.fields.length && (first.fields.zip other.fields).all fun (a, b) =>
      a.spec.name == b.spec.name && a.offset == b.offset && a.shift == b.shift && a.spec.bits == b.spec.bits &&
      a.spec.ty == b.spec.ty &&
      let (atyp, ashape) := (fixed_dimensions a.spec.spelling).getD (a.spec.spelling, [])
      let (btyp, bshape) := (fixed_dimensions b.spec.spelling).getD (b.spec.spelling, [])
      ashape == bshape && match left.find? (·.spelling == atyp), right.find? (·.spelling == btyp) with
      | none, none => atyp == btyp
      | some x, some y =>
        (if x.original.isEmpty && y.original.isEmpty then x.spelling == y.spelling else x.original == y.original) &&
        ordinary_record_compatible left right depth x y
      | _, _ => false

private def ordinary_abi_type (left right : List Ordinary.RecordLayout) (expected actual : String) : Bool :=
  let target := if expected.endsWith " *" then ordinary_pointee expected else expected
  let incoming := if actual.endsWith " *" then ordinary_pointee actual else actual
  match left.find? (·.spelling == target), right.find? (·.spelling == incoming) with
  | none, none => expected == actual
  | some first, some other =>
    expected.endsWith " *" == actual.endsWith " *" &&
      (if first.original.isEmpty && other.original.isEmpty then expected == actual else first.original == other.original) &&
      ordinary_record_compatible left right (left.length + 1) first other
  | _, _ => false

private def ordinary_decl (node : Json) (spelling : String) : Bool :=
  !spelling.isEmpty && type_spelling node == spelling

private def ordinary_member (records : List Ordinary.RecordLayout) (node base : Json) : Except String Ordinary.Field := do
  let indirect := json_field node "isArrow" == .bool true
  let recordType := if indirect then ordinary_pointee (type_spelling base) else type_spelling base
  let layout ← require (records.find? (·.spelling == recordType)) "unsupported ordinary record member base"
  let identity := field_text node "referencedMemberDecl"
  let member ← require (layout.fields.find? (·.spec.identity == identity)) "unknown ordinary record member identity"
  let category := field_text node "valueCategory"
  unless ordinary_decl node member.spec.spelling && field_text node "name" == member.spec.name &&
      (if indirect then category == "lvalue"
       else ["lvalue", "prvalue"].contains category && category == field_text base "valueCategory") do
    throw "ordinary record member type changed"
  return member

private def ordinary_selected (node : Json) : Except String Json := do
  let control :: ty :: associations := child_nodes node | throw "ordinary generic selection lacks a controlling type"
  let controlling := type_spelling ty
  unless field_text ty "kind" == "BuiltinType" && ordinary_decl control controlling &&
      (ordinary_type controlling).isSome do throw "unsupported ordinary generic controlling type"
  let mut cases := []
  let mut defaultCase := none
  for arm in associations do
    match field_text arm "associationKind", child_nodes arm with
    | "case", [candidate, expr] =>
      let name := type_spelling candidate
      unless field_text candidate "kind" == "BuiltinType" && (ordinary_type name).isSome &&
          !(cases.lookup name).isSome do throw "unsupported ordinary generic association"
      cases := (name, (arm, expr)) :: cases
    | "default", [expr] =>
      unless defaultCase.isNone do throw "duplicate ordinary generic default"
      defaultCase := some (arm, expr)
    | _, _ => throw "invalid ordinary generic association"
  let (selected, expr) ← require (cases.lookup controlling <|> defaultCase) "unmatched ordinary generic type"
  unless (associations.filter (fun arm => json_field arm "selected" == .bool true)) == [selected] &&
      ordinary_decl expr (type_spelling node) && field_text expr "valueCategory" == field_text node "valueCategory" do
    throw "ordinary generic result disagrees with its selected association"
  return expr

private def ordinary_lvalue_field (records : List Ordinary.RecordLayout) : Nat → Json → Except String (Option Ordinary.Field)
  | 0, _ => .error "ordinary member nesting exceeds the frontend budget"
  | fuel + 1, node =>
    match field_text node "kind", child_nodes node with
    | "MemberExpr", [base] => some <$> ordinary_member records node base
    | "ParenExpr", [child] => ordinary_lvalue_field records fuel child
    | "GenericSelectionExpr", _ => do ordinary_lvalue_field records fuel (← ordinary_selected node)
    | _, _ => .ok none

private def ordinary_access (records : List Ordinary.RecordLayout) (budget : Nat) (node : Json)
    (scalar : Ordinary.TypeCode) : Except String Ordinary.TypeCode := do
  let member ← ordinary_lvalue_field records budget node
  return (member.map (·.access)).getD scalar

private def ordinary_reference_type (node : Json) (spelling : String) : Bool :=
  ordinary_decl node spelling || ["struct ", "union "].any (fun tag =>
    (spelling.splitOn (tag ++ "@")).length > 1 && ((type_spelling node).splitOn tag).length > 1)

private def ordinary_binding (scope : List OrdinaryLocal) (node : Json) : Except String OrdinaryLocal := do
  let ref := json_field node "referencedDecl"
  let ident := ordinary_ident node
  let binding ← require (scope.find? (fun binding => binding.ident == ident)) "unknown ordinary local reference"
  unless field_text ref "kind" == binding.kind && field_text ref "name" == binding.name &&
      ordinary_reference_type ref binding.spelling && type_spelling node == binding.spelling do
    throw ("ordinary local reference differs for " ++ binding.name ++ ": " ++ type_spelling ref ++ " / " ++ type_spelling node ++ " / " ++ binding.spelling)
  return binding

private def ordinary_address (globals : List OrdinaryObject) (scope : List OrdinaryLocal) (node : Json) :
    Except String Ordinary.Expression := do
  let ident := ordinary_ident node
  if scope.any (fun binding => binding.ident == ident) then
    let binding ← ordinary_binding scope node
    return match binding.storage with
      | .dynamicArray _ => .arrayAddress binding.slot
      | _ => .slotAddress binding.slot
  let object ← require (globals.find? fun object => object.identities.contains ident)
    "unknown ordinary object reference"
  let reference := json_field node "referencedDecl"
  unless field_text reference "kind" == "VarDecl" && field_text reference "name" == object.name &&
      (ordinary_reference_type reference object.spelling || object.callback.any (fun callback => ordinary_decl reference callback.reference)) && ordinary_decl node object.spelling do
    throw "ordinary global reference type or name changed"
  return .globalAddress object.symbol

private def ordinary_va_signature : String → String
  | "__builtin_va_start" => "void (struct __va_list_tag *, ...)"
  | "__builtin_va_copy" => "void (struct __va_list_tag *, struct __va_list_tag *)"
  | "__builtin_va_end" => "void (struct __va_list_tag *)"
  | _ => ""

private def ordinary_va_operand (node : Json) : Bool :=
  ordinary_decl node "struct __va_list_tag *"

private def ordinary_implicit_va (node : Json) : Option Nat := do
  let signature := ordinary_va_signature (field_text node "name")
  let children := child_nodes node
  let parameters := children.filter (fun child => field_text child "kind" == "ParmVarDecl")
  let arity := if field_text node "name" == "__builtin_va_copy" then 2 else 1
  guard (json_field node "isImplicit" == .bool true && ordinary_decl node signature &&
    children.all (fun child => ["ParmVarDecl", "BuiltinAttr", "NoThrowAttr"].contains (field_text child "kind")) &&
    parameters.length == arity && parameters.all ordinary_va_operand)
  return arity

private def pthread_signature : String → Option String
  | "pthread_create" => some "int (pthread_t *restrict, const pthread_attr_t *restrict, void *(*)(void *), void *restrict)"
  | "pthread_join" => some "int (pthread_t, void **)"
  | "pthread_self" => some "pthread_t (void)"
  | "pthread_equal" => some "int (pthread_t, pthread_t)"
  | "pthread_mutex_init" => some "int (pthread_mutex_t *restrict, const pthread_mutexattr_t *restrict)"
  | "pthread_cond_init" => some "int (pthread_cond_t *restrict, const pthread_condattr_t *restrict)"
  | "pthread_cond_wait" => some "int (pthread_cond_t *restrict, pthread_mutex_t *restrict)"
  | "pthread_mutex_lock" | "pthread_mutex_trylock" | "pthread_mutex_unlock" | "pthread_mutex_destroy" =>
    some "int (pthread_mutex_t *)"
  | "pthread_cond_signal" | "pthread_cond_broadcast" | "pthread_cond_destroy" => some "int (pthread_cond_t *)"
  | _ => none

private def written_type (node : Json) := field_text (json_field node "type") "qualType"

private def file_signature : String → Option String
  | "fopen" => some "FILE *(const char *, const char *)"
  | "fread" => some "unsigned long (void *, unsigned long, unsigned long, FILE *)"
  | "fwrite" => some "unsigned long (const void *, unsigned long, unsigned long, FILE *)"
  | "fclose" => some "int (FILE *)"
  | _ => none

private def ordinary_callee (callee : Json) : Except String (String × String × String) := do
  let [reference] := child_nodes callee | throw "expected ordinary function decay"
  let declaration := json_field reference "referencedDecl"
  let name := field_text declaration "name"
  let conversion := field_text callee "castKind"
  let builtin := conversion == "BuiltinFnToFnPtr" && ordinary_decl declaration (ordinary_va_signature name) &&
    ordinary_decl reference "<builtin fn type>"
  let cursorSignature := if ["zhasvalidcap", "zis_readonly"].contains name then " (void *)" else " (struct __va_list_tag *)"
  let headerAlias := ["zcan_va_arg", "zhasvalidcap", "zis_readonly"].contains name && ordinary_decl declaration ("filc_bool" ++ cursorSignature) &&
    (type_spelling reference).startsWith "@type" && (type_spelling reference).endsWith cursorSignature
  let ordinary := conversion == "FunctionToPointerDecay" &&
    (ordinary_reference_type declaration (type_spelling reference) || headerAlias || file_signature name == some (written_type declaration) || pthread_signature name == some (written_type declaration))
  unless field_text callee "kind" == "ImplicitCastExpr" && (ordinary || builtin) &&
      field_text reference "kind" == "DeclRefExpr" && (child_nodes reference).isEmpty &&
      field_text declaration "kind" == "FunctionDecl" && field_text declaration "id" != "" do
    throw "expected a named ordinary function"
  return (name, type_spelling reference, field_text declaration "id")

private def ordinary_scalar : String → Option Ordinary.ScalarOp
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | "/" => some .div
  | "%" => some .rem
  | "&" => some .band
  | "|" => some .bor
  | "^" => some .bxor
  | "<<" => some .shl
  | ">>" => some .shr
  | "==" => some .eq
  | "!=" => some .ne
  | "<" => some .lt
  | "<=" => some .le
  | ">" => some .gt
  | ">=" => some .ge
  | _ => none

private def ordinary_unary : String → Option Ordinary.UnaryOp
  | "+" => some .plus
  | "-" => some .minus
  | "~" => some .complement
  | _ => none

private def ordinary_shift (op : String) : Bool := op == "<<" || op == ">>"

private def ordinary_promoted (ty : Ordinary.TypeCode) : Bool :=
  ty != .pointer && ty.component.isNone && !ty.floating && 4 ≤ ty.width

private def ordinary_right_operand (op spelling : String) (right : Json) : Bool :=
  if ordinary_shift op then (ordinary_type (type_spelling right)).any ordinary_promoted
  else ordinary_decl right spelling

private def ordinary_dimensions : List Char → Nat → List Char → List String → Except String (List String)
  | [], 0, _, dimensions => .ok dimensions.reverse
  | [], _ + 1, _, _ => .error "incomplete ordinary array dimension"
  | char :: rest, depth, reversed, dimensions =>
    if char == '[' then
      ordinary_dimensions rest (depth + 1) (if depth == 0 then [] else char :: reversed) dimensions
    else if char == ']' then
      if depth == 0 then .error "unmatched ordinary array bracket"
      else if depth == 1 then do
        let bound := (String.mk reversed.reverse).trim
        unless !bound.isEmpty do throw "incomplete ordinary array dimension"
        ordinary_dimensions rest 0 [] (bound :: dimensions)
      else ordinary_dimensions rest (depth - 1) (char :: reversed) dimensions
    else if depth != 0 then ordinary_dimensions rest depth (char :: reversed) dimensions
    else if char.isWhitespace then ordinary_dimensions rest 0 [] dimensions
    else .error "unexpected text after an ordinary array dimension"

private def ordinary_shape_parts (spelling : String) : Except String (String × List String) := do
  let typePrefix := spelling.toList.takeWhile (· != '[')
  let base := String.intercalate " " (((String.mk typePrefix).splitOn " ").filter
    (fun word => !word.isEmpty && !["const", "volatile", "restrict", "__restrict", "__restrict__"].contains word))
  let dimensions ← ordinary_dimensions (spelling.toList.drop typePrefix.length) 0 [] []
  return (base, dimensions)

private def ordinary_extent_shape (records : List Ordinary.RecordLayout) (spelling : String) :
    Except String (Nat × Nat × List String) := do
  if (array_pointer_parts spelling).isSome || (array_slot_pointee spelling).isSome || (callback_array_pointee spelling).isSome then return (8, 8, [])
  if let some (_, _, bounds, _) := callback_array spelling then return (8, 8, bounds.map toString)
  let (base, dimensions) ← ordinary_shape_parts spelling
  let storage ← require (ordinary_storage records base) "unsupported ordinary extent element type"
  let alignment := match storage with
    | .scalar ty => ty.alignment
    | .array _ ty _ => ty.alignment
    | .record layout => layout.alignment
    | .dynamicArray _ => 0
    | .vaList => 8
  return (storage.width, alignment, dimensions)

private def ordinary_pointer_stride (records : List Ordinary.RecordLayout) (spelling : String) : Except String Nat := do
  let (width, _, sizes) ← ordinary_extent_shape records (ordinary_pointee spelling)
  let bounds ← require (sizes.mapM String.toNat?) "ordinary pointer stride requires captured variable dimensions"
  let stride := bounds.foldl (· * ·) width
  unless stride > 0 && stride ≤ 9223372036854775807 do throw "ordinary pointer stride exceeds its object representation"
  return stride

private def dimension_suffix (dimensions : List String) : String :=
  String.join (dimensions.map (fun bound => "[" ++ bound ++ "]"))

private def OrdinaryShape.array_type (shape : OrdinaryShape) (rank : Nat) : String :=
  shape.element ++ dimension_suffix (shape.dimensions.drop rank)

private def OrdinaryShape.pointer_type (shape : OrdinaryShape) (rank : Nat) : String :=
  let tail := shape.dimensions.drop rank
  if tail.isEmpty then shape.element ++ " *" else shape.element ++ " (*)" ++ dimension_suffix tail

private def OrdinaryShape.fixed_size (shape : OrdinaryShape) (rank : Nat) : Option Nat :=
  (shape.dimensions.drop rank).mapM String.toNat? |>.map (fun sizes => sizes.foldl (· * ·) shape.width)

private def ordinary_array_alias (scope : List OrdinaryLocal) (type : Json) :
    Option (OrdinaryLocal × OrdinaryShape) := do
  let identity := field_text type "typeAliasDeclId"
  let binding ← scope.find? (fun candidate => candidate.kind == "TypedefDecl" && candidate.ident == identity)
  let .dynamicArray shape := binding.storage | none
  guard (binding.spelling == qualified_spelling type)
  return (binding, shape)

private structure OrdinaryOrigin where
  slot : Nat
  shape : OrdinaryShape
  rank : Nat

private def ordinary_array_origin (scope : List OrdinaryLocal) : Nat → Json → Option OrdinaryOrigin
  | 0, _ => none
  | budget + 1, node =>
    match field_text node "kind", child_nodes node with
    | "DeclRefExpr", [] => do
      let binding ← (ordinary_binding scope node).toOption
      match binding.storage with
      | .dynamicArray shape => some ⟨binding.slot, shape, 1⟩
      | _ => binding.pointerShape.map (fun captured => ⟨binding.slot, captured.shape, 0⟩)
    | "ParenExpr", [child] | "ConstantExpr", [child] | "ImplicitCastExpr", [child] =>
      ordinary_array_origin scope budget child
    | "ArraySubscriptExpr", [base, _] =>
      (ordinary_array_origin scope budget base).map fun origin => { origin with rank := origin.rank + 1 }
    | "UnaryOperator", [base] =>
      if field_text node "opcode" == "*" then
        (ordinary_array_origin scope budget base).map fun origin => { origin with rank := origin.rank + 1 }
      else none
    | "BinaryOperator", [left, right] =>
      if ["+", "-"].contains (field_text node "opcode") then
        ordinary_array_origin scope budget left <|> ordinary_array_origin scope budget right
      else none
    | _, _ => none

private def ordinary_array_pointer (scope : List OrdinaryLocal) (budget : Nat) (node : Json) :
    Option OrdinaryOrigin := do
  let origin ← ordinary_array_origin scope budget node
  guard (origin.rank ≤ origin.shape.dimensions.length && ordinary_decl node (origin.shape.pointer_type origin.rank))
  return origin

private def OrdinaryOrigin.offset (origin : OrdinaryOrigin) (op : Ordinary.PointerOp) (indexing : Bool)
    (left right : Ordinary.Expression) : Ordinary.Expression :=
  match origin.shape.fixed_size origin.rank with
  | some stride => .offset left right stride op
  | none => .arrayOffset op indexing origin.slot origin.rank left right

private def OrdinaryOrigin.update (origin : OrdinaryOrigin) (op : Ordinary.ScalarOp) (returnOld : Bool)
    (address value : Ordinary.Expression) : Ordinary.Expression :=
  match origin.shape.fixed_size origin.rank with
  | some stride => .update op .pointer .pointer returnOld address value stride
  | none => .arrayUpdate op origin.slot origin.rank returnOld address value

private def ordinary_argument (node : Json) (expected : String) : Bool :=
  ordinary_decl node expected || (Option.isSome (do
    let (target, dimensions) ← array_pointer_parts expected
    let (actual, suffix) ← array_pointer_parts (type_spelling node)
    let (_, required) ← (ordinary_shape_parts (target ++ dimensions)).toOption
    let (_, provided) ← (ordinary_shape_parts (actual ++ suffix)).toOption
    guard (field_text node "kind" == "ImplicitCastExpr" && field_text node "castKind" == "BitCast" &&
      actual == target && required.length == provided.length &&
      (provided.zip required).all (fun (supplied, wanted) => supplied == "*" || supplied == wanted))))

private def ordinary_extent_bounds (allBounds : Bool) :
    List String → List Json → Except String (List (Sum Nat Json))
  | [], [] => .ok []
  | [], _ :: _ => .error "unexpected ordinary extent bounds"
  | dimension :: rest, nodes => do
    match dimension.toNat?, allBounds, nodes with
    | some fixed, false, _ => return .inl fixed :: (← ordinary_extent_bounds allBounds rest nodes)
    | some fixed, true, _ :: remaining => return .inl fixed :: (← ordinary_extent_bounds allBounds rest remaining)
    | none, _, node :: remaining => return .inr node :: (← ordinary_extent_bounds allBounds rest remaining)
    | _, _, [] => throw "missing ordinary extent bound"

private def ordinary_comparison (op : String) : Bool :=
  ["==", "!=", "<", "<=", ">", ">="].contains op

private def ordinary_zero : Nat → Json → Bool
  | 0, _ => false
  | depth + 1, node =>
    match field_text node "kind", child_nodes node with
    | "IntegerLiteral", [] => field_text node "value" == "0"
    | "ParenExpr", [child] | "ConstantExpr", [child] => ordinary_zero depth child
    | _, _ => false

private def refers_to_common (common opaqueNode : Json) : Bool :=
  match child_nodes opaqueNode with
  | [child] => field_text opaqueNode "kind" == "OpaqueValueExpr" && field_text common "id" != "" &&
      field_text child "id" == field_text common "id" && type_spelling opaqueNode == type_spelling common
  | _ => false

private def shared_casts (common : Json) : Nat → Json → Except String (String × List Ordinary.TypeCode)
  | 0, _ => .error "incomplete shared operand"
  | fuel + 1, node => do
    if refers_to_common common node then return (field_text node "id", [])
    let [inner] := child_nodes node | throw "shared operand has no conversion input"
    unless field_text node "kind" == "ImplicitCastExpr" do throw "unsupported shared operand"
    let (ident, casts) ← shared_casts common fuel inner
    match field_text node "castKind" with
    | "NoOp" =>
      let source ← require (ordinary_type (type_spelling inner)) "unsupported shared operand type"
      unless ordinary_type (type_spelling node) == some source do
        throw "shared no-op conversion changes representation"
      return (ident, casts)
    | "IntegralCast" =>
      let target ← require (ordinary_type (type_spelling node)) "unsupported shared conversion"
      unless target != .pointer && target.component.isNone && !target.floating &&
          (ordinary_type (type_spelling inner)).any (fun ty => ty != .pointer && ty.component.isNone && !ty.floating) do
        throw "shared conversion requires integer operands"
      return (ident, casts ++ [target])
    | "IntegralToFloating" =>
      let target ← require (ordinary_type (type_spelling node)) "unsupported shared floating result"
      unless target.floating && (ordinary_integer_type (type_spelling inner)).isSome do
        throw "invalid shared integer-to-floating conversion"
      return (ident, casts ++ [target])
    | _ => throw "unsupported shared operand conversion"

private def string_payload (node : Json) : Except String (List UInt8) := do
  let spelling := (field_text node "value").toUTF8.data.toList
  let 34 :: rest := spelling | throw "expected ordinary string literal"
  let 34 :: reversed := rest.reverse | throw "unterminated ordinary string literal"
  let octal (b : UInt8) := 48 ≤ b && b ≤ 55
  let rec decode : List UInt8 → Option (List UInt8)
    | [] => some []
    | 92 :: b :: tail => do
      if octal b then
        let first := b.toNat - 48
        match tail with
        | c :: d :: more =>
          if octal c && octal d then
            let value := first * 64 + (c.toNat - 48) * 8 + (d.toNat - 48)
            guard (value < 256)
            return UInt8.ofNat value :: (← decode more)
          if octal c then return UInt8.ofNat (first * 8 + (c.toNat - 48)) :: (← decode (d :: more))
        | [c] => if octal c then return [UInt8.ofNat (first * 8 + (c.toNat - 48))]
        | [] => pure ()
        return (b - 48) :: (← decode tail)
      let value ← match b.toNat with
        | 110 => some 10 | 116 => some 9 | 114 => some 13 | 97 => some 7
        | 98 => some 8 | 102 => some 12 | 118 => some 11
        | 92 | 34 | 39 | 63 => some b | _ => none
      return value :: (← decode tail)
    | 92 :: [] | 34 :: _ => none
    | b :: tail => (b :: ·) <$> decode tail
  require (decode reversed.reverse) "unsupported ordinary string escape"

private def real_literal_bits (ty : Ordinary.TypeCode) (spelling : String) : Option Nat := do
  if spelling == "Inf" || spelling == "INF" then return Ordinary.floating_bits ty 1 0
  let (mantissa, exponent) ← match (spelling.replace "e" "E").splitOn "E" with
    | [head] => some (head, (0 : Int))
    | [head, power] => do
      let exponent ← (if power.startsWith "+" then power.drop 1 else power).toInt?
      guard (exponent.natAbs ≤ 6000)
      pure (head, exponent)
    | _ => none
  let (whole, fraction) ← match mantissa.splitOn "." with
    | [whole] => some (whole, "")
    | [whole, fraction] => do guard (!fraction.isEmpty); pure (whole, fraction)
    | _ => none
  guard (!whole.isEmpty && whole.toList.all Char.isDigit && fraction.toList.all Char.isDigit)
  let digits ← (whole ++ fraction).toNat?
  let scale := exponent - fraction.length
  return Ordinary.floating_bits ty (digits * 10 ^ scale.toNat) (10 ^ (-scale).toNat)

private def ordinary_stores (records : List Ordinary.RecordLayout) (parse : Json → Except String Ordinary.Expression) :
    Nat → OrdinaryStorage → Json → Except String (List Ordinary.Initialiser)
  | 0, _, _ => .error "ordinary initialiser exceeds the frontend traversal budget"
  | depth + 1, storage, initializer => do
    let nested := fun spelling ty offset node => do
      if field_text node "kind" == "ImplicitValueInitExpr" then return []
      let sub := ordinary_storage records spelling
      if (field_text node "kind" == "InitListExpr" || field_text node "kind" == "StringLiteral") &&
          sub.any (fun | .array .. | .record _ => true | _ => false) then
        let some aggregate := sub | throw "unknown ordinary aggregate initialiser"
        let stores ← ordinary_stores records parse depth aggregate node
        return stores.map (fun init => { init with offsets := offset :: init.offsets })
      return [⟨[offset], ty, ← parse node⟩]
    match storage with
    | .scalar ty =>
      if let some component := ty.component then
        if field_text initializer "kind" == "InitListExpr" then
          let values := child_nodes initializer
          unless values.length ≤ 2 do throw "ordinary complex initialiser exceeds two components"
          let stores ← values.zipIdx.mapM fun (value, index) => do
            unless ordinary_type (type_spelling value) == some component do throw "ordinary complex component has the wrong type"
            if field_text value "kind" == "ImplicitValueInitExpr" then return none
            return some (⟨[index * component.width], component, ← parse value⟩ : Ordinary.Initialiser)
          return stores.filterMap id
      return [⟨[], ty, ← parse initializer⟩]
    | .array element ty count =>
      if field_text initializer "kind" == "StringLiteral" then
        unless ["char", "unsigned char", "signed char"].contains element && (child_nodes initializer).isEmpty &&
            ordinary_array (type_spelling initializer) == some (element, count) do
          throw "invalid ordinary string initialiser destination"
        let bytes ← string_payload initializer
        unless bytes.length ≤ count do throw "ordinary string initialiser exceeds the array"
        return (((bytes ++ [0]).take count).zipIdx.map fun (b, i) => ⟨[i], .byte, .byteLiteral b⟩)
      unless field_text initializer "kind" == "InitListExpr" do
        throw "ordinary array initialiser requires an initialiser list"
      let values := child_nodes initializer
      let values := if values.isEmpty then ((json_field initializer "array_filler").getArr?.toOption.getD #[]).toList.drop 1
        else values
      unless values.length ≤ count do
        throw "ordinary array initialiser extent does not match its elements"
      let stores ← values.zipIdx.mapM fun (node, index) => do
        unless ordinary_decl node element || ordinary_decl node (element.replace "(*const)" "(*)") do throw "ordinary array initialiser element has the wrong type"
        nested element ty (index * ty.width) node
      return stores.flatten
    | .record layout =>
      unless field_text initializer "kind" == "InitListExpr" do
        throw "ordinary record initialiser requires an initialiser list"
      let values := child_nodes initializer
      let fields ← if !layout.isUnion then pure layout.fields else do
        let selected := field_text (json_field initializer "field") "id"
        let member ← require (if selected.isEmpty then layout.fields.head? else
          layout.fields.find? (·.spec.identity == selected)) "unknown ordinary union initialiser member"
        pure [member]
      unless values.length ≤ fields.length do
        throw "ordinary record initialiser does not cover its fields"
      let stores ← (fields.zip values).mapM fun (member, node) => do
        unless ordinary_decl node member.spec.spelling do throw "ordinary record initialiser changed a field type"
        nested member.spec.spelling member.access member.offset node
      return stores.flatten
    | .dynamicArray _ => throw "ordinary variable-length arrays do not have initialiser lists"
    | .vaList => throw "ordinary variadic cursors are initialised by va_start or va_copy"

private def ordinary_expr (records : List Ordinary.RecordLayout) (symbols : List OrdinarySignature) (globals : List OrdinaryObject)
    (scope : List OrdinaryLocal) : Nat → Bool → Json → Except String Ordinary.Expression
  | 0, _, _ => .error "incomplete ordinary expression"
  | depth + 1, place, node => do
    let descend := ordinary_expr records symbols globals scope depth
    let spelling := type_spelling node
    let kind := field_text node "kind"
    let children := child_nodes node
    if kind == "GenericSelectionExpr" then return ← descend place (← ordinary_selected node)
    if place then
      match kind, children with
      | "CompoundLiteralExpr", [init] => do
        let ident := field_text node "id"
        let binding ← require (scope.find? fun candidate => candidate.ident == ident && candidate.kind == "CompoundLiteralExpr")
          "ordinary compound literal lacks an automatic allocation"
        unless !ident.isEmpty && field_text node "valueCategory" == "lvalue" && ordinary_decl init spelling &&
            binding.spelling == spelling do throw "ordinary compound literal changed its object type"
        let stores ← ordinary_stores records (descend false) depth binding.storage init
        unless Ordinary.Initialiser.fits binding.storage.width stores do throw "ordinary compound literal stores exceed their object"
        return .compound binding.slot binding.storage.width (stores.foldr
          (fun init rest => .compoundStore binding.slot init.offsets init.ty init.value rest) (.compoundEnd binding.slot))
      | "DeclRefExpr", [] => ordinary_address globals scope node
      | "ParenExpr", [child] =>
        unless ordinary_decl child spelling do throw "parenthesised ordinary lvalue changed type"
        descend true child
      | "UnaryOperator", [operand] =>
        unless field_text node "opcode" == "*" do throw "unsupported ordinary dereference"
        let pointee := match ordinary_array_pointer scope depth operand with
          | some origin => origin.shape.array_type origin.rank
          | none => ordinary_pointee (type_spelling operand)
        unless ordinary_decl node pointee do throw "ordinary dereference changed the pointee type"
        descend false operand
      | "ArraySubscriptExpr", [base, index] =>
        unless (ordinary_type (type_spelling index)).any ordinary_promoted do
          throw "ordinary array index is not a promoted integer"
        if let some origin := ordinary_array_pointer scope depth base then
          unless ordinary_decl node (origin.shape.array_type origin.rank) do
            throw "ordinary subscript changed the captured array element type"
          return origin.offset .add true (← descend false base) (← descend false index)
        let stride ← ordinary_pointer_stride records (type_spelling base)
        unless ordinary_decl node (ordinary_pointee (type_spelling base)) do
          throw "unsupported ordinary array subscript"
        return .offset (← descend false base) (← descend false index) stride
      | "MemberExpr", [base] =>
        let indirect := json_field node "isArrow" == .bool true
        let member ← ordinary_member records node base
        let address ← if indirect then descend false base
          else if field_text base "valueCategory" == "lvalue" then descend true base
          else do
            let recordType ← require ((records.find? (·.spelling == type_spelling base)).bind ordinary_record_code)
              "unsupported ordinary temporary record"
            pure (.materialise recordType (← descend false base))
        return .field address member.offset
      | _, _ => throw ("unsupported ordinary lvalue: " ++ kind ++ " of type " ++ spelling)
    else
      match kind, children with
      | "ConstantExpr", [child] =>
        unless ordinary_decl child spelling do throw "ordinary constant expression changed type"
        descend false child
      | "FloatingLiteral", [] =>
        let literal := field_text node "value"
        let ty ← require (ordinary_type spelling) "unsupported ordinary floating literal"
        unless ty.floating do throw "ordinary floating literal requires a floating type"
        return .floatingLiteral ty literal (← require (real_literal_bits ty literal) "invalid ordinary floating literal")
      | "IntegerLiteral", [] =>
        let n ← require (field_text node "value").toNat? "invalid ordinary literal"
        let ty ← require (ordinary_type spelling) "unsupported ordinary literal type"
        let limit := modulus (8 * ty.width - if ty.signed then 1 else 0)
        unless ordinary_promoted ty && (n : Int) < limit do throw "ordinary literal exceeds its integer type"
        return .literal n
      | "CharacterLiteral", [] =>
        let n ← (json_field node "value").getNat?
        unless spelling == "int" && n < 2147483648 do throw "ordinary character exceeds int"
        return .literal n
      | "UnaryExprOrTypeTraitExpr", _ =>
        let trait := field_text node "name"
        unless spelling == "unsigned long" && ["sizeof", "alignof", "__alignof"].contains trait do
          throw "unsupported ordinary size or alignment query"
        let typeForm := json_field node "argType" != .null
        let argument ← if typeForm then pure (qualified_spelling (json_field node "argType")) else do
          let [operand] := children | throw "ordinary size query requires one operand"
          pure (type_spelling operand)
        let (width, alignment, dimensions) ← ordinary_extent_shape records argument
        if trait != "sizeof" then return .sizeLiteral alignment
        if let some (binding, _) := ordinary_array_alias scope (json_field node "argType") then
          return .aliasSize binding.slot
        if let some fixed := dimensions.mapM String.toNat? then
          return .sizeLiteral (fixed.foldl (· * ·) width)
        if !typeForm then
          let [operand] := children | throw "ordinary variable-length size requires an operand"
          let origin ← require (ordinary_array_origin scope depth operand) "unresolved ordinary array size"
          let rank := origin.rank - 1
          unless 0 < origin.rank && rank < origin.shape.dimensions.length &&
              ordinary_decl operand (origin.shape.array_type rank) do
            throw "ordinary size changed the captured array type"
          return .arraySize origin.slot rank (← descend true operand)
        let allBounds := children.length == dimensions.length
        let bounds ← ordinary_extent_bounds allBounds dimensions children
        let sizes ← bounds.mapM fun bound =>
          match bound with
          | .inl fixed => pure (.sizeLiteral fixed)
          | .inr value => do
            unless (ordinary_type (type_spelling value)).any (· != .pointer) do
              throw "ordinary extent bound is not an integer"
            descend false value
        return .arrayExtent width (sizes.foldr .dimension .emptyArguments)
      | "DeclRefExpr", [] =>
        if field_text (json_field node "referencedDecl") "kind" == "EnumConstantDecl" then
          return .literal (← require (field_text node "ordinaryEnumValue").toInt? "unresolved ordinary enumerator")
        let ty ← require (ordinary_value_type records spelling) ("unsupported ordinary local type: " ++ spelling)
        return .load ty (← ordinary_address globals scope node)
      | "ArraySubscriptExpr", [_, _] | "MemberExpr", [_] =>
        let ty ← require (ordinary_value_type records spelling) "unsupported ordinary aggregate element type"
        return .load (← ordinary_access records (depth + 1) node ty) (← descend true node)
      | "ParenExpr", [child] =>
        unless ordinary_decl child spelling do throw "parenthesised ordinary expression changed type"
        descend false child
      | "ImplicitCastExpr", [child] | "CStyleCastExpr", [child] =>
        if kind == "ImplicitCastExpr" && field_text node "castKind" == "FunctionToPointerDecay" then
          let (result, args) ← require (function_prototype spelling) "unsupported ordinary function pointer prototype"
          let (name, signature, ident) ← ordinary_callee node
          let target ← require (symbols.find? (·.name == name)) "ordinary function address has no linked definition"
          unless target.declarations.contains ident && signature == target.spelling && !target.variadic &&
              result == target.result && args == target.parameters.map (·.spelling) do
            throw "ordinary function address disagrees with its linked prototype"
          let index ← require (target.functions.idxOf? target.symbol) "ordinary function has no registered address"
          return .functionAddress target.symbol index
        if kind == "ImplicitCastExpr" && field_text node "castKind" == "ArrayToPointerDecay" then
          if field_text child "kind" == "StringLiteral" && spelling == "char *" && (child_nodes child).isEmpty then
            let bytes ← string_payload child
            unless ordinary_array (type_spelling child) == some ("char", bytes.length + 1) do
              throw "ordinary literal extent differs from its byte length"
            return .string bytes
          if ordinary_va_operand node && ordinary_decl child "struct __va_list_tag[1]" then
            return ← descend true child
          if let some origin := ordinary_array_origin scope depth child then
            unless 0 < origin.rank && origin.rank ≤ origin.shape.dimensions.length &&
                ordinary_decl child (origin.shape.array_type (origin.rank - 1)) &&
                spelling == origin.shape.pointer_type origin.rank do
              throw "ordinary array decay changed the captured array shape"
            return ← descend true child
          let ty ← require (ordinary_type spelling) "unsupported ordinary array decay target"
          let (element, _) ← require (ordinary_array (type_spelling child)) "ordinary array decay requires a fixed extent"
          unless ty == .pointer && element == ordinary_pointee spelling do
            throw "ordinary array decay changed the element type"
          descend true child
        else
          let target := if field_text node "castKind" == "NullToPointer" && ordinary_element records spelling == some .pointer
            then some Ordinary.TypeCode.pointer else ordinary_value_type records spelling
          let ty ← require target ("unsupported ordinary cast target: " ++ spelling)
          let inputType ← if field_text node "castKind" == "IntegralCast" && ordinary_decl child "_Bool" then pure .byte
            else if field_text node "castKind" == "LValueToRValue" && ordinary_decl child ("const " ++ spelling) then pure ty
            else require (ordinary_value_type records (type_spelling child)) ("unsupported ordinary cast input: " ++ type_spelling child)
          match field_text node "castKind" with
          | "NullToPointer" =>
            unless ty == .pointer && inputType != .pointer && ordinary_zero depth child do
              throw "ordinary null pointer requires an integer zero constant"
            return .nullPointer
          | "LValueToRValue" =>
            unless kind == "ImplicitCastExpr" && (ordinary_decl child spelling || ordinary_decl child ("const " ++ spelling) ||
                (ty == .pointer && spelling.endsWith "*" && ordinary_decl child (spelling ++ "const")) ||
                (type_spelling child).replace "(*const)" "(*)" == spelling) do
              throw "unsupported ordinary load type"
            return .load (← ordinary_access records depth child ty) (← descend true child)
          | "BitCast" =>
            unless ty == .pointer && inputType == .pointer do throw "ordinary bitcast must preserve a data pointer"
            descend false child
          | "FloatingToIntegral" =>
            unless inputType.floating && (ordinary_integer_type spelling).isSome do throw "invalid ordinary floating-to-integer conversion"
            return .truncateReal ty (← descend false child)
          | "IntegralToFloating" =>
            unless ty.floating && (ordinary_integer_type (type_spelling child)).isSome do
              throw "invalid ordinary integer-to-floating conversion"
            return .cast ty (← descend false child)
          | "IntegralCast" =>
            unless (ordinary_type spelling).isSome && ((ordinary_type (type_spelling child)).isSome || ordinary_decl child "_Bool") &&
                ty != .pointer && inputType != .pointer && ty.component.isNone && inputType.component.isNone && !ty.floating && !inputType.floating do throw "invalid ordinary integer cast operands"
            return .cast ty (← descend false child)
          | "NoOp" =>
            unless ordinary_decl child spelling || (spelling.startsWith "const " && ty == .pointer && ordinary_decl child (spelling.drop 6)) do
              throw "ordinary no-op cast changed type"
            descend false child
          | _ => throw "unsupported ordinary cast"
      | "UnaryOperator", [operand] =>
        let opcode := field_text node "opcode"
        if opcode == "&" then
          unless ordinary_decl operand (ordinary_pointee spelling) ||
              spelling == written_type operand ++ " *" do throw "unsupported ordinary address type"
          let member ← ordinary_lvalue_field records depth operand
          unless !(member.any (·.spec.bits.isSome)) do throw "ordinary bitfields have no address"
          return ← descend true operand
        else if opcode == "!" then
          unless spelling == "int" && ((ordinary_type (type_spelling operand)).isSome || ordinary_decl operand "_Bool") do
            throw "invalid ordinary logical negation"
          return .logicalNot (← descend false operand)
        else if opcode == "++" || opcode == "--" then
          let ty ← require (ordinary_type spelling) "unsupported ordinary update type"
          unless !ty.floating && ty.component.isNone do throw "floating updates require floating arithmetic"
          let returnOld ← (json_field node "isPostfix").getBool?
          unless ordinary_decl operand spelling do throw "invalid ordinary update operand"
          let op := if opcode == "++" then Ordinary.ScalarOp.add else .sub
          let address ← descend true operand
          if let some origin := ordinary_array_pointer scope depth operand then
            return origin.update op returnOld address (.literal 1)
          let access ← ordinary_access records depth operand ty
          let promoted := if ty.width < 4 then Ordinary.TypeCode.integer else ty
          let stride ← if ty == .pointer then ordinary_pointer_stride records spelling else pure 1
          return .update op access promoted returnOld address (.literal 1) stride
        else
          let op ← require (ordinary_unary opcode) "unsupported ordinary unary expression"
          let ty ← require (ordinary_type spelling) "unsupported ordinary unary type"
          unless (ordinary_promoted ty || (opcode == "+" && (ty.floating || ty.component.isSome))) && ordinary_decl operand spelling do throw "invalid ordinary unary operand"
          return .unary op ty (← descend false operand)
      | "CompoundAssignOperator", [lhs, rhs] =>
        let opcode := field_text node "opcode"
        unless opcode.endsWith "=" && !ordinary_comparison opcode do throw "invalid ordinary compound assignment"
        let symbol := opcode.take (opcode.length - 1)
        let op ← require (ordinary_scalar symbol) "unsupported ordinary compound operator"
        let ty ← require (ordinary_type spelling) "unsupported ordinary compound storage type"
        let computes := qualified_spelling (json_field node "computeLHSType")
        let arithmetic ← require (ordinary_type computes) "unsupported ordinary compound computation type"
        unless ordinary_decl lhs spelling && qualified_spelling (json_field node "computeResultType") == computes do
          throw "invalid ordinary compound operands"
        let address ← descend true lhs
        let value ← descend false rhs
        let access ← ordinary_access records depth lhs ty
        if ty == .pointer then
          unless computes == spelling && ["+", "-"].contains symbol &&
              (ordinary_type (type_spelling rhs)).any ordinary_promoted do
            throw "unsupported ordinary compound pointer operands"
          if let some origin := ordinary_array_pointer scope depth lhs then
            return origin.update op false address value
          return .update op access arithmetic false address value (← ordinary_pointer_stride records spelling)
        unless ordinary_promoted arithmetic && ordinary_right_operand symbol computes rhs do
          throw "unsupported ordinary compound integer operands"
        return .update op access arithmetic false address value
      | "BinaryConditionalOperator", [common, test, reused, fallback] =>
        let (tested, tests) ← shared_casts common depth test
        let (converted, casts) ← shared_casts common depth reused
        unless !tested.isEmpty && tested == converted && (ordinary_type (type_spelling test)).isSome &&
            ordinary_decl reused spelling && ordinary_decl fallback spelling do
          throw "conditional operands differ from the shared value"
        return .shared (← descend false common) (← descend false fallback) tests casts
      | "ConditionalOperator", [condition, yes, no] =>
        unless (ordinary_type (type_spelling condition)).isSome &&
            ordinary_decl yes spelling && ordinary_decl no spelling do
          throw "invalid ordinary conditional operands"
        return .conditional (← descend false condition) (← descend false yes) (← descend false no)
      | "BinaryOperator", [lhs, rhs] =>
        let operator := field_text node "opcode"
        match operator with
        | "+" | "-" =>
          let first := ordinary_array_pointer scope depth lhs
          let second := ordinary_array_pointer scope depth rhs
          if let some origin := first then
            if operator == "-" && second.isSome && spelling == "long" && ordinary_decl rhs (type_spelling lhs) then
              return origin.offset .difference false (← descend false lhs) (← descend false rhs)
            if spelling == type_spelling lhs && (ordinary_type (type_spelling rhs)).any ordinary_promoted then
              let op := if operator == "+" then Ordinary.PointerOp.add else .subtract
              return origin.offset op false (← descend false lhs) (← descend false rhs)
          if let some origin := second then
            if operator == "+" && spelling == type_spelling rhs && (ordinary_type (type_spelling lhs)).any ordinary_promoted then
              return origin.offset .reversedAdd false (← descend false lhs) (← descend false rhs)
          if ordinary_type spelling == some .pointer then
            let stride ← ordinary_pointer_stride records spelling
            let mode ← if ordinary_decl lhs spelling && (ordinary_type (type_spelling rhs)).any ordinary_promoted then
                pure (if operator == "+" then Ordinary.PointerOp.add else .subtract)
              else if operator == "+" && ordinary_decl rhs spelling && (ordinary_type (type_spelling lhs)).any ordinary_promoted then
                pure .reversedAdd
              else throw "ordinary pointer arithmetic requires a matching pointer and integer"
            return .offset (← descend false lhs) (← descend false rhs) stride mode
          else if ordinary_type (type_spelling lhs) == some .pointer then
            unless operator == "-" && spelling == "long" && ordinary_decl rhs (type_spelling lhs) do
              throw "ordinary pointer difference requires matching pointer types and a signed long result"
            let stride ← ordinary_pointer_stride records (type_spelling lhs)
            return .offset (← descend false lhs) (← descend false rhs) stride .difference
          else
            let ty ← require (ordinary_type spelling) "unsupported ordinary arithmetic width"
            unless ordinary_promoted ty && ordinary_decl lhs spelling && ordinary_decl rhs spelling do
              throw "unsupported ordinary addition or subtraction types"
            return .scalar (if operator == "+" then .add else .sub) ty (← descend false lhs) (← descend false rhs)
        | "||" | "&&" =>
          unless spelling == "int" && (ordinary_type (type_spelling lhs)).isSome &&
              (ordinary_type (type_spelling rhs)).isSome do throw "invalid ordinary logical operands"
          return .logic (field_text node "opcode" == "&&") (← descend false lhs) (← descend false rhs)
        | "," =>
          unless ordinary_decl rhs spelling do throw "invalid ordinary comma result type"
          return .comma (← descend false lhs) (← descend false rhs)
        | "=" =>
          unless ordinary_decl lhs spelling && ordinary_decl rhs spelling do
            throw "ordinary assignment operand types differ"
          let ty ← require (ordinary_value_type records spelling) "unsupported ordinary assignment type"
          return .assign (← ordinary_access records depth lhs ty) (← descend true lhs) (← descend false rhs)
        | opcode =>
          let op ← require (ordinary_scalar opcode) "unsupported ordinary binary expression"
          let operand := type_spelling lhs
          let ty ← require (if (ordinary_array_pointer scope depth lhs).isSome then some .pointer else ordinary_type operand)
            "unsupported ordinary arithmetic width"
          let result := if ordinary_comparison opcode then "int" else operand
          if ty == .pointer then
            unless ordinary_comparison opcode && ordinary_decl rhs operand && spelling == "int" do
              throw "ordinary pointer comparison requires matching pointer types"
            return .pointerCompare op (← descend false lhs) (← descend false rhs)
          unless ordinary_promoted ty && ordinary_right_operand opcode operand rhs && spelling == result do
            throw "unsupported ordinary scalar operand or result type"
          return .scalar op ty (← descend false lhs) (← descend false rhs)
      | "AtomicExpr", target :: operands => do
        let name := field_text node "name"
        let pointee := ordinary_pointee (type_spelling target)
        let explicit := atomic_underlying pointee
        unless explicit.isSome || name.startsWith "__atomic_" do throw "ordinary atomic operation requires an atomic object"
        let plain := explicit.getD pointee
        let aggregate := atomic_record records plain explicit.isSome
        let ty ← require (ordinary_integer_type plain <|> ((data_pointee plain).map fun _ => .pointer) <|> aggregate)
          "unsupported ordinary atomic object"
        let address ← descend false target
        let parseOrder := fun order => do
          unless ordinary_decl order "int" do throw "invalid ordinary atomic order type"
          descend false order
        let parseValue := fun value => do
          unless ordinary_decl value plain do throw "invalid ordinary atomic operand type"
          descend false value
        let plainPointer := fun arg => do
          unless ordinary_pointee (type_spelling arg) == plain do throw "ordinary atomic transfer changed the object type"
          descend false arg
        match name, operands with
        | "__atomic_load", [order, other] | "__atomic_store", [order, other] =>
          unless spelling == "void" && aggregate.isSome do throw "unsupported ordinary indirect atomic transfer"
          return .atomicTransfer (if name == "__atomic_load" then .load else .store) ty address
            (.dimension (← parseOrder order) (.dimension (← plainPointer other) .emptyArguments))
        | "__atomic_exchange", [order, source, output] =>
          unless spelling == "void" && aggregate.isSome do throw "unsupported ordinary indirect atomic exchange"
          return .atomicTransfer .exchange ty address (.dimension (← parseOrder order)
            (.dimension (← plainPointer source) (.dimension (← plainPointer output) .emptyArguments)))
        | "__atomic_compare_exchange", [successOrder, expected, failureOrder, desired, weak] =>
          let [flag] := child_nodes weak | throw "invalid ordinary atomic weak flag"
          unless spelling == "_Bool" && aggregate.isSome && field_text weak "kind" == "ImplicitCastExpr" &&
            field_text weak "castKind" == "IntegralToBoolean" && ordinary_decl weak "_Bool" &&
            (ordinary_integer_type (type_spelling flag)).isSome do throw "unsupported ordinary atomic compare-exchange"
          return .compareWord ty address (← parseOrder successOrder) (← plainPointer expected)
            (← parseOrder failureOrder) (.weakDesired (← descend false flag) (← plainPointer desired)) true
        | "__c11_atomic_compare_exchange_weak", [successOrder, expected, failureOrder, desired]
        | "__c11_atomic_compare_exchange_strong", [successOrder, expected, failureOrder, desired] =>
          unless spelling == "_Bool" && ordinary_pointee (type_spelling expected) == plain do
            throw "invalid ordinary compare-exchange expectation"
          return .compareWord ty address (← parseOrder successOrder) (← descend false expected)
            (← parseOrder failureOrder) (← parseValue desired)
        | "__c11_atomic_load", [order] =>
          unless spelling == plain do throw "invalid ordinary atomic load result"
          return .atomic .load ty address (← parseOrder order) (.literal 0)
        | "__c11_atomic_init", [value] =>
          unless spelling == "void" do throw "invalid ordinary atomic init result"
          return .atomic .initialise ty address (.literal 0) (← parseValue value)
        | _, [order, value] =>
          let op : Ordinary.AtomicOperation ← match name with
            | "__c11_atomic_store" => pure .store
            | "__c11_atomic_exchange" => pure (.fetch .exchange true)
            | "__c11_atomic_fetch_add" => pure (.fetch .add true)
            | "__c11_atomic_fetch_sub" => pure (.fetch .sub true)
            | "__c11_atomic_fetch_and" => pure (.fetch .bitAnd true)
            | "__c11_atomic_fetch_or" => pure (.fetch .bitOr true)
            | "__c11_atomic_fetch_xor" => pure (.fetch .bitXor true)
            | _ => throw ("unsupported ordinary atomic operation: " ++ name)
          unless spelling == (if name == "__c11_atomic_store" then "void" else plain) do
            throw "invalid ordinary atomic operation result"
          if aggregate.isSome then
            match op with
            | .store | .fetch .exchange true => pure ()
            | _ => throw "invalid ordinary aggregate atomic operation"
          if ty == .pointer then
            if let .fetch operation returnOld := op then
              match operation with
              | .add | .sub =>
                unless (ordinary_integer_type (type_spelling value)).isSome do throw "ordinary atomic pointer step requires an integer"
                let stride ← ordinary_pointer_stride records plain
                return .atomic (.pointerStep operation stride returnOld) ty address (← parseOrder order) (← descend false value)
              | .exchange => pure ()
              | _ => throw "invalid ordinary atomic pointer operation"
          return .atomic op ty address (← parseOrder order) (← parseValue value)
        | _, _ => throw ("unsupported ordinary atomic operation: " ++ name)
      | "VAArgExpr", [place] =>
        unless ordinary_va_operand place do throw "ordinary va_arg requires a cursor"
        let ty ← require (ordinary_value_type records spelling) "unsupported ordinary va_arg type"
        return .vaArg ty (← descend false place)
      | "CallExpr", callee :: arguments =>
        let direct := ordinary_callee callee
        if direct.toOption.isNone then
          if let [reference] := child_nodes callee then
            if let some object := globals.find? (fun object => object.identities.contains (ordinary_ident reference)) then
              if let some callback := object.callback then
                unless field_text callee "kind" == "ImplicitCastExpr" && field_text callee "castKind" == "LValueToRValue" &&
                    field_text reference "kind" == "DeclRefExpr" && (child_nodes reference).isEmpty &&
                    type_spelling callee == object.spelling.replace "(*const)" "(*)" &&
                    spelling == callback.result && arguments.isEmpty do throw "ordinary stored callback has an incompatible call"
                let registry ← require symbols.head? "ordinary indirect call has no linked functions"
                let address ← ordinary_address globals scope reference
                return .indirect registry.functions (some .pointer) (.load .pointer address) .emptyArguments
          let (result, args) ← require (function_prototype (type_spelling callee)) "unsupported ordinary indirect callee"
          unless result == spelling && args.length == arguments.length do throw "ordinary indirect call signature changed"
          let registry ← require symbols.head? "ordinary indirect call has no linked functions"
          let target ← descend false callee
          let values ← (args.zip arguments).mapM fun (expected, argument) => do
            unless ordinary_argument argument expected do throw "ordinary indirect argument type changed"
            let ty ← require (ordinary_type expected) "unsupported ordinary indirect argument type"
            return (ty, ← descend false argument)
          return .indirect registry.functions (ordinary_type result) target
            (values.foldr (fun (ty, expr) tail => .argument ty expr tail) .emptyArguments)
        let (name, signature, ident) ← direct
        if let some expected := file_signature name then
          let [reference] := child_nodes callee | throw "ordinary file call requires a declaration"
          unless written_type (json_field reference "referencedDecl") == expected do throw "ordinary file declaration differs from stdio"
        if let some expected := pthread_signature name then
          let [reference] := child_nodes callee | throw "ordinary pthread call requires a declaration"
          unless written_type (json_field reference "referencedDecl") == expected do
            throw "ordinary pthread declaration has an incompatible signature"
        if let some op := SyncOp.all.find? (·.name == name) then
          unless spelling == "int" && arguments.length == (if op.binary then 2 else 1) do
            throw "invalid ordinary pthread synchronisation prototype"
          let checked ← arguments.mapM fun arg => do
            unless ordinary_type (type_spelling arg) == some .pointer do throw "expected a pthread object pointer"
            descend false arg
          return .library (.synchronise op) (checked.foldr (.argument .pointer) .emptyArguments)
        match name, signature, spelling, arguments with
        | "pthread_create", _, "int", [dst, attributes, worker, arg] =>
          let expected := "int (" ++ written_type dst ++ "restrict, " ++ written_type attributes ++
            "restrict, void *(*)(void *), void *restrict)"
          let [attr] := child_nodes attributes | throw "ordinary thread attributes require null"
          unless signature == expected && (written_type dst).endsWith " *" &&
              field_text attributes "castKind" == "NullToPointer" && ordinary_zero depth attr &&
              ordinary_decl arg "void *" && ordinary_decl worker "void *(*)(void *)" do
            throw "ordinary pthread_create signature or attributes changed"
          let (callback, spelling, identity) ← ordinary_callee worker
          let target ← require (symbols.find? (·.name == callback)) "ordinary worker has no linked definition"
          unless spelling == "void *(void *)" && target.spelling == spelling && target.declarations.contains identity do
            throw "ordinary worker has an incompatible entry point"
          return .spawn target.symbol (← descend false dst) (← descend false arg)
        | "pthread_join", _, "int", [handle, dst] =>
          unless signature == "int (" ++ written_type handle ++ ", void **)" &&
              ordinary_type (type_spelling handle) == some .pointer && ordinary_decl dst "void **" do
            throw "ordinary pthread_join signature changed"
          return .join (← descend false handle) (← descend false dst)
        | "pthread_self", _, _, [] =>
          unless signature == written_type node ++ " (void)" && ordinary_type spelling == some .pointer do
            throw "ordinary pthread_self signature changed"
          return .self
        | "pthread_equal", _, "int", [left, right] =>
          unless signature == "int (" ++ written_type left ++ ", " ++ written_type right ++ ")" &&
              ordinary_type (type_spelling left) == some .pointer && ordinary_type (type_spelling right) == some .pointer do
            throw "ordinary pthread_equal signature changed"
          return .equal (← descend false left) (← descend false right)
        | "fopen", _, _, [path, mode] =>
          unless signature == spelling ++ "(const char *, const char *)" && (data_pointee spelling).isSome &&
              ordinary_decl path "const char *" && ordinary_decl mode "const char *" do throw "invalid ordinary fopen signature"
          return .library .fopen (.argument .pointer (← descend false path) (.argument .pointer (← descend false mode) .emptyArguments))
        | "fclose", _, "int", [handle] =>
          unless signature == "int (" ++ written_type handle ++ ")" && ordinary_type (type_spelling handle) == some .pointer do
            throw "invalid ordinary fclose signature"
          return .library .fclose (.argument .pointer (← descend false handle) .emptyArguments)
        | "fread", _, "unsigned long", [buffer, size, count, handle]
        | "fwrite", _, "unsigned long", [buffer, size, count, handle] =>
          let input := name == "fread"
          let element := if input then "void *" else "const void *"
          unless signature == "unsigned long (" ++ element ++ ", unsigned long, unsigned long, " ++ written_type handle ++ ")" &&
              ordinary_decl buffer element && ordinary_decl size "unsigned long" && ordinary_decl count "unsigned long" &&
              ordinary_type (type_spelling handle) == some .pointer do throw "invalid ordinary file transfer signature"
          return .library (if input then .fread else .fwrite) (.argument .pointer (← descend false buffer)
            (.argument .size (← descend false size) (.argument .size (← descend false count)
            (.argument .pointer (← descend false handle) .emptyArguments))))
        | "strlen", "unsigned long (const char *)", "unsigned long", [input] =>
          unless ordinary_decl input "const char *" do throw "invalid ordinary strlen argument"
          return .library .strlen (.argument .pointer (← descend false input) .emptyArguments)
        | "strcmp", "int (const char *, const char *)", "int", [lhs, rhs] =>
          unless ordinary_decl lhs "const char *" && ordinary_decl rhs "const char *" do
            throw "invalid ordinary strcmp arguments"
          return .library .strcmp (.argument .pointer (← descend false lhs) (.argument .pointer (← descend false rhs) .emptyArguments))
        | "calloc", "void *(unsigned long, unsigned long)", "void *", [count, width] =>
          unless ordinary_decl count "unsigned long" && ordinary_decl width "unsigned long" do throw "invalid ordinary calloc size"
          return .library .calloc (.argument .size (← descend false count) (.argument .size (← descend false width) .emptyArguments))
        | "memset", "void *(void *, int, unsigned long)", "void *", [dst, fill, count] =>
          unless ordinary_decl dst "void *" && ordinary_decl fill "int" && ordinary_decl count "unsigned long" do
            throw "invalid ordinary memset arguments"
          return .library .memset (.argument .pointer (← descend false dst) (.argument .integer (← descend false fill)
            (.argument .size (← descend false count) .emptyArguments)))
        | "printf", "int (const char *, ...)", "int", pattern :: inputs =>
          unless ordinary_decl pattern "const char *" do throw "invalid ordinary printf format type"
          let format ← descend false pattern
          let .string bytes := format | throw "ordinary printf requires a literal format"
          let items ← require (Ordinary.format_items bytes) "unsupported ordinary printf conversion"
          let consumed := items.filterMap fun item => match item with
            | .byte _ => none | .conversion op .. => some op
          unless consumed.length ≤ inputs.length do throw "ordinary printf is missing an argument"
          let values ← inputs.mapM fun input => do
            let ty ← require (ordinary_type (type_spelling input)) "unsupported ordinary printf argument type"
            return (ty, ← descend false input)
          unless (consumed.zip values).all (fun (op, arg) => match op with
              | .string => arg.1 == .pointer
              | .fixed .. => arg.1 == .binary64
              | _ => arg.1 != .pointer && arg.1.component.isNone && !arg.1.floating) do
            throw "ordinary printf conversion disagrees with its argument"
          let arguments := values.foldr (fun (ty, expr) tail => .argument ty expr tail) Ordinary.Expression.emptyArguments
          return .library .printf (.argument .pointer format arguments)
        | "puts", "int (const char *)", "int", [input] =>
          unless ordinary_decl input "const char *" do throw "invalid ordinary puts argument"
          return .library .puts (.argument .pointer (← descend false input) .emptyArguments)
        | "zhasvalidcap", _, "_Bool", [input] | "zis_readonly", _, "_Bool", [input] =>
          let [reference] := child_nodes callee | throw "ordinary capability query requires a declaration"
          unless written_type (json_field reference "referencedDecl") == "filc_bool (void *)" &&
              ordinary_decl input "void *" do throw "invalid ordinary capability query"
          return .library (if name == "zis_readonly" then .isReadonly else .hasCapability)
            (.argument .pointer (← descend false input) .emptyArguments)
        | "zgetlower", "void *(void *)", "void *", [input] | "zgetupper", "void *(void *)", "void *", [input] =>
          unless ordinary_decl input "void *" do throw "invalid ordinary capability bound query"
          return .library (if name == "zgetupper" then .upperBound else .lowerBound)
            (.argument .pointer (← descend false input) .emptyArguments)
        | "malloc", "void *(unsigned long)", "void *", [size] =>
          unless ordinary_decl size "unsigned long" do throw "invalid ordinary allocation size"
          return .allocate (← descend false size)
        | "memcpy", "void *(void *, const void *, unsigned long)", "void *", [dst, src, size]
        | "memmove", "void *(void *, const void *, unsigned long)", "void *", [dst, src, size] =>
          unless ordinary_decl dst "void *" && ordinary_decl src "const void *" &&
              ordinary_decl size "unsigned long" do throw "invalid ordinary copy arguments"
          return .move (if name == "memcpy" then .memcpy else .memmove) (← descend false dst) (← descend false src) (← descend false size)
        | "putchar", "int (int)", "int", [value] =>
          unless ordinary_decl value "int" do throw "invalid ordinary output argument"
          return .put (← descend false value)
        | "free", "void (void *)", "void", [addr] =>
          unless ordinary_decl addr "void *" do throw "invalid ordinary release argument"
          return .release (← descend false addr)
        | "exit", "void (int) __attribute__((noreturn))", "void", [status] =>
          unless ordinary_decl status "int" do throw "invalid ordinary exit argument"
          return .exit (← descend false status)
        | "__builtin_va_start", "<builtin fn type>", "void", [place, anchor] =>
          let last ← require (scope.filter (·.kind == "ParmVarDecl")).getLast? "ordinary va_start has no named parameter"
          unless ordinary_va_operand place && field_text anchor "kind" == "DeclRefExpr" &&
              ordinary_ident anchor == last.ident do throw "ordinary va_start must use the last named parameter"
          return .vaStart (← descend false place)
        | "__builtin_va_copy", "<builtin fn type>", "void", [dst, src] =>
          unless ordinary_va_operand dst && ordinary_va_operand src do throw "ordinary va_copy requires two cursors"
          return .vaCopy (← descend false dst) (← descend false src)
        | "__builtin_va_end", "<builtin fn type>", "void", [place] =>
          unless ordinary_va_operand place do throw "ordinary va_end requires a cursor"
          return .vaEnd (← descend false place)
        | "zcan_va_arg", _, "_Bool", [place] =>
          unless ordinary_va_operand place do throw "ordinary availability check requires a cursor"
          return .vaAvailable (← descend false place)
        | "zargs", "void *(void)", "void *", [] => return .argumentArea
        | _, _, _, _ =>
          let target ← require (symbols.find? fun target => target.name == name) ("unresolved ordinary direct call: " ++ name)
          unless target.declarations.contains ident && signature == target.spelling && spelling == target.result &&
              (if target.variadic then target.parameters.length ≤ arguments.length
               else arguments.length == target.parameters.length) do throw "ordinary call signature or arity changed"
          let parsed ← (target.parameters.zip arguments).mapM fun (parameter, argument) => do
            unless ordinary_argument argument parameter.spelling do throw "ordinary call argument type changed"
            let ty ← require parameter.storage.value_type "unsupported ordinary parameter value type"
            return (ty, ← descend false argument)
          let extra ← (arguments.drop target.parameters.length).mapM fun argument => do
            let ty ← require (ordinary_value_type records (type_spelling argument)) "unsupported ordinary variadic argument type"
            return (ty, ← descend false argument)
          return .call target.symbol target.ty ((parsed ++ extra).foldr
            (fun (ty, expr) tail => .argument ty expr tail) .emptyArguments)
      | _, _ => throw ("unsupported ordinary expression: " ++ kind)

private def ordinary_read_only : Ordinary.Expression → Bool
  | .floatingLiteral .. | .literal _ | .sizeLiteral _ | .nullPointer | .slotAddress _ | .arrayAddress _ | .globalAddress _
  | .emptyArguments | .aliasSize _ | .argumentArea | .functionAddress .. => true
  | .library .hasCapability args | .library .isReadonly args | .library .upperBound args | .library .lowerBound args
  | .library .strlen args | .library .strcmp args => ordinary_read_only args
  | .load _ operand | .cast _ operand | .truncateReal _ operand | .field operand _ | .logicalNot operand | .unary _ _ operand
  | .arrayExtent _ operand | .arraySize _ _ operand | .vaAvailable operand =>
    ordinary_read_only operand
  | .offset left right _ _ | .logic _ left right | .pointerCompare _ left right | .scalar _ _ left right
  | .argument _ left right | .comma left right | .dimension left right | .arrayOffset _ _ _ _ left right =>
    ordinary_read_only left && ordinary_read_only right
  | .shared common fallback _ _ => ordinary_read_only common && ordinary_read_only fallback
  | .conditional condition yes no => ordinary_read_only condition && ordinary_read_only yes && ordinary_read_only no
  | _ => false

private def ordinary_print_value : Ordinary.Expression → Bool
  | .string _ | .library .isReadonly (.argument .pointer (.string _) .emptyArguments) => true
  | .cast _ value => ordinary_print_value value
  | .conditional test yes no => ordinary_read_only test && ordinary_print_value yes && ordinary_print_value no
  | expr => ordinary_read_only expr

private def ordinary_print_arguments : Ordinary.Expression → Bool
  | .argument _ value rest => ordinary_print_value value && ordinary_print_arguments rest
  | .emptyArguments => true
  | _ => false

private def ordinary_root_effect : Ordinary.Expression → Bool
  | .compound _ _ writes => ordinary_root_effect writes
  | .compoundStore _ _ _ value rest => ordinary_root_effect value && ordinary_root_effect rest
  | .compoundEnd _ => true
  | .self | .string _ => true
  | .library (.synchronise _) args => ordinary_read_only args
  | .atomicTransfer _ _ target args => ordinary_read_only target && ordinary_read_only args
  | .weakDesired weak desired => ordinary_read_only weak && ordinary_read_only desired
  | .compareWord _ target successOrder expected failureOrder desired _ =>
    ordinary_read_only target && ordinary_read_only successOrder && ordinary_read_only expected &&
    ordinary_read_only failureOrder && ordinary_root_effect desired
  | .atomic _ _ target order value => ordinary_read_only target && ordinary_read_only order && ordinary_root_effect value
  | .indirect _ _ callee args => ordinary_read_only callee && ordinary_read_only args
  | .library .printf (.argument .pointer (.string _) rest) => ordinary_root_effect rest
  | .library .strcmp args | .library .strlen args | .library .isReadonly args => ordinary_print_arguments args
  | .argument _ value rest => ordinary_root_effect value && ordinary_root_effect rest
  | .library .puts (.argument .pointer (.string _) .emptyArguments) => true
  | .library .fopen args | .library .fread args | .library .fwrite args | .library .fclose args => ordinary_root_effect args
  | .library _ args => ordinary_read_only args
  | .scalar _ _ left right | .pointerCompare _ left right => ordinary_root_effect left && ordinary_root_effect right
  | .spawn _ left right | .join left right | .equal left right => ordinary_read_only left && ordinary_read_only right
  | .call _ _ args => ordinary_root_effect args
  | .allocate size | .put size | .release size | .exit size => ordinary_read_only size
  | .assign _ place value | .offset place value _ _ => ordinary_root_effect place && ordinary_root_effect value
  | .update _ _ _ _ place value _ => ordinary_root_effect place && ordinary_root_effect value
  | .arrayUpdate _ _ _ _ place value => ordinary_read_only place && ordinary_read_only value
  | .vaStart place | .vaArg _ place | .vaEnd place => ordinary_read_only place
  | .vaCopy destination source => ordinary_read_only destination && ordinary_read_only source
  | .shared common fallback _ _ => ordinary_root_effect common && ordinary_root_effect fallback
  | .conditional condition yes no =>
    ordinary_root_effect condition && ordinary_root_effect yes && ordinary_root_effect no
  | .comma left right | .logic _ left right | .dimension left right =>
    ordinary_root_effect left && ordinary_root_effect right
  | .arrayExtent _ bounds => ordinary_root_effect bounds
  | .arraySize _ _ place | .cast _ place | .truncateReal _ place | .load _ place | .field place _
  | .materialise _ place | .unary _ _ place | .logicalNot place => ordinary_root_effect place
  | .move _ dst src count => ordinary_read_only dst && ordinary_read_only src && ordinary_read_only count
  | expression => ordinary_read_only expression

private def ordinary_return (arithmetic : Option ClosedProgram) (records : List Ordinary.RecordLayout) (symbols : List OrdinarySignature)
    (globals : List OrdinaryObject) (result : String)
    (scope : List OrdinaryLocal) (budget : Nat) (node : Json) : Except String Ordinary.Expression := do
  let [value] := child_nodes node | throw "missing ordinary return expression"
  unless field_text node "kind" == "ReturnStmt" && ordinary_decl value result do
    throw "ordinary return differs from the function result type"
  let expression ← ordinary_expr records symbols globals scope budget false value
  unless arithmetic.isSome || ordinary_root_effect expression do throw "nested ordinary return effects require a sequencing proof"
  return expression

private def ordinary_case_bound : Nat → Json → Except String Int
  | 0, _ => .error "ordinary case bound exceeds the frontend budget"
  | budget + 1, node => do
    unless ordinary_decl node "int" do throw "ordinary case bound must be int"
    match field_text node "kind", child_nodes node with
    | "IntegerLiteral", [] =>
      let value ← require (field_text node "value").toNat? "invalid ordinary case bound"
      unless value < 2147483648 do throw "ordinary case bound exceeds int"
      return value
    | "ConstantExpr", [child] | "ParenExpr", [child] => ordinary_case_bound budget child
    | "UnaryOperator", [operand] =>
      let value ← ordinary_case_bound budget operand
      match field_text node "opcode" with
      | "+" => return value
      | "-" =>
        unless value != -2147483648 do throw "ordinary case negation exceeds int"
        return -value
      | _ => throw "unsupported ordinary case operator"
    | _, _ => throw "ordinary case bound must be an integer constant"

private def ordinary_label_choice (registry : List String) (guard : Json → Except String Ordinary.Expression) :
    Nat → Json → Except String Ordinary.LabelChoice
  | 0, _ => .error "ordinary label choice exceeds the frontend budget"
  | depth + 1, node => do
    unless ["void *", "const void *"].contains (type_spelling node) do
      throw "ordinary computed goto requires a label pointer"
    match field_text node "kind", child_nodes node with
    | "AddrLabelExpr", [] =>
      let identity := field_text node "labelDeclId"
      unless !identity.isEmpty do throw "ordinary label address has no identity"
      return .address identity
    | "ParenExpr", [child] => ordinary_label_choice registry guard depth child
    | "ImplicitCastExpr", [child] =>
      if field_text node "castKind" == "LValueToRValue" then return .loaded (← guard node) registry []
      unless field_text node "castKind" == "NoOp" do throw "ordinary label pointer conversion changed representation"
      ordinary_label_choice registry guard depth child
    | "ConditionalOperator", [test, yes, no] =>
      return .conditional (← guard test) (← ordinary_label_choice registry guard depth yes) (← ordinary_label_choice registry guard depth no)
    | _, _ => throw "ordinary computed goto requires explicit label choices"

private def ordinary_probe (node : Json) : Option (Nat × Json) := do
  guard (field_text node "kind" == "DeclStmt")
  let [probe] := child_nodes node | none
  let name := field_text probe "name"
  let stem := "__heresy_vla_"
  guard (field_text probe "kind" == "TypedefDecl" && name.startsWith stem)
  let offset :: order :: suffix := (name.drop stem.length).splitOn "_" | none
  let index ← order.toNat?
  guard (offset.toNat?.isSome && suffix.all (· == ""))
  return (index, probe)

private def local_array_order : Nat := 4611686018427387903

private def ordinary_captured_bounds (element : String) : Nat → List String → Json →
    Except String (List (Sum Nat Json))
  | 0, _, _ => .error "ordinary array probe exceeds the frontend budget"
  | depth + 1, dimensions, node => do
    unless ordinary_decl node (element ++ dimension_suffix dimensions) do
      throw "ordinary array probe changed its element or dimensions"
    match dimensions, field_text node "kind", child_nodes node with
    | [], _, _ => return []
    | _ :: _, "ParenType", [inner] => ordinary_captured_bounds element depth dimensions inner
    | _ :: tail, "VariableArrayType", [inner, bound] =>
      return .inr bound :: (← ordinary_captured_bounds element depth tail inner)
    | expected :: tail, "ConstantArrayType", [inner] =>
      let size ← (json_field node "size").getNat?
      unless expected.toNat? == some size do throw "ordinary array probe changed a fixed dimension"
      return .inl size :: (← ordinary_captured_bounds element depth tail inner)
    | _, _, _ => throw "unsupported ordinary array probe"

private def ordinary_bound_list (bounds : List (Sum Nat Json))
    (parse : Json → Except String Ordinary.Expression) : Except String Ordinary.Expression := do
  let expressions ← bounds.mapM fun bound => match bound with
    | .inl fixed => pure (.literal (Int.ofNat fixed))
    | .inr node => do
      unless (ordinary_type (type_spelling node)).any (· != .pointer) do
        throw "ordinary captured bound is not an integer"
      parse node
  return expressions.foldr .dimension .emptyArguments

private def ordinary_type_tree : Nat → Json → Except String Json
  | 0, _ => .error "ordinary type wrapper exceeds the frontend budget"
  | depth + 1, node =>
    match field_text node "kind", child_nodes node with
    | "TypeOfType", [child] | "ParenType", [child] => ordinary_type_tree depth child
    | _, _ => .ok node

private def ordinary_pointer_probe (budget : Nat) (spelling : String) (probe : Json) :
    Except String OrdinaryPointerShape := do
  let [wrapper] := child_nodes probe | throw "ordinary pointer probe lacks a typed declaration"
  unless field_text wrapper "kind" == "TypeOfType" do
    throw "invalid or repeated ordinary pointer probe"
  let raw ← ordinary_type_tree budget wrapper
  let (array, skip) ← if field_text raw "kind" == "PointerType" then do
      let [pointee] := child_nodes raw | throw "ordinary pointer probe lacks a pointee"
      pure ((← ordinary_type_tree budget pointee), 0)
    else pure (raw, 1)
  let (element, dimensions) ← ordinary_shape_parts (type_spelling array)
  let ty ← require (ordinary_type element) "unsupported ordinary parameter array element"
  let shape : OrdinaryShape := ⟨element, ty.width, dimensions.drop skip⟩
  unless !dimensions.isEmpty && ordinary_type spelling == some .pointer &&
      shape.pointer_type 0 == spelling do
    throw "ordinary pointer probe changed its adjusted pointer type"
  let bounds ← ordinary_captured_bounds element budget dimensions array
  let identity := field_text probe "id"
  unless !identity.isEmpty do throw "ordinary pointer probe lacks an identity"
  let captured := if skip == 0 || dimensions.any (fun bound => bound.toNat?.isNone) then some bounds else none
  return ⟨identity, shape, skip, captured⟩

private def ordinary_array_local (probe statement : Json) (budget slot : Nat) (scope : List OrdinaryLocal)
    (parse : Json → Except String Ordinary.Expression) : Except String (OrdinaryLocal × Ordinary.Statement) := do
  let [declaration] := child_nodes statement | throw "ordinary array probe must precede a single declaration"
  let ident := field_text declaration "id"
  let name := field_text declaration "name"
  let spelling := type_spelling declaration
  unless field_text statement "kind" == "DeclStmt" && field_text declaration "kind" == "VarDecl" &&
      field_text declaration "storageClass" == "" &&
      ordinary_name name && !ident.isEmpty && !(scope.any (·.ident == ident)) do
    throw "ordinary array probe has no matching automatic declaration"
  if (array_pointer_parts spelling).isSome then
    let captured ← ordinary_pointer_probe budget spelling probe
    let bounds ← require captured.bounds "ordinary array pointer lacks a captured bound"
    unless captured.skip == 0 do throw "ordinary local pointer probe adjusted an array parameter"
    let initializer ← match child_nodes declaration with
      | [] => pure none
      | [value] => do
        unless ordinary_decl value spelling do throw "ordinary array pointer initialiser changed its type"
        some <$> parse value
      | _ => throw "ordinary array pointer has multiple initialisers"
    let expressions ← ordinary_bound_list bounds parse
    return (⟨ident, name, spelling, .scalar .pointer, "VarDecl", slot, some captured⟩,
      .initialiseArrayPointer slot captured.shape.width expressions initializer)
  unless (child_nodes declaration).isEmpty do throw "ordinary automatic array has an initialiser"
  let (element, dimensions) ← ordinary_shape_parts spelling
  let ty ← require (ordinary_type element) "unsupported ordinary array element"
  unless dimensions.any (fun bound => bound.toNat?.isNone) && spelling == element ++ dimension_suffix dimensions do
    throw "ordinary captured array requires a variable dimension"
  let [wrapper] := child_nodes probe | throw "ordinary array probe lacks a typed declaration"
  let [declared] := child_nodes wrapper | throw "ordinary array probe lacks an array type"
  unless field_text wrapper "kind" == "TypeOfType" do throw "invalid ordinary array probe wrapper"
  let bounds ← ordinary_captured_bounds element budget dimensions declared
  let shape : OrdinaryShape := ⟨element, ty.width, dimensions⟩
  return (⟨ident, name, spelling, .dynamicArray shape, "VarDecl", slot, none⟩,
    .declareArray slot ty.width (← ordinary_bound_list bounds parse))

private def effect_diagnostic (message : String) (node : Json) : String :=
  let start := json_field (json_field node "range") "begin"
  let offset := (json_field start "offset").getNat?.toOption
  message ++ " in " ++ field_text node "kind" ++ (offset.map fun n => " at byte " ++ toString n).getD ""

private def ordinary_literals (records : List Ordinary.RecordLayout) (budget slot : Nat) (node : Json) :
    Except String (List OrdinaryLocal) := do
  let nodes ← startup_nodes budget node
  (nodes.filter (fun node => field_text node "kind" == "CompoundLiteralExpr")).zipIdx.mapM fun (node, index) => do
    let id := field_text node "id"
    let name := type_spelling node
    let shape ← require (ordinary_storage records name) ("unsupported ordinary compound literal type: " ++ name)
    unless !id.isEmpty && shape.frame_width.isSome && shape.width ≤ 9223372036854775792 do
      throw "invalid ordinary compound literal storage"
    return (⟨id, "", name, shape, "CompoundLiteralExpr", slot + index, none⟩ : OrdinaryLocal)

private inductive AssemblyToken where
  | atom (name : String)
  | literal (value : String)
  deriving BEq

private def assembly_tokens (source : String) : Option (List AssemblyToken) := do
  let rec quoted : List Char → List Char → Option (String × List Char)
    | [], _ => none
    | '"' :: rest, acc => some (String.mk ('"' :: acc).reverse, rest)
    | '\\' :: c :: rest, acc => quoted rest (c :: '\\' :: acc)
    | c :: rest, acc => quoted rest (c :: acc)
  let word := fun c : Char => c.isAlphanum || c == '_'
  let rec scan : Nat → List Char → Option (List AssemblyToken)
    | _, [] => some []
    | 0, _ => none
    | fuel + 1, '"' :: rest => do
      let (raw, tail) ← quoted rest ['"']
      let bytes ← (string_payload (Json.mkObj [("value", .str raw)])).toOption
      let spelling ← String.fromUTF8? ⟨bytes.toArray⟩
      return .literal spelling :: (← scan fuel tail)
    | fuel + 1, c :: rest => do
      if c.isWhitespace then return ← scan fuel rest
      if word c then
        let name := rest.takeWhile word
        return .atom (String.mk (c :: name)) :: (← scan fuel (rest.drop name.length))
      guard (!['/', '\'', '\\'].contains c)
      return .atom (String.singleton c) :: (← scan fuel rest)
  scan (source.length + 1) source.toList

private abbrev AssemblyOperand := Option String × String

private def assembly_section (tokens : List AssemblyToken) : Option (List AssemblyOperand × List AssemblyToken) := do
  let rec balance : Nat → List AssemblyToken → Option (List AssemblyToken)
    | _, [] => none
    | 0, .atom ")" :: rest => some rest
    | depth + 1, .atom ")" :: rest => balance depth rest
    | depth, .atom "(" :: rest => balance (depth + 1) rest
    | depth, _ :: rest => balance depth rest
  let rec entries : Nat → List AssemblyToken → Option (List AssemblyOperand × List AssemblyToken)
    | 0, _ => none
    | fuel + 1, tokens => do
      let (name, tokens) := match tokens with
        | .atom "[" :: .atom name :: .atom "]" :: rest => (some name, rest)
        | other => (none, other)
      let .literal constraint :: .atom "(" :: rest := tokens | none
      let tail ← balance 0 rest
      if let .atom "," :: more := tail then
        let (others, tail) ← entries fuel more
        return ((name, constraint) :: others, tail)
      return ([(name, constraint)], tail)
  match tokens with
  | .atom ":" :: rest =>
    if rest.head? == some (.atom ":") || rest.head? == some (.atom ")") then return ([], rest)
    entries (rest.length + 1) rest
  | _ => return ([], tokens)

private def assembly_syntax (raw : String) : Option (List String × List AssemblyOperand × List AssemblyOperand) := do
  let .atom keyword :: prefixTokens ← assembly_tokens raw | none
  guard (["asm", "__asm", "__asm__"].contains keyword)
  let .atom "(" :: body := prefixTokens.dropWhile (fun t => match t with
    | .atom q => ["volatile", "__volatile", "__volatile__", "inline", "__inline", "__inline__"].contains q
    | _ => false) | none
  let quoted := body.takeWhile (fun t => match t with | .literal _ => true | _ => false)
  guard (!quoted.isEmpty)
  let template := String.join (quoted.filterMap (fun t => match t with | .literal s => some s | _ => none))
  let (outputs, rest) ← assembly_section (body.drop quoted.length)
  let (inputs, rest) ← assembly_section rest
  let rec clobbers : List AssemblyToken → Bool
    | [.atom ")"] => true
    | [.literal c, .atom ")"] => ["memory", "cc"].contains c
    | .literal c :: .atom "," :: more => ["memory", "cc"].contains c && clobbers more
    | _ => false
  guard (rest == [.atom ")"] || (rest.head? == some (.atom ":") && clobbers rest.tail!))
  let instructions := ((template.replace "\r" "\n").replace ";" "\n").splitOn "\n"
  return (instructions.map String.trim, outputs, inputs)

private def assembly_instruction (operands : List AssemblyOperand) (types : List Ordinary.TypeCode)
    (registers : List Nat) (count : Nat) (line : String) : Option (Option Ordinary.RegisterInstruction) := do
  if ["", "nop", "pause", "lfence", "sfence", "mfence"].contains line then return none
  let flag : Option Ordinary.RegisterOp := match line with
    | "stc" => some .stc | "clc" => some .clc | "cmc" => some .cmc | _ => none
  if let some op := flag then return some ⟨op, 0, 0, .inr 0⟩
  let mnemonic := String.mk (line.toList.takeWhile (!·.isWhitespace))
  let args := ((line.drop mnemonic.length).splitOn ",").map String.trim
  let (width, name) ← if ["setc", "setb", "setnae"].contains mnemonic then some (8, "setc") else do
    let w ← match mnemonic.toList.getLast? with
      | some 'b' => some 8 | some 'w' => some 16 | some 'l' => some 32 | some 'q' => some 64 | _ => none
    pure (w, mnemonic.dropRight 1)
  let resolve := fun (raw : String) => do
    guard (raw.startsWith "%")
    let key := raw.drop 1
    if key.startsWith "[" && key.endsWith "]" then
      let name := (key.drop 1).dropRight 1
      operands.findIdx? (fun spec => spec.1 == some name)
    else key.toNat?
  let widthAt := fun index => do
    let ty ← types[index]?
    guard (ty != .pointer && ty.width * 8 == width)
  let (dst, op, src) ← match args with
    | [destination] => do
      let op ← match name with
        | "inc" => some .inc | "dec" => some .dec | "neg" => some .neg
        | "not" => some .inv | "setc" => some .setc | _ => none
      pure (← resolve destination, op, .inr (0 : Int))
    | [source, destination] => do
      let op : Ordinary.RegisterOp ← match name with
        | "mov" => some .mov | "add" => some .add | "sub" => some .sub | "adc" => some .adc
        | "sbb" => some .sbb | "cmp" => some .cmp | "and" => some .band | "or" => some .bor
        | "xor" => some .bxor | "sal" | "shl" => some .shl | "shr" => some .shr | "sar" => some .sar
        | "rol" => some .rol | "ror" => some .ror | _ => none
      let counted := [.shl, .shr, .sar, .rol, .ror].contains op
      let src ← if source.startsWith "$%" then do
          let key ← resolve (source.drop 1)
          let (_, constraint) ← operands[key]?
          guard (key ≥ count && ["i", "n"].contains constraint)
          pure (.inl (← registers[key]?))
        else if source.startsWith "$" then do
          let n ← (source.drop 1).toInt?
          let bits := min width 32
          guard (if counted then -128 ≤ n && n ≤ 255 else
            -(2 ^ (bits - 1) : Int) ≤ n && n < 2 ^ (if width == 64 then bits - 1 else bits))
          pure (.inr n)
        else do
          let key ← resolve source
          widthAt key
          let (_, constraint) ← operands[key]?
          guard (!counted && !["i", "n"].contains constraint)
          pure (.inl (← registers[key]?))
      pure (← resolve destination, op, src)
    | _ => none
  widthAt dst
  let target ← registers[dst]?
  guard (target < count || op == .cmp)
  return some ⟨op, width, target, src⟩

private def ordinary_assembly (raw : String) (children : List Json)
    (decode : Bool → Json → Except String Ordinary.Expression) : Except String Ordinary.Statement := do
  let (lines, outputs, inputs) ← require (assembly_syntax raw) "invalid ordinary assembly template or constraints"
  let operands := outputs ++ inputs
  let names := operands.filterMap Prod.fst
  unless operands.length == children.length && decide names.Nodup do throw "ordinary assembly operand list differs"
  let types ← children.mapM fun child =>
    let spelling := type_spelling child
    require ((ordinary_integer_type spelling).orElse (fun _ => do
      guard ((ordinary_type spelling) == some .pointer)
      return .pointer)) "ordinary assembly requires integer or pointer operands"
  let results ← outputs.zipIdx.mapM fun ((_, constraint), key) => do
    unless ["+r", "+&r", "=r", "=&r"].contains constraint do throw "invalid ordinary assembly output"
    let ty ← require types[key]? "missing assembly output"
    return (ty, constraint.startsWith "+")
  let arguments ← inputs.zipIdx.mapM fun ((_, constraint), key) => do
    if ["r", "n", "i"].contains constraint then return outputs.length + key
    let tied ← require (if constraint.startsWith "[" && constraint.endsWith "]" then
      outputs.findIdx? (fun spec => spec.1 == some ((constraint.drop 1).dropRight 1)) else constraint.toNat?)
      "invalid ordinary assembly input constraint"
    unless tied < outputs.length && types[tied]? == types[outputs.length + key]? do
      throw "ordinary assembly tied operands differ"
    return tied
  let registers := List.range outputs.length ++ arguments
  let ops ← lines.mapM fun line => require (assembly_instruction operands types registers outputs.length line)
    ("unsupported ordinary assembly instruction: " ++ line)
  let values ← children.zipIdx.mapM fun (child, index) => do
    let expr ← decode (index < outputs.length) child
    unless ordinary_root_effect expr do throw "unsequenced assembly operand"
    return expr
  unless values.length ≤ 1 || values.all ordinary_read_only do throw "unsequenced assembly operands"
  return .assembly ⟨results, arguments, ops.reduceOption⟩ (values.foldr .dimension .emptyArguments)

private def ordinary_statement (arithmetic : Option ClosedProgram) (records : List Ordinary.RecordLayout) (symbols : List OrdinarySignature)
    (globals : List OrdinaryObject) (result : String) :
    Nat → Bool → Bool → List OrdinaryLocal → Nat → Json → Except String (List OrdinaryLocal × Ordinary.Statement)
  | 0, _, _, _, _, _ => .error "ordinary statement nesting exceeds the frontend budget"
  | budget + 1, inLoop, inSwitch, scope, slot, node => do
    let decode := ordinary_statement arithmetic records symbols globals result budget
    let descend := decode inLoop inSwitch scope
    let expression := fun scope message node => do
      let value ← ordinary_expr records symbols globals scope (budget + 1) false node
      unless arithmetic.isSome || ordinary_root_effect value do throw (effect_diagnostic message node)
      return value
    let guard := fun scope node => do
      unless (ordinary_type (type_spelling node)).isSome do throw "ordinary guard must be scalar"
      let value ← ordinary_expr records symbols globals scope (budget + 1) false node
      unless arithmetic.isSome || ordinary_root_effect value do throw (effect_diagnostic "nested ordinary guard effects require a sequencing proof" node)
      return value
    match field_text node "kind", child_nodes node with
    | "GCCAsmStmt", operands =>
      let literals ← ordinary_literals records (budget + 1) slot node
      let decode := ordinary_expr records symbols globals (scope ++ literals) (budget + 1)
      return (literals, ← ordinary_assembly (field_text node "heresyAssembly") operands decode)
    | "CompoundStmt", children =>
      let (locals, _, reversed, pending) ← children.foldlM (fun (locals, visible, reversed, pending) child => do
        let next := slot + locals.length
        if let some probe := pending then
          let parse := expression visible "nested ordinary array bound effects require a sequencing proof"
          let (binding, statement) ← ordinary_array_local probe child (budget + 1) next visible parse
          return (locals ++ [binding], visible ++ [binding], statement :: reversed, none)
        else if let some (index, probe) := ordinary_probe child then
          if index == local_array_order then
            return (locals, visible, .arrayProbe :: reversed, some probe)
          else
            unless scope.any (fun binding => binding.kind == "ParmVarDecl" && binding.slot == index &&
                binding.pointerShape.any (·.probe == field_text probe "id")) do
              throw "ordinary parameter probe is outside its function"
            return (locals, visible, .arrayProbe :: reversed, none)
        else
          let (newLocals, statement) ← decode inLoop inSwitch visible next child
          let visible := if field_text child "kind" == "DeclStmt" then visible ++ newLocals else visible
          return (locals ++ newLocals, visible, statement :: reversed, none)) ([], scope, [], none)
      unless pending.isNone do throw "ordinary array probe has no declaration"
      return (locals, .block (reversed.foldl (fun rest stmt => .sequence stmt rest) .empty))
    | "DeclStmt", declarations@(_ :: _ :: _) =>
      let (locals, actions) ← declarations.foldlM (fun (locals, actions) declaration => do
        let inner := Json.mkObj [("kind", .str "DeclStmt"), ("inner", .arr #[declaration])]
        let (bound, action) ← decode inLoop inSwitch (scope ++ locals) (slot + locals.length) inner
        return (locals ++ bound, action :: actions)) ([], [])
      return (locals, .declarations (actions.foldl (fun rest action => .sequence action rest) .empty))
    | "DeclStmt", [declaration] =>
      if field_text declaration "kind" == "EnumDecl" then return ([], .arrayProbe)
      if field_text declaration "kind" == "RecordDecl" then
        let tag := field_text declaration "tagUsed" ++ " " ++ field_text declaration "name"
        unless records.any (·.spelling == tag) do throw ("unsupported ordinary block-scope record: " ++ tag)
        return ([], .arrayProbe)
      let name := field_text declaration "name"
      let ident := field_text declaration "id"
      let spelling := type_spelling declaration
      unless ordinary_name name && !ident.isEmpty && !(scope.any (fun value => value.ident == ident)) do
        throw "invalid ordinary declaration identity"
      if field_text declaration "kind" == "VarDecl" && field_text declaration "storageClass" == "static" then
        unless globals.any (fun object => object.owner.isSome && object.identities == [ident] &&
            object.definition == declaration) do throw "unknown ordinary block-scope static"
        return ([], .arrayProbe)
      if field_text declaration "kind" == "TypedefDecl" then
        if records.any (·.spelling == spelling) || (ordinary_integer_type spelling).isSome ||
            (array_pointer_parts spelling).any (fun (element, bounds) => (fixed_dimensions (element ++ bounds)).isSome) ||
            (fixed_dimensions spelling).any (fun (base, _) => (ordinary_integer_type base).isSome) then
          return ([], .arrayProbe)
        let (element, dimensions) ← ordinary_shape_parts spelling
        let ty ← require (ordinary_type element) "unsupported ordinary array alias element"
        unless dimensions.any (fun bound => bound.toNat?.isNone) do
          throw "ordinary local typedef requires a variable-length array shape"
        let [type] := child_nodes declaration | throw "ordinary array alias lacks a type"
        let bounds ← ordinary_captured_bounds element (budget + 1) dimensions type
        let parse := expression scope "nested ordinary array bound effects require a sequencing proof"
        let captured ← ordinary_bound_list bounds parse
        let shape : OrdinaryShape := ⟨element, ty.width, dimensions⟩
        return ([⟨ident, name, spelling, .dynamicArray shape, "TypedefDecl", slot, none⟩],
          .declareArray slot ty.width captured true)
      if let some (alias, shape) := ordinary_array_alias scope (json_field declaration "type") then
        unless field_text declaration "kind" == "VarDecl" && field_text declaration "storageClass" == "" &&
            (child_nodes declaration).isEmpty do
          throw "invalid ordinary declaration from a captured array alias"
        return ([⟨ident, name, spelling, .dynamicArray shape, "VarDecl", slot, none⟩], .arrayFromAlias slot alias.slot)
      let storage ← require (ordinary_storage records spelling) ("unsupported ordinary local type: " ++ spelling)
      unless field_text declaration "kind" == "VarDecl" && field_text declaration "storageClass" == "" do
        throw "unsupported ordinary local declaration"
      let width := storage.width
      unless width ≤ 9223372036854775792 do throw "ordinary local size exceeds host limits"
      let children := child_nodes declaration
      if children.isEmpty then
        return ([⟨ident, name, spelling, storage, "VarDecl", slot, none⟩], .uninitialised slot)
      let [initializer] := children | throw "unsupported ordinary local initializer"
      unless ordinary_decl initializer spelling do throw "unsupported ordinary local declaration"
      let literals ← ordinary_literals records (budget + 1) (slot + 1) initializer
      let parse := expression (scope ++ literals) "nested ordinary initializer effects require a sequencing proof"
      let initialise := do
        let stores ← ordinary_stores records parse (budget + 1) storage initializer
        unless Ordinary.Initialiser.fits width stores do throw "ordinary local initialiser spans overlap or exceed the object"
        pure (Ordinary.Statement.initialiseAggregate slot width stores)
      let action ← match storage with
        | .scalar ty =>
          if let some plain := atomic_underlying spelling then
            let [value] := child_nodes initializer | throw "ordinary atomic initializer requires a value"
            unless field_text initializer "kind" == "ImplicitCastExpr" && field_text initializer "castKind" == "NonAtomicToAtomic" &&
                ordinary_decl value plain do throw "incorrect ordinary atomic initializer type"
            pure (.initialiseAtomic slot ty (← parse value))
          else if ty.component.isSome && field_text initializer "kind" == "InitListExpr" then initialise
          else pure (.initialise slot ty (← parse initializer))
        | .array .. => initialise
        | .record layout =>
          if field_text initializer "kind" == "InitListExpr" then initialise
          else
            let ty ← require (ordinary_record_code layout) "ordinary record has no value representation"
            pure (.initialise slot ty (← parse initializer))
        | .dynamicArray _ => throw "ordinary dynamic arrays require a typed probe"
        | .vaList => throw "ordinary variadic cursor has a declaration initialiser"
      return (⟨ident, name, spelling, storage, "VarDecl", slot, none⟩ :: literals, action)
    | "IfStmt", condition :: chosen :: fallback =>
      let literals ← ordinary_literals records (budget + 1) slot condition
      let tested ← guard (scope ++ literals) condition
      let after := slot + literals.length
      let (yesLocals, yes) ← descend after chosen
      let (noLocals, no) ← match fallback with
        | [] => pure ([], .empty)
        | [other] => descend (after + yesLocals.length) other
        | _ => throw "invalid ordinary branch"
      return (literals ++ yesLocals ++ noLocals, .branch tested yes no)
    | "WhileStmt", [condition, body] =>
      let literals ← ordinary_literals records (budget + 1) slot condition
      let tested ← guard (scope ++ literals) condition
      let (locals, action) ← decode true inSwitch scope (slot + literals.length) body
      return (literals ++ locals, .whileDo tested action)
    | "DoStmt", [body, condition] =>
      let (locals, action) ← decode true inSwitch scope slot body
      let literals ← ordinary_literals records (budget + 1) (slot + locals.length) condition
      return (locals ++ literals, .doWhile action (← guard (scope ++ literals) condition))
    | "ForStmt", [initial, conditionVariable, condition, advance, body] =>
      unless field_text conditionVariable "kind" == "" && (child_nodes conditionVariable).isEmpty do
        throw "ordinary for loop requires an expression guard"
      unless ["DeclStmt", "NullStmt", ""].contains (field_text initial "kind") ||
          (ordinary_type (type_spelling initial)).isSome do
        throw "ordinary for loop requires a declaration or expression initialiser"
      let (initialLocals, start) ← descend slot initial
      let visible := scope ++ initialLocals
      let first := slot + initialLocals.length
      let testLocals ← ordinary_literals records (budget + 1) first condition
      let stepLocals ← ordinary_literals records (budget + 1) (first + testLocals.length) advance
      let tested ← if field_text condition "kind" == "" && (child_nodes condition).isEmpty then pure none
        else some <$> guard (visible ++ testLocals) condition
      let step ← if field_text advance "kind" == "" && (child_nodes advance).isEmpty then pure none
        else some <$> expression (visible ++ stepLocals) "nested ordinary advance effects require a sequencing proof" advance
      let bounds := initialLocals ++ testLocals ++ stepLocals
      let (bodyLocals, action) ← decode true inSwitch visible (slot + bounds.length) body
      return (bounds ++ bodyLocals, .forDo start tested action step)
    | "GotoStmt", [] =>
      let identity := field_text node "targetLabelDeclId"
      unless !identity.isEmpty do throw "ordinary goto lacks a label identity"
      return ([], .gotoLabel identity)
    | "IndirectGotoStmt", [address] =>
      let locals ← ordinary_literals records (budget + 1) slot address
      return (locals, .indirect (← ordinary_label_choice ((symbols.head?.map (·.functions)).getD []) (guard (scope ++ locals)) (budget + 1) address))
    | "LabelStmt", [child] =>
      let identity := field_text node "declId"
      unless !identity.isEmpty do throw "ordinary label lacks a declaration identity"
      let (locals, action) ← descend slot child
      return (locals, .label identity action)
    | "SwitchStmt", [condition, body] =>
      let literals ← ordinary_literals records (budget + 1) slot condition
      let selector ← guard (scope ++ literals) condition
      let (locals, action) ← decode inLoop true scope (slot + literals.length) body
      return (literals ++ locals, .select selector action)
    | "CaseStmt", lower :: tail =>
      unless inSwitch do throw "ordinary case outside a switch"
      let (upper, child) ← match tail with
        | [child] => pure (lower, child)
        | [upper, child] => pure (upper, child)
        | _ => throw "invalid ordinary case"
      let lo ← ordinary_case_bound (budget + 1) lower
      let hi ← ordinary_case_bound (budget + 1) upper
      unless lo ≤ hi do throw "empty ordinary case range"
      let (locals, action) ← descend slot child
      return (locals, .caseOf (some (lo, hi)) action)
    | "DefaultStmt", [child] =>
      unless inSwitch do throw "ordinary default outside a switch"
      let (locals, action) ← descend slot child
      return (locals, .caseOf none action)
    | "BreakStmt", [] =>
      unless inLoop || inSwitch do throw "ordinary break outside a loop or switch"
      return ([], .stop)
    | "ContinueStmt", [] =>
      unless inLoop do throw "ordinary continue outside a loop"
      return ([], .restart)
    | "NullStmt", [] | "", [] => return ([], .skip)
    | "ReturnStmt", [] =>
      unless result == "void" do throw "ordinary nonvoid return requires a value"
      return ([], .result (.sizeLiteral 0))
    | "ReturnStmt", [value] =>
      if let [compound] := child_nodes value then
        if field_text compound "kind" == "CompoundLiteralExpr" then
          let [initializer] := child_nodes compound | throw "ordinary compound literal requires an initialiser"
          let ident := field_text compound "id"
          unless field_text value "kind" == "ImplicitCastExpr" && field_text value "castKind" == "LValueToRValue" &&
              !ident.isEmpty && ordinary_decl value result && ordinary_decl compound result && ordinary_decl initializer result do
            throw "ordinary compound literal differs from its result type"
          let layout ← require (records.find? (·.spelling == result)) "ordinary compound return requires a record"
          let ty ← require (ordinary_record_code layout) "ordinary compound return requires a complete record"
          let nested ← ordinary_literals records (budget + 1) (slot + 1) initializer
          let stores ← ordinary_stores records (expression (scope ++ nested) "unsequenced ordinary compound initialiser") (budget + 1) (.record layout) initializer
          unless Ordinary.Initialiser.fits layout.width stores do throw "ordinary compound literal stores exceed its layout"
          return (⟨ident, "", result, .record layout, "CompoundLiteralExpr", slot, none⟩ :: nested,
            .initialiseAggregate slot layout.width stores (some ty))
      let literals ← ordinary_literals records (budget + 1) slot value
      return (literals, .result (← ordinary_return arithmetic records symbols globals result (scope ++ literals) (budget + 1) node))
    | _, _ =>
      let literals ← ordinary_literals records (budget + 1) slot node
      let value ← expression (scope ++ literals) "nested ordinary effects require a sequencing proof" node
      return (literals, .discard value)

private def ordinary_parameter (records : List Ordinary.RecordLayout) (node : Json) : Except String OrdinaryLocal := do
  let name := field_text node "name"
  let ident := field_text node "id"
  let spelling := type_spelling node
  let storage ← require (ordinary_storage records spelling) ("unsupported ordinary parameter type: " ++ spelling)
  unless storage.value_type.isSome do throw "ordinary parameter lacks an ABI value type"
  unless field_text node "kind" == "ParmVarDecl" && ordinary_name name && !ident.isEmpty &&
      field_text node "storageClass" == "" && (child_nodes node).isEmpty do
    throw "unsupported ordinary parameter"
  return ⟨ident, name, spelling, storage, "ParmVarDecl", 0, none⟩

private def ordinary_parameters_with_shapes (budget : Nat) (parameters : List OrdinaryLocal) (body : Json) :
    Except String (List OrdinaryLocal) := do
  let probes := (child_nodes body).takeWhile (fun child =>
    (ordinary_probe child).any (fun (index, _) => index != local_array_order))
  probes.foldlM (fun parameters child => do
    let (index, probe) ← require (ordinary_probe child) "invalid ordinary parameter probe"
    let parameter ← require parameters[index]? "ordinary parameter probe has no parameter"
    unless parameter.pointerShape.isNone do throw "duplicate ordinary parameter probe"
    let shape ← ordinary_pointer_probe budget parameter.spelling probe
    return parameters.set index { parameter with pointerShape := some shape }) parameters

private def ordinary_signature (unit : OrdinaryUnit) (node : Json) : Except String OrdinarySignature := do
  let name := field_text node "name"
  let spelling := type_spelling node
  let rawResult :: signature := spelling.splitOn "(" | throw "missing ordinary function type"
  let tail := String.intercalate "(" signature
  let result := rawResult.trim
  let ty ← if result == "void" then pure none
    else some <$> require (ordinary_value_type unit.records result) ("unsupported ordinary result type in " ++ name ++ ": " ++ result)
  let body :: arguments := (child_nodes node).reverse | throw "ordinary callee requires a body"
  let parameters ← arguments.reverse.mapM (ordinary_parameter unit.records)
  let parameters := parameters.zipIdx.map fun (parameter, slot) => { parameter with slot }
  let variadic := json_field node "variadic" == .bool true
  let parameterText := if parameters.isEmpty && !variadic then "void"
    else String.intercalate ", " (parameters.map (·.spelling) ++ if variadic then ["..."] else [])
  unless ordinary_name name && field_text body "kind" == "CompoundStmt" && tail == parameterText ++ ")" &&
      ["", "static"].contains (field_text node "storageClass") &&
      decide ((parameters.map (·.ident)).Nodup) do
    throw "unsupported ordinary function definition"
  let parameters ← ordinary_parameters_with_shapes unit.budget parameters body
  let symbol := unit_function_key unit.namespaceName unit.declarations name
  return ⟨name, symbol, spelling, result, ty, parameters, [], body, unit.records, variadic, []⟩

private def ordinary_prototype (symbol : OrdinarySignature) (node : Json) : Except String Nat := do
  let children := child_nodes node
  unless type_spelling node == symbol.spelling &&
      ["", "static", "extern"].contains (field_text node "storageClass") &&
      children.length == symbol.parameters.length &&
      (children.zip symbol.parameters).all (fun (argument, expected) =>
        field_text argument "kind" == "ParmVarDecl" && ordinary_decl argument expected.spelling &&
        field_text argument "id" != "" && (child_nodes argument).isEmpty) do
    throw "ordinary prototype differs from its definition"
  return children.length

private def ordinary_parameter_shape (records : List Ordinary.RecordLayout) (symbols : List OrdinarySignature)
    (globals : List OrdinaryObject) (parameters : List OrdinaryLocal) (budget : Nat) (parameter : OrdinaryLocal) :
    Except String (Option Ordinary.ParameterShape) := do
  let some captured := parameter.pointerShape | return none
  let some bounds := captured.bounds | return none
  let expressions ← ordinary_bound_list bounds fun node => do
    let expression ← ordinary_expr records symbols globals (parameters.take parameter.slot) budget false node
    unless ordinary_root_effect expression do throw "nested ordinary parameter effects require a sequencing proof"
    return expression
  return some ⟨parameter.slot, captured.shape.width, captured.skip, expressions⟩

private def ordinary_introspects : Nat → Json → Bool
  | 0, _ => false
  | depth + 1, node =>
    let children := child_nodes node
    let here := match field_text node "kind", children with
      | "CallExpr", target :: _ => (ordinary_callee target).toOption.any (fun (name, _, _) =>
          ["__builtin_va_start", "zargs"].contains name)
      | _, _ => false
    here || children.any (ordinary_introspects depth)

private def ordinary_atomic_builtin (node : Json) : Bool :=
  let name := field_text node "name"
  (name.startsWith "__c11_atomic_" || name.startsWith "__atomic_") &&
    json_field node "isImplicit" == .bool true && ordinary_decl node "void ()" &&
    (child_nodes node).map (fun child => field_text child "kind") == ["BuiltinAttr"]

private def ordinary_procedures (arithmetic : Option ClosedProgram) (records : List Ordinary.RecordLayout) (symbols : List OrdinarySignature)
    (globals : List OrdinaryObject) (namespaceName : String) (labels : List (String × String)) (budget slot graphCount : Nat) :
    List Json → Except String (List Ordinary.Procedure)
  | [] => .ok []
  | declaration :: rest => do
    if ordinary_atomic_builtin declaration then
      return ← ordinary_procedures arithmetic records symbols globals namespaceName labels budget slot graphCount rest
    if let some arity := ordinary_implicit_va declaration then
      return ← ordinary_procedures arithmetic records symbols globals namespaceName labels budget (slot + arity) graphCount rest
    let symbol ← require (symbols.find? fun symbol => symbol.name == field_text declaration "name")
      ("ordinary prototype has no checked definition: " ++ field_text declaration "name")
    if (child_nodes declaration).any (fun node => field_text node "kind" == "CompoundStmt") then
      let visible := globals.filter fun object => object.owner.isNone || object.owner == some symbol.name
      let (locals, statements) ← (ordinary_statement arithmetic records symbols visible symbol.result budget false false
        symbol.parameters symbol.parameters.length symbol.entry).mapError (fun why => symbol.name ++ ": " ++ why)
      let bindings := symbol.parameters ++ locals
      unless decide ((bindings.map (·.ident)).Nodup) do throw "ordinary locals share a declaration identity"
      let slots := bindings.map fun binding => namespaceName ++ binding.name ++ "." ++ toString (slot + binding.slot)
      let graphName := "g_" ++ namespaceName.replace ":" "_" ++ toString graphCount
      let dispatch ← if statements.needs_dispatch then some <$> Ordinary.compile_dispatch graphName statements labels else pure none
      let parameters ← symbol.parameters.mapM fun parameter =>
        require parameter.storage.value_type "ordinary parameter lacks an ABI value type"
      let shapes ← symbol.parameters.mapM (ordinary_parameter_shape records symbols visible symbol.parameters budget)
      let procedure : Ordinary.Procedure :=
        ⟨symbol.symbol, symbol.ty, parameters, locals.map (·.storage.frame_width), slots, statements, dispatch,
          shapes.filterMap id, locals.any (·.pointerShape.isSome), ordinary_introspects budget symbol.entry,
          (kernel_source declaration budget).toOption.map fun (term, _) => ⟨term⟩⟩
      return procedure :: (← ordinary_procedures arithmetic records symbols globals namespaceName labels budget (slot + bindings.length)
        (graphCount + if dispatch.isSome then 1 else 0) rest)
    else
      let used ← ordinary_prototype symbol declaration
      ordinary_procedures arithmetic records symbols globals namespaceName labels budget (slot + used) graphCount rest

private def ordinary_objects (unit : OrdinaryUnit) : List Json :=
  unit.objects.filter (fun node => field_text node "storageClass" != "extern" || field_text node "init" != "")

private def ordinary_private_object (unit : OrdinaryUnit) (name : String) : Bool :=
  unit.objects.any (fun node => field_text node "name" == name && field_text node "storageClass" == "static")

private def ordinary_availability_definition (node : Json) : Bool := Id.run do
  let [cursor, body] := child_nodes node | return false
  let [returned] := child_nodes body | return false
  let [call] := child_nodes returned | return false
  let [primitive, loaded, count] := child_nodes call | return false
  let [reference] := child_nodes primitive | return false
  let [dereference] := child_nodes loaded | return false
  let [cast] := child_nodes dereference | return false
  let [argument] := child_nodes cast | return false
  let [binding] := child_nodes argument | return false
  let [width] := child_nodes count | return false
  return field_text node "storageClass" == "static" && json_field node "inline" == .bool true &&
    field_text cursor "kind" == "ParmVarDecl" && ordinary_va_operand cursor &&
    field_text body "kind" == "CompoundStmt" && field_text returned "kind" == "ReturnStmt" &&
    field_text call "kind" == "CallExpr" && ordinary_decl call "_Bool" &&
    field_text primitive "castKind" == "FunctionToPointerDecay" && field_text reference "kind" == "DeclRefExpr" &&
    field_text (json_field reference "referencedDecl") "name" == "zvalinbounds" &&
    field_text loaded "castKind" == "LValueToRValue" && ordinary_decl loaded "void *" &&
    field_text dereference "opcode" == "*" && ordinary_decl dereference "void *" &&
    field_text cast "castKind" == "BitCast" && ordinary_decl cast "void **" &&
    field_text argument "castKind" == "LValueToRValue" && ordinary_va_operand argument &&
    field_text binding "kind" == "DeclRefExpr" && ordinary_ident binding == field_text cursor "id" &&
    field_text count "castKind" == "IntegralCast" && ordinary_decl count "unsigned long" &&
    field_text width "kind" == "IntegerLiteral" && ordinary_decl width "int" && field_text width "value" == "8" &&
    (child_nodes binding).isEmpty && (child_nodes width).isEmpty && (child_nodes reference).isEmpty

private abbrev TypeAliases := Std.HashMap String String

private structure OrdinaryEnums where
  types : TypeAliases := {}
  constants : Std.HashMap String (String × String × Int) := {}

private def enum_base (spelling : String) : String := Id.run do
  if !spelling.startsWith "enum " then return ""
  if spelling.startsWith "enum (" then
    let first :: _ := spelling.splitOn ")" | return ""
    return first ++ ")"
  return String.mk (spelling.toList.take 5 ++ (spelling.drop 5).toList.takeWhile (fun c => c.isAlphanum || c == '_'))

private def OrdinaryEnums.expand (enums : OrdinaryEnums) (spelling : String) : String := Id.run do
  if !spelling.startsWith "enum " then return spelling
  let tag := enum_base spelling
  let some ty := enums.types[tag]? | return spelling
  return ty ++ spelling.drop tag.length

private def enum_members (node : Json) : Option (String × List (String × String × String × Int)) := do
  let members := child_nodes node
  guard (!members.isEmpty && json_field node "fixedUnderlyingType" == .null)
  let fits := fun width isSigned value => (if isSigned then signed else unsigned) (8 * width) value == value
  let mut next := (0 : Int)
  let mut width := 4
  let mut entries := []
  for member in members do
    let spelling := type_spelling member
    let ty ← ordinary_integer_type spelling
    guard (field_text member "kind" == "EnumConstantDecl" && !((field_text member "id").isEmpty) &&
      ordinary_name (field_text member "name") && ty.width ≤ 8)
    let value ← match child_nodes member with
      | [] => pure next
      | [expr] => do
        guard (field_text expr "kind" == "ConstantExpr")
        (field_text expr "value").toInt?
      | _ => none
    guard (fits ty.width ty.signed value)
    next := value + 1
    width := max width ty.width
    entries := (field_text member "id", field_text member "name", spelling, value) :: entries
  let signed := entries.any (fun entry => entry.2.2.2 < 0)
  guard (entries.all (fun entry => fits width signed entry.2.2.2))
  return ((if signed then "" else "unsigned ") ++ (if width == 4 then "int" else "long"), entries)

private def ordinary_enums (nodes : List Json) : Except String OrdinaryEnums := do
  let mut result : OrdinaryEnums := {}
  let mut ids : TypeAliases := {}
  let mut anonymous := []
  let add := fun (types : TypeAliases) (tag value : String) => do
    if let some old := types[tag]? then
      unless old == value do throw "ambiguous ordinary enum layout"
    pure (types.insert tag value)
  for node in nodes do
    if field_text node "kind" != "EnumDecl" then continue
    let some (ty, members) := enum_members node | continue
    ids := ids.insert (field_text node "id") ty
    for (ident, name, spelling, value) in members do
      result := { result with constants := result.constants.insert ident (name, spelling, value) }
    let name := field_text node "name"
    if name.isEmpty then
      let range := json_field node "range"
      if let .ok first := (json_field (json_field range "begin") "offset").getNat? then
        if let .ok last := (json_field (json_field range "end") "offset").getNat? then
          anonymous := (first, last, ty) :: anonymous
    else result := { result with types := ← add result.types ("enum " ++ name) ty }
  for node in nodes do
    let tag := enum_base (type_spelling node)
    if tag.isEmpty then continue
    if let some ty := ids[field_text (json_field node "ownedTagDecl") "id"]? then
      result := { result with types := ← add result.types tag ty }
    if tag.startsWith "enum (" && ["VarDecl", "FieldDecl"].contains (field_text node "kind") then
      let .ok first := (json_field (json_field (json_field node "range") "begin") "offset").getNat? | continue
      let .ok name := (json_field (json_field node "loc") "offset").getNat? | continue
      let [(_, _, ty)] := anonymous.filter (fun entry => entry.1 == first && entry.2.1 < name) | continue
      let key := tag.replace "unnamed enum at " "unnamed at "
      let types ← add result.types key ty
      result := { result with types := ← add types (key.replace "unnamed at " "unnamed enum at ") ty }
  return result

private def ordinary_aliases (enums : OrdinaryEnums) (nodes : List Json) : TypeAliases :=
  nodes.foldl (fun aliases node => Id.run do
    let key := field_text node "heresyAlias"
    let target := enums.expand (type_spelling node)
    if field_text node "kind" != "TypedefDecl" || key.isEmpty then return aliases
    let supported := (fixed_dimensions target).any (fun (base, _) => (ordinary_integer_type base).isSome) ||
      target != type_spelling node || ["__int128", "unsigned __int128"].contains target || (function_prototype target).isSome ||
      (["struct ", "union "].any target.startsWith && !target.contains '*' && !target.contains '[')
    if !supported then return aliases
    let name := field_text node "name"
    let aliases := aliases.insert key target
    if (nodes.filter (fun other => field_text other "kind" == "TypedefDecl" && field_text other "name" == name)).length == 1 then
      return aliases.insert name target
    return aliases) {}

private def leading_type (spelling : String) : String :=
  String.mk (spelling.toList.takeWhile (fun c => c.isAlphanum || c == '_' || c == '@'))

private def expand_alias (aliases : TypeAliases) (spelling : String) (reference : Bool) : String := Id.run do
  let qualified := spelling.startsWith "const "
  let plain := if qualified then spelling.drop 6 else spelling
  let word := leading_type plain
  if !reference && !word.startsWith "@type" then return spelling
  let some target := aliases[word]? | return spelling
  let suffix := plain.drop word.length
  if let [head, tail] := target.splitOn "(*)(" then
    let qualifier := if qualified then "const" else ""
    if suffix.startsWith "[" || suffix.isEmpty then return head ++ "(*" ++ qualifier ++ suffix ++ ")(" ++ tail
    if suffix.startsWith " *" && suffix.trim.toList.all (· == '*') then
      return head ++ "(*" ++ qualifier ++ (if qualified then " " else "") ++ suffix.trim ++ ")(" ++ tail
    return spelling
  if qualified then
    if ["struct ", "union "].any target.startsWith && !target.contains '*' && !target.contains '[' then
      return "const " ++ target ++ suffix
    return spelling
  let some (base, sizes) := fixed_dimensions target | return target ++ suffix
  let bounds := String.join (sizes.map (fun n => "[" ++ toString n ++ "]"))
  if suffix.isEmpty then return target
  if suffix.startsWith "[" && (fixed_dimensions ("x" ++ suffix)).isSome then return base ++ suffix ++ bounds
  if suffix.startsWith " *" && suffix.trim.toList.all (· == '*') then return base ++ " (" ++ suffix.trim ++ ")" ++ bounds
  return spelling

private abbrev DeclaredTypes := Std.HashMap String (String × String)

private def declared_types (aliases names : TypeAliases) (nodes : List Json) : DeclaredTypes :=
  nodes.foldl (fun types node => Id.run do
    let ident := field_text node "id"
    let spelling := type_spelling node
    let word := leading_type spelling
    let some name := names[word]? | return types
    let canonical := expand_alias aliases spelling false
    if ident.isEmpty || canonical == spelling then return types
    return types.insert ident (name ++ spelling.drop word.length, canonical)) {}

private def store_block_result (decl : Json) : Nat → Json → Option Json
  | 0, _ => none
  | depth + 1, node => do
    if field_text node "kind" == "LabelStmt" then
      let [child] := child_nodes node | none
      return node.setObjVal! "inner" (.arr #[← store_block_result decl depth child])
    guard (ordinary_decl node (type_spelling decl) && field_text node "valueCategory" == "prvalue")
    let ty := json_field decl "type"
    let ref := Json.mkObj [("id", json_field decl "id"), ("kind", .str "VarDecl"),
      ("name", json_field decl "name"), ("type", ty)]
    let place := Json.mkObj [("kind", .str "DeclRefExpr"), ("referencedDecl", ref),
      ("type", ty), ("valueCategory", .str "lvalue")]
    return Json.mkObj [("kind", .str "BinaryOperator"), ("opcode", .str "="), ("type", ty),
      ("valueCategory", .str "prvalue"), ("inner", .arr #[place, node])]

private def block_initialiser (budget : Nat) (stmt : Json) : Option (List Json) := do
  let [decl] := child_nodes stmt | none
  guard (field_text stmt "kind" == "DeclStmt" && field_text decl "kind" == "VarDecl" &&
    field_text decl "storageClass" == "" && ["int", "unsigned int", "long", "unsigned long"].contains (written_type decl))
  let [init] := child_nodes decl | none
  let expr ← if field_text init "kind" == "GenericSelectionExpr" then (ordinary_selected init).toOption else some init
  guard (field_text expr "kind" == "StmtExpr" && ordinary_decl expr (type_spelling decl))
  let [block] := child_nodes expr | none
  guard (field_text block "kind" == "CompoundStmt")
  let last :: preceding := (child_nodes block).reverse | none
  let assignment ← store_block_result decl budget last
  let declaration := stmt.setObjVal! "inner" (.arr #[decl.setObjVal! "inner" (.arr #[])])
  return [declaration, block.setObjVal! "inner" (.arr (preceding.reverse ++ [assignment]).toArray)]

private def ordinary_types (enums : OrdinaryEnums) (aliases : TypeAliases) (declarations : DeclaredTypes) : Nat → Bool → Json → Except String Json
  | 0, _, _ => .error "incomplete ordinary type traversal"
  | fuel + 1, reference, node => do
    let mut result := node
    if field_text node "kind" == "DeclRefExpr" && field_text (json_field node "referencedDecl") "kind" == "EnumConstantDecl" then
      let ref := json_field node "referencedDecl"
      let value := do
        let (name, ty, value) ← enums.constants[ordinary_ident node]?
        guard (name == field_text ref "name" && type_spelling node == ty && type_spelling ref == ty)
        return Json.str (toString value)
      result := result.setObjVal! "ordinaryEnumValue" (value.getD .null)
    for key in ["type", "argType"] do
      let ty := json_field node key
      let spelling := qualified_spelling ty
      if !spelling.isEmpty then
        let canonical := match reference, declarations[field_text node "id"]? with
          | true, some (written, target) => if written == spelling then target else expand_alias aliases spelling reference
          | _, _ => enums.expand (expand_alias aliases spelling reference)
        if canonical != spelling then
          result := result.setObjVal! key (ty.setObjVal! "desugaredQualType" (.str canonical))
    for key in ["inner", "array_filler"] do
      if let .arr entries := json_field node key then
        result := result.setObjVal! key (.arr (← entries.mapM (ordinary_types enums aliases declarations fuel false)))
    for key in ["referencedDecl", "field"] do
      if let .obj _ := json_field node key then
        result := result.setObjVal! key (← ordinary_types enums aliases declarations fuel true (json_field node key))
    if field_text result "kind" == "CompoundStmt" then
      let children := (child_nodes result).flatMap (fun child => (block_initialiser (fuel + 1) child).getD [child])
      return result.setObjVal! "inner" (.arr children.toArray)
    return result

private def literal_object (occupied : Std.HashSet String) (decl : Json) : Option (List Json) := do
  guard (field_text decl "kind" == "VarDecl" && (field_text decl "tls").isEmpty)
  let [decay] := child_nodes decl | none
  guard (field_text decay "kind" == "ImplicitCastExpr" && field_text decay "castKind" == "ArrayToPointerDecay")
  let [literal] := child_nodes decay | none
  guard (field_text literal "kind" == "CompoundLiteralExpr" && field_text literal "valueCategory" == "lvalue" &&
    !(field_text literal "id").isEmpty)
  let [init] := child_nodes literal | none
  guard (field_text init "kind" == "InitListExpr" && ordinary_decl init (type_spelling literal))
  let stem := "__heresy_literal_" ++ field_text decl "name" ++ "_"
  let rec fresh : Nat → Nat → Option String
    | 0, _ => none
    | fuel + 1, i =>
      let candidate := stem ++ toString i
      if occupied.contains candidate then fresh fuel (i + 1) else some candidate
  let name ← fresh (occupied.size + 1) 0
  let ty := json_field literal "type"
  let fields : List (String × Json) := [("kind", .str "VarDecl"), ("id", json_field literal "id"), ("type", ty), ("name", .str name)]
  let ref := Json.mkObj fields
  let address := Json.mkObj [("kind", .str "DeclRefExpr"), ("valueCategory", .str "lvalue"), ("type", ty), ("referencedDecl", ref)]
  let backing := Json.mkObj (fields ++ [("storageClass", .str "static"), ("init", .str "c"),
    ("loc", json_field decl "loc"), ("inner", .arr #[init])])
  return [decl.setObjVal! "inner" (.arr #[decay.setObjVal! "inner" (.arr #[address])]), backing]

private def ordinary_unit (namespaceName : String) (budget : Nat) (tree : Json) : Except String OrdinaryUnit := do
  let all ← startup_nodes (budget + 1) tree
  let typedefs := all.filter (fun node => field_text node "kind" == "TypedefDecl")
  let enums ← ordinary_enums all
  let aliases := ordinary_aliases enums typedefs
  let names : TypeAliases := typedefs.foldl (fun names node => names.insert (field_text node "heresyAlias") (field_text node "name")) {}
  let tree ← ordinary_types enums aliases (declared_types aliases names all) (budget + 1) false tree
  let occupied : Std.HashSet String := (all.filter (fun node => ["VarDecl", "FunctionDecl"].contains (field_text node "kind"))).foldl
    (fun names node => names.insert (field_text node "name")) {}
  let nodes := (child_nodes tree).flatMap (fun decl => (literal_object occupied decl).getD [decl])
  let tree := tree.setObjVal! "inner" (.arr nodes.toArray)
  let declarations := unit_function_declarations tree
  let objects := nodes.filter (fun node => source_declaration node && field_text node "kind" == "VarDecl")
  let builtin := ["fopen", "fread", "fwrite", "fclose", "calloc", "memset", "strlen", "strcmp", "printf", "puts", "zhasvalidcap", "zis_readonly", "zgetupper", "zgetlower", "malloc", "memcpy", "memmove", "putchar", "free", "exit", "__builtin_va_start", "__builtin_va_copy",
    "__builtin_va_end", "zargs", "zcan_va_arg", "pthread_create", "pthread_join", "pthread_self", "pthread_equal"] ++ SyncOp.all.map SyncOp.name
  let standard := fun node =>
    let name := field_text node "name"
    if name == "zcan_va_arg" then ordinary_availability_definition node
    else !builtin.contains name
  unless !(declarations.any (fun node => builtin.contains (field_text node "name") && (ordinary_implicit_va node).isNone)) &&
      !(objects.any (fun node => builtin.contains (field_text node "name"))) &&
      (function_definitions nodes).all standard do
    throw "ordinary certificate requires standard builtins"
  let functions : List (String × List Json) ← (function_definitions declarations).mapM (fun node =>
    (field_text node "name", ·) <$> startup_nodes (budget + 1) node)
  let localTags := functions.flatMap fun (_, body) =>
    (body.filter (fun stmt => field_text stmt "kind" == "DeclStmt")).flatMap child_nodes
  let tags := (nodes ++ localTags).filter (fun node => field_text node "kind" == "RecordDecl")
  let records ← tags.foldlM (collect_records (budget + 1)) []
  let inlineEntries := ((json_field tree "heresyInlineRecords").getArr?.toOption.getD #[]).toList
  let members := functions.flatMap fun (_, body) => body.filter (fun node => field_text node "kind" == "MemberExpr" || json_field node "field" != .null)
  let records := inlineEntries.foldl (fun layouts entry => match inline_record layouts members entry with
    | some layout => layout :: layouts
    | none => layouts) records
  let recordNames : List String := List.map Ordinary.RecordLayout.spelling records
  unless decide recordNames.Nodup do throw "ambiguous ordinary record definition"
  let references := functions.flatMap (fun entry => entry.2.filterMap (fun node =>
    if field_text node "kind" == "DeclRefExpr" then some (field_text (json_field node "referencedDecl") "name") else none))
  return ⟨namespaceName, budget, tree, declarations, objects, records, label_names namespaceName functions,
    references.any (fun name => (file_signature name).isSome), references.contains "pthread_create",
    functions.flatMap (fun (owner, nodes) => nodes.filterMap fun node =>
      if field_text node "kind" == "VarDecl" && field_text node "storageClass" == "static" then some (owner, node) else none)⟩

private def ordinary_alias (unit : OrdinaryUnit) (key : String) : Option String := do
  guard (key.startsWith "@type" && (key.drop 5).toNat?.isSome)
  let [entry] := (child_nodes unit.tree).filter (fun node => field_text node "kind" == "TypedefDecl" &&
    field_text node "heresyAlias" == key) | none
  return type_spelling entry

private def ordinary_callback (unit : OrdinaryUnit) (spelling : String) : Option OrdinaryCallback := do
  let [head, tail] := spelling.splitOn "(*" | none
  guard (tail == "const)(void)" || tail == ")(void)")
  let key := head.trim
  let result ← ordinary_alias unit key
  guard (ordinary_type result == some .pointer)
  let entry ← (child_nodes unit.tree).find? (fun node => field_text node "heresyAlias" == key)
  let original := field_text entry "name"
  guard (ordinary_name original)
  return ⟨key, spelling.replace key original, result⟩

private def ordinary_global_storage (unit : OrdinaryUnit) (spelling : String) : Option (OrdinaryStorage × Bool) := do
  if let [head, tail] := spelling.splitOn "(*" then
    if let [qualifier, suffix] := tail.splitOn "[" then
      let [count, arguments] ← pure (suffix.splitOn "]") | none
      guard (qualifier == "" || qualifier == "const")
      let count ← count.toNat?
      guard (0 < count)
      let element := head ++ "(*" ++ arguments
      guard ((function_prototype element).isSome)
      return (.array element .pointer count, qualifier == "const")
  if let some (element, count) := ordinary_array spelling then
    let readOnly := element.startsWith "const "
    let name := if readOnly then element.drop 6 else element
    if element.endsWith "*const" && (data_pointee element).isSome then
      return (.array (element.take (element.length - 5)) .pointer count, true)
    if let some target := ordinary_alias unit name then
      if (function_prototype target).isSome then return (.array target .pointer count, readOnly)
  let readOnly := (spelling.splitOn "(*const)").length == 2 ||
    (spelling.startsWith "const " && !spelling.contains '*')
  let plain := if (spelling.splitOn "(*const)").length == 2 then spelling.replace "(*const)" "(*)"
    else if readOnly then spelling.drop 6 else spelling
  if let [head, tail] := plain.splitOn "(*)(" then
    if let some result := ordinary_alias unit head.trim then
      if (function_prototype (result ++ "(*)(" ++ tail)).isSome then return (.scalar .pointer, readOnly)
  return (← ordinary_storage unit.records plain, readOnly)

private def ordinary_object_definition (unit : OrdinaryUnit) (node : Json) (index : Nat) (owner : Option String := none) :
    Except String OrdinaryObject := do
  let name := field_text node "name"
  let spelling := type_spelling node
  let (storage, readOnly) ← require (ordinary_global_storage unit spelling) ("unsupported ordinary global type for " ++ name ++ ": " ++ spelling)
  unless storage.width ≤ 9223372036854775800 do throw "ordinary global size exceeds host limits"
  unless ordinary_name name && field_text node "id" != "" && ["", "static"].contains (field_text node "tls") &&
      ["", "extern", "static"].contains (field_text node "storageClass") do
    throw "unsupported ordinary global storage"
  let symbol := if owner.isSome || ordinary_private_object unit name then unit.namespaceName ++ name ++ "." ++ toString index
    else "extern:" ++ name
  let pointed := unit.records.find? (·.spelling == ordinary_pointee spelling)
  return ⟨name, symbol, spelling, storage, node, [], pointed, unit.records, readOnly, ordinary_callback unit spelling, owner⟩

private def ordinary_global_scope (unit : OrdinaryUnit) (definitions localDefinitions : List OrdinaryObject) :
    Except String (List OrdinaryObject) := do
  let visible := (child_nodes unit.tree).filter (fun node => field_text node "kind" == "VarDecl")
  let selected := definitions.filter (fun object => object.owner.isNone &&
    if ordinary_private_object unit object.name then
      localDefinitions.any (fun resident => resident.symbol == object.symbol)
    else object.symbol == "extern:" ++ object.name)
  let bindings : List OrdinaryObject ← (selected.filter (fun object => visible.any (fun node => field_text node "name" == object.name))).mapM
    fun object => do
      let declarations := visible.filter (fun node => field_text node "name" == object.name)
      unless ordinary_callback unit object.spelling == object.callback do throw "ordinary callback declarations differ across units"
      unless declarations.all (fun node => ordinary_decl node object.spelling && field_text node "id" != "" &&
          field_text node "tls" == field_text object.definition "tls") do
        throw "ordinary global declaration differs from its definition"
      let layout := match object.storage with
        | .record layout => some layout
        | .array .. => (fixed_dimensions object.spelling).bind fun (element, _) =>
            object.records.find? (·.spelling == element)
        | _ => object.recordTarget
      if let some expected := layout then
        unless unit.records.any (fun actual => actual.spelling == expected.spelling &&
            ordinary_record_compatible object.records unit.records (object.records.length + 1) expected actual) do
          throw "ordinary global record layout disagrees with its definition"
      return { object with identities := declarations.map (field_text · "id") }
  let statics := localDefinitions.filterMap fun object =>
    if object.owner.isSome then some { object with identities := [field_text object.definition "id"] } else none
  let bindings := bindings ++ statics
  let ids : List String := bindings.flatMap (·.identities)
  unless decide ids.Nodup && unit.objects.all (fun node => ids.contains (field_text node "id")) do
    throw "unresolved or ambiguous ordinary global declaration"
  return bindings

private def ordinary_static_value : Ordinary.Expression → Bool
  | .floatingLiteral .. | .literal _ | .sizeLiteral _ | .nullPointer | .globalAddress _ | .functionAddress .. => true
  | .cast _ child | .unary _ _ child => ordinary_static_value child
  | _ => false

private def ordinary_initialiser (unit : OrdinaryUnit) (functions : List String) (symbols : List OrdinarySignature) (globals : List OrdinaryObject)
    (budget : Nat) (object : OrdinaryObject) :
    Except String Ordinary.Global := do
  let scalar := fun (node : Json) => do
    if field_text node "kind" == "AddrLabelExpr" then
      let owner ← require object.owner "ordinary label address has no enclosing function"
      let ident := field_text node "labelDeclId"
      let symbol ← require (unit.labels.lookup ident) "unregistered ordinary label address"
      unless ordinary_decl node "void *" && (child_nodes node).isEmpty &&
          symbol.startsWith ("label:" ++ unit.namespaceName ++ owner ++ ":") do throw "ordinary label address has a different owner"
      let procedure ← require (symbols.find? (·.name == owner)) "missing ordinary label owner"
      let nodes ← startup_nodes budget procedure.entry
      unless nodes.any (fun label => field_text label "kind" == "LabelStmt" && field_text label "declId" == ident &&
          field_text label "name" == field_text node "name") do throw "ordinary label address has no matching statement"
      let index ← require (functions.idxOf? symbol) "ordinary label address has no code"
      return .functionAddress symbol index
    if let some callback := object.callback then
      if let .ok ("pthread_self", signature, ident) := ordinary_callee node then
        let [reference] := child_nodes node | throw "ordinary pthread function requires a declaration"
        let declaration := json_field reference "referencedDecl"
        unless ordinary_decl declaration "pthread_t (void)" && signature == callback.alias ++ " (void)" &&
            ordinary_decl node (object.spelling.replace "(*const)" "(*)") &&
            (child_nodes unit.tree).any (fun entry => field_text entry "kind" == "FunctionDecl" &&
              field_text entry "name" == "pthread_self" && field_text entry "id" == ident && ordinary_decl entry signature) do
          throw "ordinary pthread function address has an incompatible declaration"
        let index ← require (functions.idxOf? "pthread_self") "ordinary pthread function has no registered address"
        return .functionAddress "pthread_self" index
    let expression ← ordinary_expr unit.records symbols globals [] budget false node
    unless ordinary_static_value expression do throw "ordinary global initialiser requires a constant or static address"
    return expression
  let stores : List Ordinary.Initialiser ← match child_nodes object.definition with
    | [] => pure []
    | [initializer] => do
      unless ordinary_decl initializer object.spelling || (object.readOnly &&
          ordinary_decl initializer (object.spelling.replace "(*const)" "(*)")) ||
          (object.readOnly && object.spelling.startsWith "const " && ordinary_decl initializer (object.spelling.drop 6)) do throw "ordinary global initialiser has the wrong type"
      ordinary_stores unit.records scalar budget object.storage initializer
    | _ => throw "unsupported ordinary global initialiser"
  return ⟨object.symbol, object.storage.width, stores, field_text object.definition "tls" == "static", object.readOnly⟩

private def ordinary_local_signature (unit : OrdinaryUnit) (definition : OrdinarySignature) (node : Json) :
    Option OrdinarySignature := do
  let spelling := type_spelling node
  let result :: parametersText := spelling.splitOn "(" | none
  let result := result.trim
  let arguments := (child_nodes node).filter (fun argument => field_text argument "kind" == "ParmVarDecl")
  guard (arguments.length == definition.parameters.length &&
    ordinary_abi_type definition.records unit.records definition.result result)
  let parameters ← (definition.parameters.zip arguments).mapM fun (parameter, argument) => do
    let actual := type_spelling argument
    guard (ordinary_abi_type definition.records unit.records parameter.spelling actual)
    let storage ← ordinary_storage unit.records actual
    guard (storage.value_type == parameter.storage.value_type)
    return { parameter with spelling := actual, storage }
  let suffix := if parameters.isEmpty && !definition.variadic then "void"
    else String.intercalate ", " (parameters.map (·.spelling) ++ if definition.variadic then ["..."] else [])
  guard (String.intercalate "(" parametersText == suffix ++ ")")
  return { definition with spelling, result, parameters }

private def ordinary_imports (unit : OrdinaryUnit) (exports : List OrdinarySignature) (functions : List String) : List OrdinarySignature :=
  let declarations := (child_nodes unit.tree).filter (fun node => field_text node "kind" == "FunctionDecl")
  exports.filterMap fun definition => do
    guard (unit_function_key unit.namespaceName unit.declarations definition.name == definition.symbol)
    let visible := declarations.filter fun declaration =>
      field_text declaration "name" == definition.name &&
        (source_declaration declaration || ["", "extern"].contains (field_text declaration "storageClass"))
    let compatible := visible.filterMap fun declaration => do
      let signature ← ordinary_local_signature unit definition declaration
      return (signature, field_text declaration "id")
    let (localSignature, _) :: _ := compatible | none
    guard (compatible.all (fun (signature, _) => signature.spelling == localSignature.spelling))
    let identities := compatible.map Prod.snd
    guard (!identities.isEmpty && identities.all (!·.isEmpty) && decide identities.Nodup)
    return { localSignature with declarations := identities, functions }

private def ordinary_link (frontends : List String) :
    Except String { program : Ordinary.Program // ∃ trees,
      frontends.mapM Json.parse = .ok trees ∧
        program.procedures.map (·.name) = (link_entries trees).map Prod.fst ∧
        (program.procedures.map (·.name)).Nodup ∧ (program.globals.map (·.name)).Nodup ∧
        program.procedures.all Ordinary.Procedure.control_checked = true ∧
        program.globals.all Ordinary.Global.initialisers_fit = true ∧ program.labels_checked = true } := do
  match frontends.mapM Json.parse with
  | .error why => throw why
  | .ok trees =>
    let units ← (trees.zipIdx).mapM fun (tree, index) =>
      ordinary_unit (unit_namespace trees.length index) (frontends[index]?.getD "").utf8ByteSize tree
    let exports := (← units.mapM fun unit => (function_definitions unit.declarations).mapM (ordinary_signature unit)).flatten
    unless decide ((exports.map (·.symbol)).Nodup) do throw "multiple definitions of an ordinary function"
    unless exports.length ≤ 2 ^ 63 do throw "ordinary function addresses exceed the code space"
    let [entry] := exports.filter (fun definition => definition.symbol == "main")
      | throw "ordinary certificate requires exactly one externally visible main definition"
    unless ["int (void)", "int (int, char **)"].contains entry.spelling do
      throw "ordinary entry must be int main(void) or int main(int, char **)"
    let byUnit ← units.mapM fun unit => do
      let definitions := ordinary_objects unit
      unless decide ((definitions.map (field_text · "name")).Nodup) do
        throw "ordinary certificate requires one definition per global"
      let objects ← definitions.zipIdx.mapM (fun (node, index) => ordinary_object_definition unit node index)
      let statics ← unit.statics.zipIdx.mapM fun ((owner, node), index) =>
        ordinary_object_definition unit node (objects.length + index) (some owner)
      return objects ++ statics
    let allObjects := byUnit.flatten
    unless decide ((allObjects.map (·.symbol)).Nodup) do throw "multiple definitions of an ordinary global"
    let arithmetic := match frontends, units with
      | [text], [unit] => (closed_tree text.length unit.tree).toOption
      | _, _ => none
    let functions := exports.map (·.symbol) ++ (units.flatMap (fun unit => unit.labels.map Prod.snd)).mergeSort ++
      ["pthread_create", "pthread_join", "pthread_self"]
    unless functions.length ≤ 2 ^ 63 do throw "ordinary linked symbols exceed the code space"
    let bodies ← (units.zip byUnit).mapM fun (unit, definitions) => do
      let globals ← ordinary_global_scope unit allObjects definitions
      let symbols := ordinary_imports unit exports functions
      let initialisers ← definitions.mapM fun object =>
        let visible := globals.filter fun other => other.owner.isNone || other.owner == object.owner
        ordinary_initialiser unit functions symbols visible (unit.budget + 1) object
      let procedures ← ordinary_procedures arithmetic unit.records symbols globals unit.namespaceName
        unit.labels (unit.budget + 1) (globals.flatMap (·.identities)).length 0 unit.declarations
      pure (⟨unit.namespaceName, procedures, initialisers, unit.labels.map Prod.snd⟩ : Ordinary.UnitBody)
    let startup ← link_startup (units.map fun unit => (unit.budget + 1, unit.tree))
    let program : Ordinary.Program := ⟨bodies, startup.parallel⟩
    if valid : program.procedures.map (·.name) = (link_entries trees).map Prod.fst ∧
        (program.procedures.map (·.name)).Nodup ∧ (program.globals.map (·.name)).Nodup then
      if control : program.procedures.all Ordinary.Procedure.control_checked = true then
        if layout : program.globals.all Ordinary.Global.initialisers_fit = true then
          if labels : program.labels_checked = true then
            return ⟨program, ⟨trees, rfl, valid.1, valid.2.1, valid.2.2, control, layout, labels⟩⟩
          else throw "ordinary computed jump lacks a registered label"
        else throw "ordinary initialiser spans overlap or exceed the object"
      else throw "ordinary function may fall through without a return or escape a loop"
    else throw "ordinary definitions differ from the checked link schedule"

private def ordinary_source (frontends : List String) : Except String Ordinary.Program :=
  Subtype.val <$> ordinary_link frontends

theorem ordinary_link_order (frontends : List String) (program : Ordinary.Program)
    (accepted : ordinary_source frontends = .ok program) :
    ∃ trees, frontends.mapM Json.parse = .ok trees ∧
      program.procedures.map (·.name) = (link_entries trees).map Prod.fst ∧
      (program.procedures.map (·.name)).Nodup ∧ (program.globals.map (·.name)).Nodup ∧
      program.procedures.all Ordinary.Procedure.control_checked = true ∧
      program.globals.all Ordinary.Global.initialisers_fit = true ∧ program.labels_checked = true := by
  unfold ordinary_source at accepted
  cases found : ordinary_link frontends with
  | error why => simp [found, Functor.map, Except.map] at accepted
  | ok linked =>
    simp [found, Functor.map, Except.map] at accepted
    subst program
    exact linked.property


private def ordinary_token (c : Char) : Bool := c.toNat < 128 && (c.isAlphanum || c == '_' || c == '\'')

private def ordinary_location (c : Char) : Bool :=
  c.toNat < 128 && (c.isAlphanum || ['.', '/', ':', '_', '-', ' ', '@'].contains c)

private def ordinary_locations (body : String) : Except String String :=
  let rec quoted : List Char → List Char → Except String (String × List Char)
    | '"' :: rest, value => .ok (String.mk ('"' :: ('"' :: value).reverse), rest)
    | '\\' :: c :: rest, value =>
      if c == '\n' || c == '\r' then .error "newline in ordinary string"
      else quoted rest (c :: '\\' :: value)
    | '\n' :: _, _ | '\r' :: _, _ | [], _ => .error "unterminated ordinary string"
    | c :: rest, value => quoted rest (c :: value)
  let rec scan : Nat → List Char → List String → Except String String
    | _, [], output => .ok (String.join output.reverse)
    | 0, _, _ => .error "ordinary token budget exhausted"
    | fuel + 1, chars@(head :: tail), output =>
      if ordinary_token head then
        let token := String.mk (chars.takeWhile ordinary_token)
        let remaining := chars.drop token.length
        if token == "at" || token == "atFlow" then
          match remaining with
          | ' ' :: '"' :: quoted =>
            let location := quoted.takeWhile ordinary_location
            match quoted.drop location.length with
            | '"' :: suffix => scan fuel suffix ((token ++ " \"@\"") :: output)
            | _ => .error "invalid ordinary location literal"
          | _ => .error "missing ordinary location literal"
        else scan fuel remaining (token :: output)
      else if head == '"' then do
        let (value, suffix) ← quoted tail []
        scan fuel suffix (value :: output)
      else scan fuel tail (String.singleton head :: output)
  scan (body.length + 1) body.toList []

opaque ordinary_runtime : String := include_str "../runtime/Heap.hs"

private def ordinary_runtime_checks (runtime generated : String) : Bool :=
  runtime == ordinary_runtime && (validates_access generated && validates_pointer_arithmetic generated &&
    validates_release generated && validates_allocation generated && validates_copy generated &&
    validates_scalar_memory generated && validates_pointer_memory generated &&
    validates_process generated && validates_dispatch_runtime generated && validates_link_runtime generated)

def validate_ordinary (runtime : String) (frontends : List String) (generated : String) : Except String Ordinary.Program := do
  let parsed ← ordinary_source frontends
  let bound ← bind_runtime runtime generated
  let normalised ← ordinary_locations bound.val
  unless normalised == parsed.moduleBody do
    throw "ordinary generated body differs from the typed lowering"
  unless ordinary_runtime_checks runtime generated do
    throw "ordinary runtime differs from the pinned implementation or its checked equations"
  return parsed

theorem ordinary_certificate_sound (runtime : String) (frontends : List String) (generated : String) (program : Ordinary.Program)
    (accepted : validate_ordinary runtime frontends generated = .ok program) :
    ordinary_source frontends = .ok program ∧ ordinary_runtime_checks runtime generated = true ∧
      (∃ prelude body, standalone_runtime runtime = .ok prelude ∧ generated = prelude ++ "\n" ++ body ∧
        ordinary_locations body = .ok program.moduleBody) ∧
      (∀ depth invocation, program.target depth invocation = (program.source depth invocation).emit .finish) := by
  unfold validate_ordinary at accepted
  cases read : ordinary_source frontends with
  | error why => simp [read, bind, Except.bind] at accepted
  | ok decoded =>
    cases matched : bind_runtime runtime generated with
    | error why => simp [read, matched, bind, Except.bind] at accepted
    | ok binding =>
      cases normal : ordinary_locations binding.val with
      | error why => simp [read, matched, normal, bind, Except.bind] at accepted
      | ok body =>
        by_cases same : body == decoded.moduleBody
        · by_cases checked : ordinary_runtime_checks runtime generated
          · simp only [read, matched, normal, bind, Except.bind, same, checked, if_true, pure, Except.pure,
              Except.ok.injEq] at accepted
            subst program
            obtain ⟨prefixText, prefixOk, exactText⟩ := binding.property
            exact ⟨rfl, checked, ⟨prefixText, binding.val, prefixOk, exactText, beq_iff_eq.mp same ▸ normal⟩,
              Ordinary.lower_program_correct decoded⟩
          · simp [read, matched, normal, bind, Except.bind, same, checked, pure, Except.pure] at accepted
        · simp [read, matched, normal, bind, Except.bind, same] at accepted

theorem ordinary_observation_sound (runtime : String) (frontends : List String) (generated : String) (program : Ordinary.Program)
    (accepted : validate_ordinary runtime frontends generated = .ok program) (fuel : Nat) (terminal : Bool)
    (invocation : Ordinary.Invocation := {}) :
    ordinary_source frontends = .ok program ∧
      program.observation fuel terminal invocation = program.source_observation fuel terminal invocation := by
  refine ⟨(ordinary_certificate_sound runtime frontends generated program accepted).1, ?_⟩
  exact Ordinary.prefix_refines program terminal fuel invocation ⟨[], ⟨1, 4096⟩, [], [], { events := invocation.files }⟩ ⟨[], [], 0, true⟩ rfl id (by intro a b eq; exact eq)

theorem ordinary_completed_behaviour (runtime : String) (frontends : List String) (generated : String)
    (program : Ordinary.Program) (accepted : validate_ordinary runtime frontends generated = .ok program)
    (invocation : Ordinary.Invocation) (terminal : Bool) (result : TraceOutcome × List UInt8) :
    Ordinary.Observes (fun fuel => program.observation fuel terminal invocation) result ↔
      Ordinary.Observes (fun fuel => program.source_observation fuel terminal invocation) result := by
  have agrees (fuel : Nat) := (ordinary_observation_sound runtime frontends generated program accepted fuel terminal invocation).2
  unfold Ordinary.Observes
  simp only [agrees]

def process_status : TraceOutcome → Option Nat
  | .returned code => some code.toNat
  | .fault _ => some 70
  | .paused => none

theorem ordinary_scheduled_behaviour (accepted : validate_ordinary runtime frontends generated = .ok program)
    (context : ThreadCode α → ScheduleState α HeapImage StdoutBuffer)
    (blocks : Nat → Option (ThreadCode α)) (schedule : List Nat) (terminal : Bool)
    (depth : Nat) (invocation : Ordinary.Invocation) (reference : Nat → Nat)
    (distinct : Function.Injective reference)
    (valid : ∀ code, (context code).stdout.size = (context code).stdout.snapshot.pending.length) :
    ordinary_source frontends = .ok program ∧
      (run_schedule (sparse_machine reference) terminal blocks schedule
        (context (.fromTrace (program.target depth invocation)))).snapshot reference =
      run_schedule abstract_machine terminal blocks schedule
        ((context (.fromTrace ((program.source depth invocation).emit .finish))).snapshot reference) :=
  ⟨(ordinary_certificate_sound _ _ _ _ accepted).1,
    scheduled_lowering _ _ _ _ _ _ _ reference distinct valid⟩

def matches_observation (program : Ordinary.Program) (budget : Nat) (invocation : Ordinary.Invocation)
    (status : Nat) (stdout : List UInt8) : Bool :=
  let (outcome, visible) := program.observation budget false invocation
  process_status outcome == some status && stdout == visible

theorem checked_process_observation (accepted : validate_ordinary runtime frontends generated = .ok program)
    (checked : matches_observation program budget invocation status stdout = true) :
    ∃ outcome, process_status outcome = some status ∧
      Ordinary.Observes (fun fuel => program.source_observation fuel false invocation) (outcome, stdout) ∧
      ∀ other, Ordinary.Observes (fun fuel => program.source_observation fuel false invocation) other →
        other = (outcome, stdout) := by
  rcases ran : program.observation budget false invocation with ⟨actual, bytes⟩
  simp only [matches_observation, ran, Bool.and_eq_true, beq_iff_eq] at checked
  obtain ⟨status_eq, rfl⟩ := checked
  have done_ : actual ≠ .paused := by rintro rfl; contradiction
  have target : Ordinary.Observes (fun fuel => program.observation fuel false invocation) (actual, stdout) :=
    ⟨done_, budget, ran⟩
  have agrees := ordinary_completed_behaviour _ _ _ _ accepted invocation false
  exact ⟨actual, status_eq, (agrees _).mp target, fun other observed =>
    Ordinary.completed_observations_unique _ _ _ _ _ ((agrees other).mpr observed) target⟩

def invocation_observation (program : Ordinary.Program) (budget : Nat) (invocation : Ordinary.Invocation)
    (witness : Option (List Nat) := none) : TraceOutcome × List UInt8 :=
  if program.parallel then
    program.threadObservation budget false invocation (witness.getD (program.threadSchedule budget false invocation))
  else program.observation budget false invocation

def matches_invocation (program : Ordinary.Program) (budget : Nat) (invocation : Ordinary.Invocation)
    (status : Nat) (stdout : List UInt8) (witness : Option (List Nat) := none) :=
  let (result, bytes) := invocation_observation program budget invocation witness
  process_status result == some status && bytes == stdout

theorem checked_thread_invocation (accepted : validate_ordinary runtime frontends generated = .ok program)
    (parallel : program.parallel = true) (checked : matches_invocation program budget invocation status stdout witness = true) :
    ordinary_source frontends = .ok program ∧ ∃ schedule result, process_status result = some status ∧
      program.sourceThreadObservation budget false invocation schedule = (result, stdout) := by
  let schedule := witness.getD (program.threadSchedule budget false invocation)
  rcases ran : program.threadObservation budget false invocation schedule with ⟨result, bytes⟩
  simp only [matches_invocation, invocation_observation, parallel, if_true] at checked
  change (process_status (program.threadObservation budget false invocation schedule).1 == some status &&
    (program.threadObservation budget false invocation schedule).2 == stdout) = true at checked
  rw [ran] at checked
  simp only [Bool.and_eq_true, beq_iff_eq] at checked
  obtain ⟨statusEq, bytesEq⟩ := checked
  exact ⟨(ordinary_certificate_sound _ _ _ _ accepted).1, schedule, result, statusEq,
    by rw [← thread_observation_correct, ran, bytesEq]⟩

def Ordinary.Program.sourceBehaviour (program : Ordinary.Program) (invocation : Ordinary.Invocation)
    (terminal : Bool) (result : TraceOutcome × List UInt8) : Prop :=
  if program.parallel then result.1 ≠ .paused ∧ ∃ depth schedule,
    program.sourceThreadObservation depth terminal invocation schedule = result
  else Ordinary.Observes (fun fuel => program.source_observation fuel terminal invocation) result

def Ordinary.Program.targetBehaviour (program : Ordinary.Program) (invocation : Ordinary.Invocation)
    (terminal : Bool) (result : TraceOutcome × List UInt8) : Prop :=
  if program.parallel then result.1 ≠ .paused ∧ ∃ depth schedule,
    program.threadObservation depth terminal invocation schedule = result
  else Ordinary.Observes (fun fuel => program.observation fuel terminal invocation) result

theorem certified_behaviours (accepted : validate_ordinary runtime frontends generated = .ok program)
    (invocation : Ordinary.Invocation) (terminal : Bool) (result : TraceOutcome × List UInt8) :
    program.targetBehaviour invocation terminal result ↔ program.sourceBehaviour invocation terminal result := by
  cases mode : program.parallel with
  | true => simp only [Ordinary.Program.targetBehaviour, Ordinary.Program.sourceBehaviour, mode, if_true,
      thread_observation_correct]
  | false => exact (by simpa only [Ordinary.Program.targetBehaviour, Ordinary.Program.sourceBehaviour, mode,
      Bool.false_eq_true, if_false] using ordinary_completed_behaviour _ _ _ _ accepted invocation terminal result)

theorem distinct_native_results_preclude_adequacy
    (accepted : validate_ordinary runtime frontends generated = .ok program)
    (sequential : program.parallel = false) (invocation : Ordinary.Invocation) (terminal : Bool)
    (native : TraceOutcome × List UInt8 → Prop) (left : native first) (right : native second)
    (different : first ≠ second) :
    ¬ (∀ result, native result ↔ program.sourceBehaviour invocation terminal result) := by
  intro adequate
  have observed result (possible : native result) :=
    (certified_behaviours accepted invocation terminal result).mpr ((adequate result).mp possible)
  have a := observed first left
  have b := observed second right
  simp only [Ordinary.Program.targetBehaviour, sequential, Bool.false_eq_true, if_false] at a b
  exact different (Ordinary.completed_observations_unique program terminal invocation first second a b)

theorem ordinary_executable_behaviour (input : Input) (artifact : Executable) (runtime : String)
    (frontends : List String) (generated : String) (program : Ordinary.Program)
    (frontend : Input → Except String (List String)) (ghc : String → Except String Executable)
    (native_observes : Input → Ordinary.Invocation → Bool → TraceOutcome × List UInt8 → Prop)
    (executable_observes : Executable → Ordinary.Invocation → Bool → TraceOutcome × List UInt8 → Prop)
    (dumped : frontend input = .ok frontends) (built : ghc generated = .ok artifact)
    (accepted : validate_ordinary runtime frontends generated = .ok program)
    (frontend_adequate : frontend input = .ok frontends → ordinary_source frontends = .ok program →
      ∀ invocation terminal result, native_observes input invocation terminal result ↔
        program.sourceBehaviour invocation terminal result)
    (ghc_adequate : ∀ prelude body, standalone_runtime runtime = .ok prelude → runtime = ordinary_runtime →
      generated = prelude ++ "\n" ++ body → ordinary_locations body = .ok program.moduleBody → ghc generated = .ok artifact →
      ∀ invocation terminal result, executable_observes artifact invocation terminal result ↔
        program.targetBehaviour invocation terminal result) :
    ∀ invocation terminal result, executable_observes artifact invocation terminal result ↔
      native_observes input invocation terminal result := by
  obtain ⟨decoded, checks, ⟨prelude, body, runtimeOk, exactBody, normal⟩, _⟩ :=
    ordinary_certificate_sound runtime frontends generated program accepted
  have pinned : runtime = ordinary_runtime := by
    unfold ordinary_runtime_checks at checks
    simp only [Bool.and_eq_true] at checks
    exact beq_iff_eq.mp checks.1
  intro invocation terminal result
  exact (ghc_adequate prelude body runtimeOk pinned exactBody normal built invocation terminal result).trans
    ((certified_behaviours accepted invocation terminal result).trans
      (frontend_adequate dumped decoded invocation terminal result).symm)

theorem ordinary_registered_call (runtime : String) (frontends : List String) (generated : String)
    (program : Ordinary.Program) (accepted : validate_ordinary runtime frontends generated = .ok program)
    (procedure : Ordinary.Procedure) (registered : procedure ∈ program.procedures) :
    program.lookup procedure.name = some procedure := by
  obtain ⟨_, _, _, unique, _, _, _, _⟩ := ordinary_link_order frontends program
    (ordinary_certificate_sound runtime frontends generated program accepted).1
  exact Ordinary.lookup_registered program procedure unique registered

theorem ordinary_procedure_control (runtime : String) (frontends : List String) (generated : String)
    (program : Ordinary.Program) (accepted : validate_ordinary runtime frontends generated = .ok program)
    (procedure : Ordinary.Procedure) (registered : procedure ∈ program.procedures) :
    procedure.control_checked = true := by
  obtain ⟨_, _, _, _, _, control, _, _⟩ := ordinary_link_order frontends program
    (ordinary_certificate_sound runtime frontends generated program accepted).1
  exact List.all_eq_true.mp control procedure registered

theorem ordinary_global_initialiser_in_bounds (runtime : String) (frontends : List String) (generated : String)
    (program : Ordinary.Program) (accepted : validate_ordinary runtime frontends generated = .ok program)
    (object : Ordinary.Global) (allocated : object ∈ program.globals)
    (init : Ordinary.Initialiser) (present : init ∈ object.initialisers) :
    init.offsets.sum + init.ty.width ≤ object.width := by
  obtain ⟨_, _, _, _, _, _, stores, _⟩ := ordinary_link_order frontends program
    (ordinary_certificate_sound runtime frontends generated program accepted).1
  exact object.initialiser_in_bounds (List.all_eq_true.mp stores object allocated) init present

theorem ordinary_computed_labels_checked (runtime : String) (frontends : List String) (generated : String)
    (program : Ordinary.Program) (accepted : validate_ordinary runtime frontends generated = .ok program) :
    program.labels_checked = true := by
  obtain ⟨_, _, _, _, _, _, _, labels⟩ := ordinary_link_order frontends program
    (ordinary_certificate_sound runtime frontends generated program accepted).1
  exact labels

inductive SharedExpression where
  | literal (value : Nat)
  | call (name : String)
  | choose (common fallback : SharedExpression)

def SharedExpression.source (call : String → σ → Except ε Int × σ) :
    SharedExpression → σ → Except ε Int × σ
  | .literal n, state => (.ok n, state)
  | .call name, state => call name state
  | .choose common fallback, state =>
    match common.source call state with
    | (.error why, next) => (.error why, next)
    | (.ok n, next) => if n = 0 then fallback.source call next else (.ok n, next)

def SharedExpression.target (call : String → σ → Except ε Int × σ) :
    SharedExpression → σ → Except ε Int × σ
  | .literal n => fun state => (.ok n, state)
  | .call name => call name
  | .choose common fallback => bind_action (common.target call) fun shared =>
      branch_action (fun state => (.ok (shared != 0), state))
        (fun state => (.ok shared, state)) (fallback.target call)

theorem shared_expression_correct (expr : SharedExpression) (call : String → σ → Except ε Int × σ) :
    expr.target call = expr.source call := by
  induction expr with
  | literal n => rfl
  | call name => rfl
  | choose common fallback left right =>
    funext state
    simp only [SharedExpression.target, SharedExpression.source, left, right, branch_action, bind_action]
    obtain ⟨result, next⟩ := common.source call state
    cases result with
    | error why => rfl
    | ok n => by_cases zero : n = 0 <;> simp [zero]

private def SharedExpression.haskell : SharedExpression → String
  | .literal n => "pure (Number (" ++ toString n ++ "))"
  | .call name => "invoke (Just (IntegerType 32 True)) (function " ++ haskell_quote name ++ ") []"
  | .choose common fallback => "conditional (" ++ common.haskell ++
      ") (\\shared -> pure shared) (\\shared -> pure shared) (" ++ fallback.haskell ++ ")"

private def read_shared : Nat → Json → Except String SharedExpression
  | 0, _ => .error "incomplete shared expression"
  | depth + 1, node => do
    unless type_spelling node == "int" do throw "expected an int expression"
    match field_text node "kind", child_nodes node with
    | "ParenExpr", [child] => read_shared depth child
    | "IntegerLiteral", [] =>
      let n ← require (field_text node "value").toNat? "invalid integer literal"
      unless n < 2147483648 do throw "integer literal exceeds int"
      pure (.literal n)
    | "CallExpr", [callee] =>
      let name := direct_callee depth callee
      if name.isEmpty then throw "expected a direct call" else pure (.call name)
    | "BinaryConditionalOperator", [common, test, reused, fallback] =>
      unless refers_to_common common test && refers_to_common common reused &&
          field_text test "id" != "" && field_text test "id" == field_text reused "id" do
        throw "conditional operands differ from the shared value"
      return .choose (← read_shared depth common) (← read_shared depth fallback)
    | _, _ => throw "unsupported shared expression"

private def location_rest : List Char → Option (List Char)
  | '"' :: rest => some rest
  | '\\' :: _ :: rest => location_rest rest
  | '\\' :: [] | [] => none
  | _ :: rest => location_rest rest

private def skip_location (head line : String) : Option String := do
  guard (line.startsWith (head ++ "\""))
  return String.mk (← location_rest (line.drop (head.length + 1)).toList)

private def shared_body (name line : String) : Option String := do
  let after ← skip_location (hex_binding "f" name ++ " _ = at ") line
  let block ← skip_location " (marshal (IntegerType 32 True) <$> (frame (do { atFlow " after
  let statement ← skip_location " (chain [(atFlow " block
  let start := " (Return <$> ("
  let stop := ")))]) })))"
  guard (statement.startsWith start && statement.endsWith stop)
  return (statement.drop start.length).take (statement.length - start.length - stop.length)

def checked_shared_body (name line : String) (expr : SharedExpression) : Bool :=
  shared_body name line == some expr.haskell

theorem checked_shared_body_correct (name line : String) (expr : SharedExpression)
    (checked : checked_shared_body name line expr = true) (call : String → σ → Except ε Int × σ) :
    shared_body name line = some expr.haskell ∧ expr.target call = expr.source call := by
  exact ⟨beq_iff_eq.mp checked, shared_expression_correct expr call⟩

private def shared_source (name frontend : String) : Except String SharedExpression := do
  let tree ← Json.parse frontend
  let [fn] := (function_definitions (unit_function_declarations tree)).filter (fun n => field_text n "name" == name)
    | throw "expected one named function definition"
  unless type_spelling fn == "int (void)" && field_text fn "storageClass" != "static" do
    throw "expected an external int (void) definition"
  let [block] := child_nodes fn | throw "expected one function body"
  let [ret] := child_nodes block | throw "expected a single return"
  let [body] := child_nodes ret | throw "expected a return value"
  unless field_text ret "kind" == "ReturnStmt" do throw "expected a return"
  let expr ← read_shared (frontend.utf8ByteSize + 1) body
  let .choose .. := expr | throw "expected a shared conditional"
  return expr

def validate_shared (name frontend generated : String) : Except String Unit :=
  match shared_source name frontend with
  | .error why => .error why
  | .ok expr =>
    let binding := hex_binding "f" name
    match (generated.splitOn "\n").filter (·.startsWith (binding ++ " ")) with
    | [signature, equation] =>
      if signature == binding ++ " :: [Value] -> R Value" && checked_shared_body name equation expr &&
          validates_dispatch_runtime generated then .ok ()
      else .error "generated shared conditional differs from the typed function"
    | _ => .error "missing or ambiguous generated definition"

theorem shared_certificate_sound (name frontend generated : String)
    (accepted : validate_shared name frontend generated = .ok ()) (call : String → σ → Except ε Int × σ) :
    ∃ expr equation, shared_source name frontend = .ok expr ∧ equation ∈ generated.splitOn "\n" ∧
      shared_body name equation = some expr.haskell ∧ expr.target call = expr.source call := by
  unfold validate_shared at accepted
  split at accepted
  next => contradiction
  next expr parsed =>
    dsimp only at accepted
    split at accepted
    next signature equation rows =>
      split at accepted
      next checked =>
        have present : equation ∈ (generated.splitOn "\n").filter (·.startsWith (hex_binding "f" name ++ " ")) := by
          rw [rows]
          simp
        simp only [Bool.and_eq_true] at checked
        exact ⟨expr, equation, parsed, (List.mem_filter.mp present).1,
          checked_shared_body_correct name equation expr checked.1.2 call⟩
      next => contradiction
    next => contradiction

end Heresy

#print axioms Heresy.shared_certificate_sound
#print axioms Heresy.module_runtime_bound
#print axioms Heresy.ordinary_certificate_sound
#print axioms Heresy.ordinary_link_order
#print axioms Heresy.ordinary_registered_call
#print axioms Heresy.ordinary_procedure_control
#print axioms Heresy.ordinary_global_initialiser_in_bounds
#print axioms Heresy.ordinary_computed_labels_checked
#print axioms Heresy.ordinary_observation_sound
#print axioms Heresy.ordinary_executable_behaviour
#print axioms Heresy.checked_thread_invocation
#print axioms Heresy.checked_process_observation
#print axioms Heresy.ordinary_scheduled_behaviour

#print axioms Heresy.kernel_certificate_sound
#print axioms Heresy.kernel_return_preserves_result
#print axioms Heresy.checked_kernel_entry_equation
#print axioms Heresy.checked_dispatch_counts
#print axioms Heresy.program_certificate_sound
#print axioms Heresy.framed_program_certificate_sound
#print axioms Heresy.closed_executable_exit_refines
#print axioms Heresy.closed_text_executable_exit
#print axioms Heresy.closed_native_haskell_agree
#print axioms Heresy.compile_closed_text_sound
#print axioms Heresy.certified_helper_uses_bound_arguments
#print axioms Heresy.link_schedule_order
#print axioms Heresy.linkage_certificate_routes
#print axioms Heresy.certified_definition_authentication
#print axioms Heresy.linkage_certificate_line
#print axioms Heresy.linkage_validation_sound

run_cmd
  let env ← getEnv
  let mut checked := 0
  let mut dependencies : CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    unless (`Heresy).isPrefixOf ((privateToUserName? name).getD name) do continue
    unless getOriginalConstKind? env name matches some .thm | some .axiom do continue
    checked := checked + 1
    dependencies := (((CollectAxioms.collect name).run env).run dependencies).2
  if checked == 0 then throwError "no heresy theorems found"
  let extra := dependencies.axioms.filter fun name => ![``propext, ``Classical.choice, ``Quot.sound].contains name
  unless extra.isEmpty do throwError "unverified axioms in heresy proofs: {extra}"
  logInfo m!"checked {checked} declarations against the kernel axiom set"
