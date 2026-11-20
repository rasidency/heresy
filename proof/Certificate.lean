import Lean.Data.Json
import Semantics
import Synchronisation
import Runtime
import Ordinary
import Surface

set_option warningAsError true

open Lean

namespace Heresy

def operator_text : Operator → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .band => ".&."
  | .bor => ".|."
  | .bxor => "`xor`"

def render_expression (render_slot : Nat → String) (strict : Bool) : Target → String
  | .constant value => toString value
  | .parameter index => render_slot index
  | .binary operator left right =>
    let left := "(" ++ render_expression render_slot strict left ++ ")"
    let right := "(" ++ render_expression render_slot strict right ++ ")"
    let operator := operator_text operator
    if strict then "strictOperands (\\left right -> left " ++ operator ++ " right) " ++ left ++ " " ++ right
    else left ++ " " ++ operator ++ " " ++ right
  | .wrap width expression =>
    "normalise " ++ toString width ++ " False (" ++ render_expression render_slot strict expression ++ ")"
  | .conditional condition yes no =>
    "if (" ++ render_expression render_slot strict condition ++ ") == 0 then (" ++ render_expression render_slot strict no ++
      ") else (" ++ render_expression render_slot strict yes ++ ")"
  | .invoke slot arguments =>
    "(" ++ String.intercalate " " (("h_" ++ toString slot) ::
      arguments.map (fun value => "(" ++ render_expression render_slot strict value ++ ")")) ++ ")"

def render_target := render_expression (fun index => "x" ++ toString index) false

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

private def type_spelling (node : Json) : String :=
  let type := json_field node "type"
  let canonical := field_text type "desugaredQualType"
  if canonical.isEmpty then field_text type "qualType" else canonical

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

private def haskell_quote (name : String) : String :=
  "\"" ++ name.toUTF8.toList.foldl (fun result byte =>
    result ++ match byte.toNat with
      | 9 => "\\t"
      | 10 => "\\n"
      | 13 => "\\r"
      | 34 => "\\\""
      | 92 => "\\\\"
      | n => if 32 ≤ n && n ≤ 126 then String.singleton (Char.ofNat n) else "\\" ++ toString n ++ "\\&") "" ++ "\""

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
    "      initial = World counter [] S.empty S.empty (S.fromList entries) codes \"startup\" 0 [] False False table (terminal, output) gate threads owner nullPointer initThread",
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

def closed_source (frontend : String) : Except String ClosedProgram := do
  let tree ← Json.parse frontend
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
  let (ordered, recursive) ← order_helpers (definitions.filter (fun node => field_text node "name" != "main")) frontend.length
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
    let (code, _) ← read_command (fun callee => List.lookup callee scope) false frontend.length identifiers.zipIdx arity block
    helpers := ⟨arity, code⟩ :: helpers
    linked := (name, (slot, arity)) :: linked
  let (entry, _) ← read_command (fun name => List.lookup name linked) true frontend.length [] 0 body
  if framed then pure (.framed helpers.reverse entry)
  else
    let direct ← helpers.reverse.mapM fun helper => match helper.body with
      | .result value => pure ⟨helper.arity, value⟩
      | _ => throw "closed helper requires one return statement"
    pure (.direct direct entry)

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

private def validates_aggregate_memory (generated : String) : Bool :=
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

private def validates_atomic_memory (generated : String) : Bool :=
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

private def validates_pointer_memory (generated : String) : Bool :=
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

private inductive OrdinaryStorage where
  | scalar (ty : Ordinary.TypeCode)
  | array (element : String) (ty : Ordinary.TypeCode) (count : Nat)
  | record (layout : Ordinary.RecordLayout)

private def OrdinaryStorage.width : OrdinaryStorage → Nat
  | .scalar ty => ty.width
  | .array _ ty count => count * ty.width
  | .record layout => layout.width

private def OrdinaryStorage.scalar_type : OrdinaryStorage → Option Ordinary.TypeCode
  | .scalar ty => some ty
  | _ => none

private structure OrdinaryLocal where
  ident : String
  name : String
  spelling : String
  storage : OrdinaryStorage
  kind : String
  slot : Nat

private structure OrdinarySignature where
  name : String
  symbol : String
  spelling : String
  result : String
  ty : Ordinary.TypeCode
  parameters : List OrdinaryLocal
  declarations : List String
  entry : Json
  records : List Ordinary.RecordLayout

private structure OrdinaryUnit where
  namespaceName : String
  budget : Nat
  tree : Json
  declarations : List Json
  objects : List Json
  records : List Ordinary.RecordLayout
  labels : List (String × String)

private structure OrdinaryObject where
  name : String
  symbol : String
  spelling : String
  storage : OrdinaryStorage
  definition : Json
  identities : List String
  recordTarget : Option Ordinary.RecordLayout

private def ordinary_type : String → Option Ordinary.TypeCode
  | "unsigned char **" | "unsigned char *" | "char **" | "char *" | "signed char **" | "signed char *"
  | "int *" | "unsigned long *" | "void *" | "const void *" => some .pointer
  | "unsigned char" => some .byte
  | "char" | "signed char" => some .signedByte
  | "int" => some .integer
  | "unsigned int" => some .unsignedInt
  | "unsigned long" => some .size
  | spelling =>
    if (spelling.startsWith "struct " || spelling.startsWith "union ") && spelling.endsWith " *" then some .pointer else none

private def ordinary_pointee : String → String
  | "unsigned char **" => "unsigned char *"
  | "unsigned char *" => "unsigned char"
  | "char **" => "char *"
  | "char *" => "char"
  | "signed char **" => "signed char *"
  | "signed char *" => "signed char"
  | "int *" => "int"
  | "unsigned long *" => "unsigned long"
  | spelling =>
    if (spelling.startsWith "struct " || spelling.startsWith "union ") && spelling.endsWith " *" then
      spelling.take (spelling.length - 2) else ""

private def ordinary_array (spelling : String) : Option (String × Nat) := do
  let [element, bound] := spelling.splitOn "[" | none
  guard (bound.endsWith "]")
  let extent ← (bound.take (bound.length - 1)).toNat?
  guard (extent > 0)
  return (element.trim, extent)

private def ordinary_ident (node : Json) : String :=
  field_text (json_field node "referencedDecl") "id"

private def ordinary_name (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_'))

private def ordinary_record (node : Json) : Option Ordinary.RecordLayout := do
  let name := field_text node "name"
  let tag := field_text node "tagUsed"
  let named := ordinary_name name || (name.startsWith "@" && (name.drop 1).toNat?.isSome)
  guard (field_text node "kind" == "RecordDecl" && ["struct", "union"].contains tag &&
    json_field node "completeDefinition" == .bool true && named && !(child_nodes node).isEmpty)
  let fields ← (child_nodes node).mapM fun member => do
    let identity := field_text member "id"
    let name := field_text member "name"
    let spelling := type_spelling member
    let ty ← ordinary_type spelling
    guard (field_text member "kind" == "FieldDecl" && ordinary_name name && !identity.isEmpty)
    let bits ← if json_field member "isBitfield" == .bool true then do
      let [constant] := child_nodes member | none
      guard (field_text constant "kind" == "ConstantExpr" && ty != .pointer)
      let width ← (field_text constant "value").toNat?
      guard (0 < width && width ≤ 8 * ty.width)
      pure (some (width - 1))
    else do
      guard ((child_nodes member).isEmpty)
      pure none
    pure (⟨identity, name, spelling, ty, bits⟩ : Ordinary.FieldSpec)
  guard (decide ((fields.map (·.identity)).Nodup) && decide ((fields.map (·.name)).Nodup))
  let spelling := tag ++ " " ++ name
  return if tag == "union" then Ordinary.union_layout spelling fields
    else if fields.any (·.bits.isSome) then Ordinary.bit_record_layout spelling fields
    else Ordinary.record_layout spelling fields

private def ordinary_storage (records : List Ordinary.RecordLayout) (spelling : String) : Option OrdinaryStorage :=
  if let some (element, count) := ordinary_array spelling then do
    return .array element (← ordinary_type element) count
  else if let some ty := ordinary_type spelling then some (.scalar ty)
  else (records.find? (·.spelling == spelling)).map .record

private def ordinary_record_compatible (left right : Ordinary.RecordLayout) : Bool :=
  let fields := fun (layout : Ordinary.RecordLayout) =>
    layout.fields.map (fun field => (field.spec.name, field.spec.spelling, field.offset, field.shift, field.spec.bits))
  left.isUnion == right.isUnion && left.width == right.width && left.alignment == right.alignment && fields left == fields right

private def ordinary_record_pointer_compatible (left right : List Ordinary.RecordLayout) (type : String) : Bool :=
  let spelling := ordinary_pointee type
  if !(spelling.startsWith "struct " || spelling.startsWith "union ") then true else
    match left.find? (·.spelling == spelling), right.find? (·.spelling == spelling) with
    | none, none => true
    | some first, some other => ordinary_record_compatible first other
    | _, _ => false

private def ordinary_decl (node : Json) (spelling : String) : Bool :=
  !spelling.isEmpty && type_spelling node == spelling

private def ordinary_member (records : List Ordinary.RecordLayout) (node base : Json) : Except String Ordinary.Field := do
  let indirect := json_field node "isArrow" == .bool true
  let recordType := if indirect then ordinary_pointee (type_spelling base) else type_spelling base
  let layout ← require (records.find? (·.spelling == recordType)) "unsupported ordinary record member base"
  let identity := field_text node "referencedMemberDecl"
  let member ← require (layout.fields.find? (·.spec.identity == identity)) "unknown ordinary record member identity"
  unless ordinary_decl node member.spec.spelling && field_text node "name" == member.spec.name &&
      (indirect || field_text base "valueCategory" == "lvalue") do throw "ordinary record member type changed"
  return member

private def ordinary_lvalue_field (records : List Ordinary.RecordLayout) : Nat → Json → Except String (Option Ordinary.Field)
  | 0, _ => .error "ordinary member nesting exceeds the frontend budget"
  | fuel + 1, node =>
    match field_text node "kind", child_nodes node with
    | "MemberExpr", [base] => some <$> ordinary_member records node base
    | "ParenExpr", [child] => ordinary_lvalue_field records fuel child
    | _, _ => .ok none

private def ordinary_access (records : List Ordinary.RecordLayout) (budget : Nat) (node : Json)
    (scalar : Ordinary.TypeCode) : Except String Ordinary.TypeCode := do
  let member ← ordinary_lvalue_field records budget node
  return (member.map (·.access)).getD scalar

private def ordinary_reference_type (node : Json) (spelling : String) : Bool :=
  ordinary_decl node spelling || ["struct ", "union "].any (fun tag =>
    (spelling.splitOn (tag ++ "@")).length > 1 && ((type_spelling node).splitOn tag).length > 1)

private def ordinary_slot (scope : List OrdinaryLocal) (node : Json) : Except String Nat := do
  let ref := json_field node "referencedDecl"
  let ident := ordinary_ident node
  let binding ← require (scope.find? (fun binding => binding.ident == ident)) "unknown ordinary local reference"
  unless field_text ref "kind" == binding.kind && field_text ref "name" == binding.name &&
      ordinary_reference_type ref binding.spelling && type_spelling node == binding.spelling do
    throw "ordinary local reference type or name changed"
  return binding.slot

private def ordinary_address (globals : List OrdinaryObject) (scope : List OrdinaryLocal) (node : Json) :
    Except String Ordinary.Expression := do
  let ident := ordinary_ident node
  if scope.any (fun binding => binding.ident == ident) then
    return .slotAddress (← ordinary_slot scope node)
  let object ← require (globals.find? fun object => object.identities.contains ident)
    "unknown ordinary object reference"
  let reference := json_field node "referencedDecl"
  unless field_text reference "kind" == "VarDecl" && field_text reference "name" == object.name &&
      ordinary_reference_type reference object.spelling && ordinary_decl node object.spelling do
    throw "ordinary global reference type or name changed"
  return .globalAddress object.symbol

private def ordinary_callee (callee : Json) : Except String (String × String × String) := do
  let [reference] := child_nodes callee | throw "expected ordinary function decay"
  let declaration := json_field reference "referencedDecl"
  unless field_text callee "kind" == "ImplicitCastExpr" && field_text callee "castKind" == "FunctionToPointerDecay" &&
      field_text reference "kind" == "DeclRefExpr" && (child_nodes reference).isEmpty &&
      field_text declaration "kind" == "FunctionDecl" && field_text declaration "id" != "" &&
      ordinary_reference_type declaration (type_spelling reference) do
    throw "expected a named ordinary function"
  return (field_text declaration "name", type_spelling reference, field_text declaration "id")

private def ordinary_scalar : String → Option Ordinary.ScalarOp
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | "==" => some .eq
  | "!=" => some .ne
  | "<" => some .lt
  | "<=" => some .le
  | ">" => some .gt
  | ">=" => some .ge
  | _ => none

private def ordinary_comparison (op : String) : Bool :=
  ["==", "!=", "<", "<=", ">", ">="].contains op

private def ordinary_record_source (spelling : String) : Nat → Json → Except String Json
  | 0, _ => .error "incomplete ordinary record expression"
  | depth + 1, node => do
    unless ordinary_decl node spelling do throw "ordinary record copy changed type"
    match field_text node "kind", child_nodes node with
    | "ParenExpr", [child] => ordinary_record_source spelling depth child
    | "ImplicitCastExpr", [place] =>
      unless field_text node "castKind" == "LValueToRValue" && ordinary_decl place spelling do
        throw "ordinary record copy requires a matching source lvalue"
      return place
    | _, _ => throw "ordinary record copy requires a source lvalue"

private def ordinary_zero : Nat → Json → Bool
  | 0, _ => false
  | depth + 1, node =>
    match field_text node "kind", child_nodes node with
    | "IntegerLiteral", [] => field_text node "value" == "0"
    | "ParenExpr", [child] | "ConstantExpr", [child] => ordinary_zero depth child
    | _, _ => false

private def ordinary_expr (records : List Ordinary.RecordLayout) (symbols : List OrdinarySignature) (globals : List OrdinaryObject)
    (scope : List OrdinaryLocal) : Nat → Bool → Json → Except String Ordinary.Expression
  | 0, _, _ => .error "incomplete ordinary expression"
  | depth + 1, place, node => do
    let descend := ordinary_expr records symbols globals scope depth
    let spelling := type_spelling node
    let kind := field_text node "kind"
    let children := child_nodes node
    if place then
      match kind, children with
      | "DeclRefExpr", [] => ordinary_address globals scope node
      | "ParenExpr", [child] =>
        unless ordinary_decl child spelling do throw "parenthesised ordinary lvalue changed type"
        descend true child
      | "UnaryOperator", [operand] =>
        unless field_text node "opcode" == "*" && ordinary_decl node (ordinary_pointee (type_spelling operand)) do
          throw "unsupported ordinary dereference"
        descend false operand
      | "ArraySubscriptExpr", [base, index] =>
        let ty ← require (ordinary_type spelling) "unsupported ordinary array element type"
        unless ordinary_decl node (ordinary_pointee (type_spelling base)) &&
            ["int", "unsigned long"].contains (type_spelling index) do
          throw "unsupported ordinary array subscript"
        return .offset (← descend false base) (← descend false index) ty.width
      | "MemberExpr", [base] =>
        let indirect := json_field node "isArrow" == .bool true
        let member ← ordinary_member records node base
        return .field (← descend (!indirect) base) member.offset
      | _, _ => throw "unsupported ordinary lvalue"
    else
      match kind, children with
      | "IntegerLiteral", [] =>
        let n ← require (field_text node "value").toNat? "invalid ordinary literal"
        unless spelling == "int" && n < 2147483648 do throw "ordinary literal exceeds int"
        return .literal n
      | "CharacterLiteral", [] =>
        let n ← (json_field node "value").getNat?
        unless spelling == "int" && n < 2147483648 do throw "ordinary character exceeds int"
        return .literal n
      | "DeclRefExpr", [] =>
        let ty ← require (ordinary_type spelling) "unsupported ordinary local type"
        return .load ty (← ordinary_address globals scope node)
      | "ArraySubscriptExpr", [_, _] | "MemberExpr", [_] =>
        let ty ← require (ordinary_type spelling) "unsupported ordinary aggregate element type"
        return .load (← ordinary_access records (depth + 1) node ty) (← descend true node)
      | "ParenExpr", [child] =>
        unless ordinary_decl child spelling do throw "parenthesised ordinary expression changed type"
        descend false child
      | "ImplicitCastExpr", [child] | "CStyleCastExpr", [child] =>
        let ty ← require (ordinary_type spelling) "unsupported ordinary cast target"
        if kind == "ImplicitCastExpr" && field_text node "castKind" == "ArrayToPointerDecay" then
          let (element, _) ← require (ordinary_array (type_spelling child)) "ordinary array decay requires a fixed extent"
          unless ty == .pointer && element == ordinary_pointee spelling do
            throw "ordinary array decay changed the element type"
          descend true child
        else
          let inputType ← require (ordinary_type (type_spelling child)) "unsupported ordinary cast input"
          match field_text node "castKind" with
          | "NullToPointer" =>
            unless ty == .pointer && inputType != .pointer && ordinary_zero depth child do
              throw "ordinary null pointer requires an integer zero constant"
            return .nullPointer
          | "LValueToRValue" =>
            unless kind == "ImplicitCastExpr" && ordinary_decl child spelling do
              throw "unsupported ordinary load type"
            return .load (← ordinary_access records depth child ty) (← descend true child)
          | "BitCast" =>
            unless ty == .pointer && inputType == .pointer do throw "ordinary bitcast must preserve a data pointer"
            descend false child
          | "IntegralCast" =>
            unless ty != .pointer && inputType != .pointer do throw "ordinary integer cast has a pointer operand"
            return .cast ty (← descend false child)
          | "NoOp" =>
            unless ordinary_decl child spelling do throw "ordinary no-op cast changed type"
            descend false child
          | _ => throw "unsupported ordinary cast"
      | "UnaryOperator", [operand] =>
        if field_text node "opcode" == "&" then
          unless ordinary_decl operand (ordinary_pointee spelling) do throw "unsupported ordinary address type"
          let member ← ordinary_lvalue_field records depth operand
          unless !(member.any (·.spec.bits.isSome)) do throw "ordinary bitfields have no address"
          return ← descend true operand
        unless field_text node "opcode" == "!" && spelling == "int" &&
            (ordinary_type (type_spelling operand)).isSome do throw "unsupported ordinary unary expression"
        return .logicalNot (← descend false operand)
      | "BinaryOperator", [lhs, rhs] =>
        match field_text node "opcode" with
        | "+" =>
          if ordinary_type spelling == some .pointer then
            let element ← require (ordinary_type (ordinary_pointee spelling)) "unsupported ordinary pointer stride"
            unless ordinary_decl lhs spelling && ["int", "unsigned long"].contains (type_spelling rhs) do
              throw "ordinary pointer arithmetic requires a matching pointer and integer index"
            return .offset (← descend false lhs) (← descend false rhs) element.width
          else
            let ty ← require (ordinary_type spelling) "unsupported ordinary arithmetic width"
            unless [.integer, .unsignedInt, .size].contains ty && ordinary_decl lhs spelling && ordinary_decl rhs spelling do
              throw "unsupported ordinary addition types"
            return .scalar .add ty (← descend false lhs) (← descend false rhs)
        | "||" | "&&" =>
          unless spelling == "int" && (ordinary_type (type_spelling lhs)).isSome &&
              (ordinary_type (type_spelling rhs)).isSome do throw "invalid ordinary logical operands"
          return .logic (field_text node "opcode" == "&&") (← descend false lhs) (← descend false rhs)
        | "=" =>
          unless ordinary_decl lhs spelling && ordinary_decl rhs spelling do
            throw "ordinary assignment operand types differ"
          if let some layout := records.find? (·.spelling == spelling) then
            let source ← ordinary_record_source spelling depth rhs
            return .copyRecord (← descend true lhs) (← descend true source) layout.width layout.alignment
          else
            let ty ← require (ordinary_type spelling) "unsupported ordinary assignment type"
            return .assign (← ordinary_access records depth lhs ty) (← descend true lhs) (← descend false rhs)
        | opcode =>
          let op ← require (ordinary_scalar opcode) "unsupported ordinary binary expression"
          let operand := type_spelling lhs
          let ty ← require (ordinary_type operand) "unsupported ordinary arithmetic width"
          let result := if ordinary_comparison opcode then "int" else operand
          if ty == .pointer then
            unless ["==", "!="].contains opcode && ordinary_decl rhs operand && spelling == "int" do
              throw "ordinary pointer comparison requires matching pointer types"
            return .pointerCompare (opcode == "==") (← descend false lhs) (← descend false rhs)
          unless [.integer, .unsignedInt, .size].contains ty && ordinary_decl rhs operand && spelling == result do
            throw "unsupported ordinary scalar operand or result type"
          return .scalar op ty (← descend false lhs) (← descend false rhs)
      | "CallExpr", callee :: arguments =>
        let (name, signature, ident) ← ordinary_callee callee
        match name, signature, spelling, arguments with
        | "malloc", "void *(unsigned long)", "void *", [size] =>
          unless ordinary_decl size "unsigned long" do throw "invalid ordinary allocation size"
          return .allocate (← descend false size)
        | "memmove", "void *(void *, const void *, unsigned long)", "void *", [dst, src, size] =>
          unless ordinary_decl dst "void *" && ordinary_decl src "const void *" &&
              ordinary_decl size "unsigned long" do throw "invalid ordinary copy arguments"
          return .move (← descend false dst) (← descend false src) (← descend false size)
        | "putchar", "int (int)", "int", [value] =>
          unless ordinary_decl value "int" do throw "invalid ordinary output argument"
          return .put (← descend false value)
        | "free", "void (void *)", "void", [addr] =>
          unless ordinary_decl addr "void *" do throw "invalid ordinary release argument"
          return .release (← descend false addr)
        | "exit", "void (int) __attribute__((noreturn))", "void", [status] =>
          unless ordinary_decl status "int" do throw "invalid ordinary exit argument"
          return .exit (← descend false status)
        | _, _, _, _ =>
          let target ← require (symbols.find? fun target => target.name == name) "unresolved ordinary direct call"
          unless target.declarations.contains ident && signature == target.spelling && spelling == target.result &&
              arguments.length == target.parameters.length do throw "ordinary call signature or arity changed"
          let parsed ← (target.parameters.zip arguments).mapM fun (parameter, argument) => do
            unless ordinary_decl argument parameter.spelling do throw "ordinary call argument type changed"
            let ty ← require parameter.storage.scalar_type "unsupported ordinary parameter value type"
            return (ty, ← descend false argument)
          return .call target.symbol target.ty (parsed.foldr (fun (ty, expr) tail => .argument ty expr tail) .emptyArguments)
      | _, _ => throw "unsupported ordinary expression"

private def ordinary_read_only : Ordinary.Expression → Bool
  | .literal _ | .nullPointer | .slotAddress _ | .globalAddress _ | .emptyArguments => true
  | .load _ operand | .cast _ operand | .field operand _ | .logicalNot operand => ordinary_read_only operand
  | .offset left right _ | .logic _ left right | .pointerCompare _ left right | .scalar _ _ left right | .argument _ left right =>
    ordinary_read_only left && ordinary_read_only right
  | _ => false

private def ordinary_root_effect : Ordinary.Expression → Bool
  | .allocate size | .put size | .release size | .exit size | .call _ _ size => ordinary_read_only size
  | .assign _ place value => ordinary_read_only place && ordinary_read_only value
  | .copyRecord destination source _ _ => ordinary_read_only destination && ordinary_read_only source
  | .move dst src count => ordinary_read_only dst && ordinary_read_only src && ordinary_read_only count
  | expression => ordinary_read_only expression

private def ordinary_array_stores (element : String) (count : Nat) (ty : Ordinary.TypeCode)
    (initializer : Json) (parse : Json → Except String Ordinary.Expression) : Except String (List Ordinary.Initialiser) := do
  unless field_text initializer "kind" == "InitListExpr" do
    throw "ordinary array initialiser requires an initialiser list"
  let values := child_nodes initializer
  let values := if values.isEmpty then ((json_field initializer "array_filler").getArr?.toOption.getD #[]).toList.drop 1
    else values
  unless values.length ≤ count do
    throw "ordinary array initialiser extent does not match its elements"
  let stores ← values.zipIdx.mapM fun (node, index) => do
    unless ordinary_decl node element do throw "ordinary array initialiser element has the wrong type"
    if field_text node "kind" == "ImplicitValueInitExpr" then pure none
    else pure (some (⟨some (index * ty.width), ty, ← parse node⟩ : Ordinary.Initialiser))
  return stores.filterMap id

private def ordinary_stores (storage : OrdinaryStorage) (initializer : Json)
    (parse : Json → Except String Ordinary.Expression) : Except String (List Ordinary.Initialiser) :=
  match storage with
  | .scalar ty => do pure [⟨none, ty, ← parse initializer⟩]
  | .array element ty count => ordinary_array_stores element count ty initializer parse
  | .record layout => do
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
      if field_text node "kind" == "ImplicitValueInitExpr" then pure none
      else pure (some (⟨some member.offset, member.access, ← parse node⟩ : Ordinary.Initialiser))
    return stores.filterMap id

private def ordinary_return (records : List Ordinary.RecordLayout) (symbols : List OrdinarySignature)
    (globals : List OrdinaryObject) (result : String)
    (scope : List OrdinaryLocal) (budget : Nat) (node : Json) : Except String Ordinary.Expression := do
  let [value] := child_nodes node | throw "missing ordinary return expression"
  unless field_text node "kind" == "ReturnStmt" && ordinary_decl value result do
    throw "ordinary return differs from the function result type"
  let expression ← ordinary_expr records symbols globals scope budget false value
  unless ordinary_root_effect expression do throw "nested ordinary return effects require a sequencing proof"
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
    | _, _ => throw "ordinary case bound must be an integer literal"

private def ordinary_label_choice (guard : Json → Except String Ordinary.Expression) :
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
    | "ParenExpr", [child] => ordinary_label_choice guard depth child
    | "ImplicitCastExpr", [child] =>
      unless field_text node "castKind" == "NoOp" do throw "ordinary label pointer conversion changed representation"
      ordinary_label_choice guard depth child
    | "ConditionalOperator", [test, yes, no] =>
      return .conditional (← guard test) (← ordinary_label_choice guard depth yes) (← ordinary_label_choice guard depth no)
    | _, _ => throw "ordinary computed goto requires explicit label choices"

private def ordinary_statement (records : List Ordinary.RecordLayout) (symbols : List OrdinarySignature)
    (globals : List OrdinaryObject) (result : String) :
    Nat → Bool → Bool → List OrdinaryLocal → Nat → Json → Except String (List OrdinaryLocal × Ordinary.Statement)
  | 0, _, _, _, _, _ => .error "ordinary statement nesting exceeds the frontend budget"
  | budget + 1, inLoop, inSwitch, scope, slot, node => do
    let decode := ordinary_statement records symbols globals result budget
    let descend := decode inLoop inSwitch scope
    let expression := fun scope message node => do
      let value ← ordinary_expr records symbols globals scope (budget + 1) false node
      unless ordinary_root_effect value do throw message
      return value
    let guard := fun scope node => do
      unless ordinary_decl node "int" do throw "ordinary guard must be an int"
      let value ← ordinary_expr records symbols globals scope (budget + 1) false node
      unless ordinary_read_only value do throw "ordinary guard may only read state"
      return value
    match field_text node "kind", child_nodes node with
    | "CompoundStmt", children =>
      let (locals, _, reversed) ← children.foldlM (fun (locals, visible, reversed) child => do
        let (newLocals, statement) ← decode inLoop inSwitch visible (slot + locals.length) child
        let visible := if field_text child "kind" == "DeclStmt" then visible ++ newLocals else visible
        return (locals ++ newLocals, visible, statement :: reversed)) ([], scope, [])
      return (locals, .block (reversed.foldl (fun rest stmt => .sequence stmt rest) .empty))
    | "DeclStmt", [declaration] =>
      let name := field_text declaration "name"
      let ident := field_text declaration "id"
      let spelling := type_spelling declaration
      let [initializer] := child_nodes declaration | throw "ordinary local requires an initializer"
      let storage ← require (ordinary_storage records spelling) "unsupported ordinary local type"
      let width := storage.width
      unless field_text declaration "kind" == "VarDecl" && field_text declaration "storageClass" == "" &&
          ordinary_name name && !ident.isEmpty && !(scope.any (fun value => value.ident == ident)) &&
          ordinary_decl initializer spelling do
        throw "unsupported ordinary local declaration"
      unless width ≤ 9223372036854775792 do throw "ordinary local size exceeds host limits"
      let parse := expression scope "nested ordinary initializer effects require a sequencing proof"
      let initialise := do
        let stores ← ordinary_stores storage initializer parse
        unless Ordinary.Initialiser.fits width stores do throw "ordinary local initialiser spans overlap or exceed the object"
        pure (Ordinary.Statement.initialiseAggregate slot width stores)
      let action ← match storage with
        | .scalar ty => pure (.initialise slot ty (← parse initializer))
        | .array .. => initialise
        | .record layout =>
          if field_text initializer "kind" == "InitListExpr" then initialise
          else
            let source ← ordinary_record_source spelling (budget + 1) initializer
            let value ← ordinary_expr records symbols globals scope (budget + 1) true source
            unless ordinary_read_only value do throw "ordinary record source may only read state"
            pure (Ordinary.Statement.initialiseCopy slot value width layout.alignment)
      return ([⟨ident, name, spelling, storage, "VarDecl", slot⟩], action)
    | "IfStmt", condition :: chosen :: fallback =>
      let tested ← guard scope condition
      let (yesLocals, yes) ← descend slot chosen
      let (noLocals, no) ← match fallback with
        | [] => pure ([], .empty)
        | [other] => descend (slot + yesLocals.length) other
        | _ => throw "invalid ordinary branch"
      return (yesLocals ++ noLocals, .branch tested yes no)
    | "WhileStmt", [condition, body] =>
      let tested ← guard scope condition
      let (locals, action) ← decode true inSwitch scope slot body
      return (locals, .whileDo tested action)
    | "DoStmt", [body, condition] =>
      let (locals, action) ← decode true inSwitch scope slot body
      return (locals, .doWhile action (← guard scope condition))
    | "ForStmt", [initial, conditionVariable, condition, advance, body] =>
      unless field_text conditionVariable "kind" == "" && (child_nodes conditionVariable).isEmpty do
        throw "ordinary for loop requires an expression guard"
      unless ["DeclStmt", "NullStmt", ""].contains (field_text initial "kind") ||
          (ordinary_type (type_spelling initial)).isSome do
        throw "ordinary for loop requires a declaration or expression initialiser"
      let (initialLocals, start) ← descend slot initial
      let visible := scope ++ initialLocals
      let tested ← if field_text condition "kind" == "" && (child_nodes condition).isEmpty then pure none
        else some <$> guard visible condition
      let step ← if field_text advance "kind" == "" && (child_nodes advance).isEmpty then pure none
        else some <$> expression visible "nested ordinary advance effects require a sequencing proof" advance
      let (bodyLocals, action) ← decode true inSwitch visible (slot + initialLocals.length) body
      return (initialLocals ++ bodyLocals, .forDo start tested action step)
    | "GotoStmt", [] =>
      let identity := field_text node "targetLabelDeclId"
      unless !identity.isEmpty do throw "ordinary goto lacks a label identity"
      return ([], .gotoLabel identity)
    | "IndirectGotoStmt", [address] =>
      return ([], .indirect (← ordinary_label_choice (guard scope) (budget + 1) address))
    | "LabelStmt", [child] =>
      let identity := field_text node "declId"
      unless !identity.isEmpty do throw "ordinary label lacks a declaration identity"
      let (locals, action) ← descend slot child
      return (locals, .label identity action)
    | "SwitchStmt", [condition, body] =>
      let selector ← guard scope condition
      let (locals, action) ← decode inLoop true scope slot body
      return (locals, .select selector action)
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
    | "ReturnStmt", _ =>
      return ([], .result (← ordinary_return records symbols globals result scope (budget + 1) node))
    | _, _ =>
      let value ← expression scope "nested ordinary effects require a sequencing proof" node
      return ([], .discard value)

private def ordinary_parameter (node : Json) : Except String OrdinaryLocal := do
  let name := field_text node "name"
  let ident := field_text node "id"
  let spelling := type_spelling node
  let ty ← require (ordinary_type spelling) "unsupported ordinary parameter type"
  unless field_text node "kind" == "ParmVarDecl" && ordinary_name name && !ident.isEmpty &&
      field_text node "storageClass" == "" && (child_nodes node).isEmpty do
    throw "unsupported ordinary parameter"
  return ⟨ident, name, spelling, .scalar ty, "ParmVarDecl", 0⟩

private def ordinary_signature (unit : OrdinaryUnit) (node : Json) : Except String OrdinarySignature := do
  let name := field_text node "name"
  let spelling := type_spelling node
  let [rawResult, tail] := spelling.splitOn "(" | throw "ordinary callee requires a nonvariadic function type"
  let result := rawResult.trim
  let ty ← require (ordinary_type result) "unsupported ordinary result type"
  let body :: arguments := (child_nodes node).reverse | throw "ordinary callee requires a body"
  let parameters ← arguments.reverse.mapM ordinary_parameter
  let parameters := parameters.zipIdx.map fun (parameter, slot) => { parameter with slot }
  let parameterText := if parameters.isEmpty then "void" else String.intercalate ", " (parameters.map (·.spelling))
  unless ordinary_name name && field_text body "kind" == "CompoundStmt" && tail == parameterText ++ ")" &&
      ["", "static"].contains (field_text node "storageClass") &&
      decide ((parameters.map (·.ident)).Nodup) do
    throw "unsupported ordinary function definition"
  let symbol := unit_function_key unit.namespaceName unit.declarations name
  return ⟨name, symbol, spelling, result, ty, parameters, [], body, unit.records⟩

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

private def ordinary_procedures (records : List Ordinary.RecordLayout) (symbols : List OrdinarySignature)
    (globals : List OrdinaryObject) (namespaceName : String) (labels : List (String × String)) (budget slot graphCount : Nat) :
    List Json → Except String (List Ordinary.Procedure)
  | [] => .ok []
  | declaration :: rest => do
    let symbol ← require (symbols.find? fun symbol => symbol.name == field_text declaration "name")
      "ordinary prototype has no checked definition"
    if (child_nodes declaration).any (fun node => field_text node "kind" == "CompoundStmt") then
      let (locals, statements) ← ordinary_statement records symbols globals symbol.result budget false false symbol.parameters
        symbol.parameters.length symbol.entry
      let bindings := symbol.parameters ++ locals
      unless decide ((bindings.map (·.ident)).Nodup) do throw "ordinary locals share a declaration identity"
      let slots := bindings.map fun binding => namespaceName ++ binding.name ++ "." ++ toString (slot + binding.slot)
      let graphName := "g_" ++ namespaceName.replace ":" "_" ++ toString graphCount
      let dispatch ← if statements.needs_dispatch then some <$> Ordinary.compile_dispatch graphName statements labels else pure none
      let parameters ← symbol.parameters.mapM fun parameter => require parameter.storage.scalar_type "ordinary parameter must be scalar"
      let procedure : Ordinary.Procedure :=
        ⟨symbol.symbol, symbol.ty, parameters, locals.map (·.storage.width), slots, statements, dispatch⟩
      return procedure :: (← ordinary_procedures records symbols globals namespaceName labels budget (slot + bindings.length)
        (graphCount + if dispatch.isSome then 1 else 0) rest)
    else
      let used ← ordinary_prototype symbol declaration
      ordinary_procedures records symbols globals namespaceName labels budget (slot + used) graphCount rest

private def ordinary_objects (unit : OrdinaryUnit) : List Json :=
  unit.objects.filter (fun node => field_text node "storageClass" != "extern" || field_text node "init" != "")

private def ordinary_private_object (unit : OrdinaryUnit) (name : String) : Bool :=
  unit.objects.any (fun node => field_text node "name" == name && field_text node "storageClass" == "static")

private def ordinary_unit (namespaceName : String) (budget : Nat) (tree : Json) : Except String OrdinaryUnit := do
  let nodes := child_nodes tree
  let declarations := unit_function_declarations tree
  let objects := nodes.filter (fun node => source_declaration node && field_text node "kind" == "VarDecl")
  let records := nodes.filterMap ordinary_record
  unless decide ((records.map (·.spelling)).Nodup) do throw "ambiguous ordinary record definition"
  let builtin := ["malloc", "memmove", "putchar", "free", "exit"]
  unless !(declarations.any (fun node => builtin.contains (field_text node "name"))) &&
      !(objects.any (fun node => builtin.contains (field_text node "name"))) &&
      !((function_definitions nodes).any (fun node => builtin.contains (field_text node "name"))) do
    throw "ordinary certificate requires standard builtins"
  let functions ← (function_definitions declarations).mapM (fun node =>
    (field_text node "name", ·) <$> startup_nodes (budget + 1) node)
  return ⟨namespaceName, budget, tree, declarations, objects, records, label_names namespaceName functions⟩

private def ordinary_object_definition (unit : OrdinaryUnit) (node : Json) (index : Nat) :
    Except String OrdinaryObject := do
  let name := field_text node "name"
  let spelling := type_spelling node
  let storage ← require (ordinary_storage unit.records spelling) "unsupported ordinary global type"
  unless storage.width ≤ 9223372036854775800 do throw "ordinary global size exceeds host limits"
  unless ordinary_name name && field_text node "id" != "" && field_text node "tls" == "" &&
      ["", "extern", "static"].contains (field_text node "storageClass") do
    throw "unsupported ordinary global storage"
  let symbol := if ordinary_private_object unit name then unit.namespaceName ++ name ++ "." ++ toString index
    else "extern:" ++ name
  let pointed := unit.records.find? (·.spelling == ordinary_pointee spelling)
  return ⟨name, symbol, spelling, storage, node, [], pointed⟩

private def ordinary_global_scope (unit : OrdinaryUnit) (definitions localDefinitions : List OrdinaryObject) :
    Except String (List OrdinaryObject) := do
  let visible := (child_nodes unit.tree).filter (fun node => field_text node "kind" == "VarDecl")
  let selected := definitions.filter (fun object =>
    if ordinary_private_object unit object.name then
      localDefinitions.any (fun resident => resident.symbol == object.symbol)
    else object.symbol == "extern:" ++ object.name)
  let bindings : List OrdinaryObject ← (selected.filter (fun object => visible.any (fun node => field_text node "name" == object.name))).mapM
    fun object => do
      let declarations := visible.filter (fun node => field_text node "name" == object.name)
      unless declarations.all (fun node => ordinary_decl node object.spelling && field_text node "id" != "" &&
          field_text node "tls" == "") do
        throw "ordinary global declaration differs from its definition"
      let layout := match object.storage with
        | .record layout => some layout
        | _ => object.recordTarget
      if let some expected := layout then
        unless unit.records.any (fun actual => actual.spelling == expected.spelling &&
            ordinary_record_compatible expected actual) do throw "ordinary global record layout disagrees with its definition"
      return { object with identities := declarations.map (field_text · "id") }
  let ids : List String := bindings.flatMap (·.identities)
  unless decide ids.Nodup && unit.objects.all (fun node => ids.contains (field_text node "id")) do
    throw "unresolved or ambiguous ordinary global declaration"
  return bindings

private def ordinary_static_value : Ordinary.Expression → Bool
  | .literal _ | .nullPointer | .globalAddress _ => true
  | .cast _ child => ordinary_static_value child
  | _ => false

private def ordinary_initialiser (records : List Ordinary.RecordLayout) (globals : List OrdinaryObject)
    (budget : Nat) (object : OrdinaryObject) :
    Except String Ordinary.Global := do
  let scalar := fun (node : Json) => do
    let expression ← ordinary_expr records [] globals [] budget false node
    unless ordinary_static_value expression do throw "ordinary global initialiser must be a literal or global address"
    return expression
  let stores : List Ordinary.Initialiser ← match child_nodes object.definition with
    | [] => pure []
    | [initializer] => do
      unless ordinary_decl initializer object.spelling do throw "ordinary global initialiser has the wrong type"
      ordinary_stores object.storage initializer scalar
    | _ => throw "unsupported ordinary global initialiser"
  return ⟨object.symbol, object.storage.width, stores⟩

private def ordinary_imports (unit : OrdinaryUnit) (exports : List OrdinarySignature) : List OrdinarySignature :=
  let declarations := (child_nodes unit.tree).filter (fun node => field_text node "kind" == "FunctionDecl")
  exports.filterMap fun definition => do
    guard (unit_function_key unit.namespaceName unit.declarations definition.name == definition.symbol)
    guard ((definition.result :: definition.parameters.map (·.spelling)).all
      (ordinary_record_pointer_compatible definition.records unit.records))
    let visible := declarations.filter fun declaration =>
      field_text declaration "name" == definition.name && type_spelling declaration == definition.spelling &&
        (source_declaration declaration || ["", "extern"].contains (field_text declaration "storageClass"))
    let identities := visible.map (field_text · "id")
    guard (!identities.isEmpty && identities.all (!·.isEmpty) && decide identities.Nodup)
    return { definition with declarations := identities }

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
    let [entry] := exports.filter (fun definition => definition.symbol == "main")
      | throw "ordinary certificate requires exactly one externally visible main definition"
    unless ["int (void)", "int (int, char **)"].contains entry.spelling do
      throw "ordinary entry must be int main(void) or int main(int, char **)"
    let byUnit ← units.mapM fun unit => do
      let definitions := ordinary_objects unit
      unless decide ((definitions.map (field_text · "name")).Nodup) do
        throw "ordinary certificate requires one definition per global"
      (definitions.zipIdx).mapM (fun (node, index) => ordinary_object_definition unit node index)
    let allObjects := byUnit.flatten
    unless decide ((allObjects.map (·.symbol)).Nodup) do throw "multiple definitions of an ordinary global"
    let bodies ← (units.zip byUnit).mapM fun (unit, definitions) => do
      let globals ← ordinary_global_scope unit allObjects definitions
      let initialisers ← definitions.mapM (ordinary_initialiser unit.records globals (unit.budget + 1))
      let procedures ← ordinary_procedures unit.records (ordinary_imports unit exports) globals unit.namespaceName
        unit.labels (unit.budget + 1) (globals.flatMap (·.identities)).length 0 unit.declarations
      pure (⟨unit.namespaceName, procedures, initialisers, unit.labels.map Prod.snd⟩ : Ordinary.UnitBody)
    let program : Ordinary.Program := ⟨bodies⟩
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
      else if head == '"' then
        let value := tail.takeWhile (fun c => c != '"' && c != '\\' && c != '\n' && c != '\r')
        match tail.drop value.length with
        | '"' :: suffix => scan fuel suffix ((String.mk ('"' :: value ++ ['"'])) :: output)
        | _ => .error "unsupported ordinary string escape"
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
  exact Ordinary.prefix_refines program terminal fuel invocation ⟨[], ⟨1, 4096⟩⟩ ⟨[], [], 0, true⟩ rfl id (by intro a b eq; exact eq)

theorem ordinary_completed_behaviour (runtime : String) (frontends : List String) (generated : String)
    (program : Ordinary.Program) (accepted : validate_ordinary runtime frontends generated = .ok program)
    (invocation : Ordinary.Invocation) (terminal : Bool) (result : TraceOutcome × List UInt8) :
    Ordinary.Observes (fun fuel => program.observation fuel terminal invocation) result ↔
      Ordinary.Observes (fun fuel => program.source_observation fuel terminal invocation) result := by
  have agrees (fuel : Nat) := (ordinary_observation_sound runtime frontends generated program accepted fuel terminal invocation).2
  unfold Ordinary.Observes
  simp only [agrees]

theorem ordinary_executable_behaviour (input : Input) (artifact : Executable) (runtime : String)
    (frontends : List String) (generated : String) (program : Ordinary.Program)
    (frontend : Input → Except String (List String)) (ghc : String → Except String Executable)
    (native_observes : Input → Ordinary.Invocation → Bool → TraceOutcome × List UInt8 → Prop)
    (executable_observes : Executable → Ordinary.Invocation → Bool → TraceOutcome × List UInt8 → Prop)
    (dumped : frontend input = .ok frontends) (built : ghc generated = .ok artifact)
    (accepted : validate_ordinary runtime frontends generated = .ok program)
    (frontend_adequate : frontend input = .ok frontends → ordinary_source frontends = .ok program →
      ∀ invocation terminal result, native_observes input invocation terminal result ↔
        Ordinary.Observes (fun fuel => program.source_observation fuel terminal invocation) result)
    (ghc_adequate : ∀ prelude body, standalone_runtime runtime = .ok prelude → runtime = ordinary_runtime →
      generated = prelude ++ "\n" ++ body → ordinary_locations body = .ok program.moduleBody → ghc generated = .ok artifact →
      ∀ invocation terminal result, executable_observes artifact invocation terminal result ↔
        Ordinary.Observes (fun fuel => program.observation fuel terminal invocation) result) :
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
    ((ordinary_completed_behaviour runtime frontends generated program accepted invocation terminal result).trans
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
    init.offset.getD 0 + init.ty.width ≤ object.width := by
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

private def refers_to_common (common opaqueNode : Json) : Bool :=
  match child_nodes opaqueNode with
  | [child] => field_text opaqueNode "kind" == "OpaqueValueExpr" && field_text common "id" != "" &&
      field_text child "id" == field_text common "id" && type_spelling opaqueNode == "int"
  | _ => false

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

#print axioms Heresy.kernel_certificate_sound
#print axioms Heresy.kernel_return_preserves_result
#print axioms Heresy.checked_kernel_entry_equation
#print axioms Heresy.checked_dispatch_counts
#print axioms Heresy.program_certificate_sound
#print axioms Heresy.framed_program_certificate_sound
#print axioms Heresy.closed_executable_exit_refines
#print axioms Heresy.closed_text_executable_exit
#print axioms Heresy.certified_helper_uses_bound_arguments
#print axioms Heresy.link_schedule_order
#print axioms Heresy.linkage_certificate_routes
#print axioms Heresy.certified_definition_authentication
#print axioms Heresy.linkage_certificate_line
#print axioms Heresy.linkage_validation_sound

private def check_observation (runtime haskell steps status stdout : String) (frontends : List String)
    (invocation : Heresy.Ordinary.Invocation) : IO UInt32 := do
  match steps.toNat?, status.toNat? with
  | some budget, some observedStatus =>
    match Heresy.validate_ordinary (← IO.FS.readFile runtime)
        (← frontends.mapM (fun (path : String) => IO.FS.readFile path)) (← IO.FS.readFile haskell) with
    | .error message => IO.eprintln message; pure 1
    | .ok program =>
      let (outcome, visible) := program.observation budget false invocation
      let expected := match outcome with
        | .returned code => some code.toNat
        | .fault _ => some 70
        | .paused => none
      if expected == some observedStatus && (← IO.FS.readBinFile stdout).data.toList == visible then
        IO.println "checked the linked program's exit status and stdout"
        pure 0
      else
        IO.eprintln "ordinary observation disagrees with supplied exit status or stdout, or exceeded its step budget"
        pure 1
  | _, _ => IO.eprintln "ordinary observation requires a step budget and numeric exit status"; pure 1

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | "module" :: runtime :: haskell :: ast :: rest =>
    match Heresy.validate_module (← IO.FS.readFile runtime)
        (← (ast :: rest).mapM (fun (path : String) => IO.FS.readFile path)) (← IO.FS.readFile haskell) with
    | .ok count =>
      IO.println s!"checked complete runtime, linkage of {count} function(s) and dispatch structure"
      pure 0
    | .error message => IO.eprintln message; pure 1
  | "ordinary-link" :: runtime :: haskell :: ast :: rest =>
    match Heresy.validate_ordinary (← IO.FS.readFile runtime)
        (← (ast :: rest).mapM (fun (path : String) => IO.FS.readFile path)) (← IO.FS.readFile haskell) with
    | .ok _ => IO.println "checked all ordinary function bodies, direct calls, and startup"; pure 0
    | .error message => IO.eprintln message; pure 1
  | "ordinary-observe" :: runtime :: haskell :: steps :: status :: stdout :: ast :: rest =>
    check_observation runtime haskell steps status stdout (ast :: rest) {}
  | "ordinary-observe-argv" :: runtime :: haskell :: steps :: status :: stdout :: argv :: ast :: rest =>
    match Heresy.Ordinary.Invocation.decode (← IO.FS.readBinFile argv).data.toList with
    | some invocation => check_observation runtime haskell steps status stdout (ast :: rest) invocation
    | none => IO.eprintln "expected NUL-terminated argv entries, including argv[0]"; pure 1
  | ["ordinary", runtime, ast, haskell] =>
    match Heresy.validate_ordinary (← IO.FS.readFile runtime) [← IO.FS.readFile ast]
        (← IO.FS.readFile haskell) with
    | .ok _ => IO.println "checked all ordinary function bodies, direct calls, and startup"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["effects", runtime, ast, haskell, stdout] =>
    match Heresy.validate_ordinary (← IO.FS.readFile runtime) [← IO.FS.readFile ast]
        (← IO.FS.readFile haskell) with
    | .error message => IO.eprintln message; pure 1
    | .ok program =>
      let (outcome, visible) := program.observation 256 false
      if outcome = .fault (.access .dead) && (← IO.FS.readBinFile stdout).data.toList == visible then
        IO.println "checked the decoded program's stale alias fault and stdout"
        pure 0
      else
        IO.eprintln "ordinary program does not predict the stale alias fault and supplied stdout"
        pure 1
  | ["effects", stdout] =>
    let observed := (Heresy.copied_alias_run 65).snapshot.observation
    let overlap := Heresy.copied_alias_uses_overlapping_snapshot
    let _ := overlap
    if observed.1 = .fault (.access .dead) &&
        (← IO.FS.readBinFile stdout).data.toList == observed.2 then
      IO.println "checked overlapping copy, pointer shadow, release fault and visible stdout"
      pure 0
    else
      IO.eprintln "stdout differs from the copied-alias model"
      pure 1
  | ["shared", name, ast, haskell] =>
    match Heresy.validate_shared name (← IO.FS.readFile ast) (← IO.FS.readFile haskell) with
    | .ok () => IO.println s!"checked shared conditional in {name}"; pure 0
    | .error message => IO.eprintln message; pure 1
  | "linkage" :: haskell :: ast :: rest =>
    match Heresy.validate_linkage (← (ast :: rest).mapM (fun (path : String) => IO.FS.readFile path)) (← IO.FS.readFile haskell) with
    | .ok count => IO.println s!"checked {count} linked function bindings, label symbols and startup"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["dispatch", haskell] =>
    match Heresy.validate_dispatches (← IO.FS.readFile haskell) with
    | .ok count => IO.println s!"checked dispatch equations and {count} emitted control-flow graph(s)"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["process", haskell] =>
    if Heresy.validates_process (← IO.FS.readFile haskell) then
      IO.println "checked stream operations, process termination and cleanup equations"; pure 0
    else
      IO.eprintln "stream operations, process termination or cleanup differ from the model"; pure 1
  | ["memory", haskell] =>
    let generated ← IO.FS.readFile haskell
    if !Heresy.validates_access generated then
      IO.eprintln "memory access differs from the model"; pure 1
    else if !Heresy.validates_pointer_arithmetic generated then
      IO.eprintln "pointer arithmetic differs from the model"; pure 1
    else if !Heresy.validates_release generated then
      IO.eprintln "memory release differs from the model"; pure 1
    else if !Heresy.validates_allocation generated then
      IO.eprintln "memory allocation differs from the model"; pure 1
    else if !Heresy.validates_copy generated then
      IO.eprintln "memory copy differs from the model"; pure 1
    else if !Heresy.validates_aggregate_memory generated then
      IO.eprintln "aggregate memory differs from the model"; pure 1
    else if !Heresy.validates_atomic_memory generated then
      IO.eprintln "atomic memory differs from the model"; pure 1
    else if !Heresy.validates_scalar_memory generated then
      IO.eprintln "scalar memory differs from the model"; pure 1
    else if !Heresy.validates_pointer_memory generated then
      IO.eprintln "pointer memory differs from the model"; pure 1
    else if !Heresy.validates_freeze generated then
      IO.eprintln "read-only transition differs from the model"; pure 1
    else if !Heresy.validates_synchronisation generated then
      IO.eprintln "synchronisation differs from the model"; pure 1
    else if !Heresy.validates_argument_slots generated then
      IO.eprintln "argument slot layout differs from the model"; pure 1
    else if !Heresy.validates_invocation generated then
      IO.eprintln "call routing differs from the model"; pure 1
    else IO.println "checked memory, calls and synchronisation equations"; pure 0
  | ["program", ast, haskell] =>
    match Heresy.validate_program (← IO.FS.readFile ast) (← IO.FS.readFile haskell) with
    | .ok () => IO.println "checked emitted closed program and exit status"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["text", source, haskell] =>
    match Heresy.validate_closed_text (← IO.FS.readFile source) (← IO.FS.readFile haskell) with
    | .ok body => IO.println s!"checked closed C source and lowering, exit status {Heresy.source_status body}"; pure 0
    | .error message => IO.eprintln message; pure 1
  | [ast, haskell] =>
    let frontend ← IO.FS.readFile ast
    let generated ← IO.FS.readFile haskell
    match Heresy.validate_kernels frontend generated with
    | .ok count => IO.println s!"checked {count} emitted integer kernel(s)"; pure 0
    | .error message => IO.eprintln message; pure 1
  | _ =>
    IO.eprintln "usage: certificate [program] AST.json Module.hs | certificate text SOURCE.c Module.hs | certificate shared FUNCTION AST.json Module.hs | certificate (dispatch|memory|process) Module.hs | certificate linkage Module.hs AST.json ... | certificate module Heap.hs Module.hs AST.json ... | certificate ordinary Heap.hs AST.json Module.hs | certificate ordinary-link Heap.hs Module.hs AST.json ... | certificate ordinary-observe Heap.hs Module.hs STEPS STATUS STDOUT AST.json ... | certificate ordinary-observe-argv Heap.hs Module.hs STEPS STATUS STDOUT ARGV AST.json ... | certificate effects [Heap.hs AST.json Module.hs] STDOUT"
    pure 2
