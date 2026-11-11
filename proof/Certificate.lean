import Lean.Data.Json
import Semantics
import Synchronisation

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

private def unit_entries (unit_name : String) (tree : Json) : List (String × String) :=
  let functions := unit_function_declarations tree
  let internal := (functions.filter (fun node => field_text node "storageClass" == "static")).map (field_text · "name")
  (function_definitions functions).map
    (fun node =>
      let name := field_text node "name"
      let key := if internal.contains name then unit_name ++ name else name
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
    let children := if field_text node "kind" == "GenericSelectionExpr" then
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

private def unit_startup (unit_name : String) (depth : Nat) (tree : Json) : Except String LinkStartup := do
  let functions ← (function_definitions (unit_function_declarations tree)).mapM (fun node =>
    (field_text node "name", ·) <$> startup_nodes depth node)
  let objects ← (object_definitions tree).mapM (startup_nodes depth)
  let labels : List (String × String) := functions.foldl (fun labels (name, nodes) =>
    nodes.foldl (fun labels node =>
      let ident := field_text node "labelDeclId"
      if field_text node "kind" == "AddrLabelExpr" && !(labels.any (fun entry => entry.1 == ident)) then
        (ident, "label:" ++ unit_name ++ name ++ ":" ++ toString labels.length) :: labels
      else labels) labels) []
  pure ⟨(functions.any (fun (_, nodes) => nodes.any thread_reference)) || (objects.any (·.any thread_reference)), labels.map Prod.snd⟩

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
    "      initial = World counter [] S.empty S.empty (S.fromList entries) codes \"startup\" 0 [] False False table gate threads owner nullPointer initThread",
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
  let transformer := String.intercalate "\n" [
    "newtype R a = R { unR :: ExceptT Fault (StateT World IO) a }",
    "  deriving (Functor, Applicative, Monad, MonadIO, MonadState World, MonadError Fault)",
    "",
    "runWorld :: World -> R a -> IO (Either Fault a, World)",
    "runWorld world action = runStateT (runExceptT (unR action)) world"]
  let finish := "builtin \"exit\" [code] = throwError (Finish (fromInteger (number code `mod` 256)))"
  let stream_seed := "  table <- newIORef (1, M.empty)"
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
    "builtin \"fclose\" [value@(Stream ident _)] = do",
    "  handle <- stream value",
    "  io (hClose handle)",
    "  table <- gets streamTable",
    "  liftIO $ atomicModifyIORef' table $ \\(next, entries) -> ((next, M.delete ident entries), ())",
    "  pure (Number 0)"]
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
  let epilogue := String.intercalate "\n" [
    "  outcome <- E.try (runWorld initial action)",
    "  let (result, final) = either (\\fault -> (Left fault, initial)) id outcome",
    "  handles <- snd <$> readIORef table",
    "  forM_ (M.elems handles) (void . tryIOError . hClose)",
    "  hFlush stdout",
    "  case result of",
    "    Right value -> let code = fromInteger (number value `mod` 256) in exitWith (if code == 0 then ExitSuccess else ExitFailure code)",
    "    Left (Finish code) -> exitWith (if code == 0 then ExitSuccess else ExitFailure code)",
    "    Left (Transfer _) -> hPutStrLn stderr \"heresy panic: control transfer escaped its function\" >> exitWith (ExitFailure 70)",
    "    Left (Panic message) -> do",
    "      hPutStrLn stderr (\"heresy panic: \" ++ message)",
    "      unless (enabled || null (recent final)) $ hPutStrLn stderr (intercalate \"\\n\" (reverse (recent final)))",
    "      exitWith (ExitFailure 70)"]
  [nearestCoefficient, decimalDigits, fixedExtended, scientificExtended, transformer, finish, stream_seed, stream_lookup, register, close, file_read, epilogue].all
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

end Heresy

#print axioms Heresy.kernel_certificate_sound
#print axioms Heresy.kernel_return_preserves_result
#print axioms Heresy.checked_kernel_entry_equation
#print axioms Heresy.checked_dispatch_counts
#print axioms Heresy.program_certificate_sound
#print axioms Heresy.framed_program_certificate_sound
#print axioms Heresy.closed_executable_exit_refines
#print axioms Heresy.certified_helper_uses_bound_arguments
#print axioms Heresy.link_schedule_order
#print axioms Heresy.linkage_certificate_routes
#print axioms Heresy.certified_definition_authentication
#print axioms Heresy.linkage_certificate_line
#print axioms Heresy.linkage_validation_sound

def main (arguments : List String) : IO UInt32 := do
  match arguments with
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
  | [ast, haskell] =>
    let frontend ← IO.FS.readFile ast
    let generated ← IO.FS.readFile haskell
    match Heresy.validate_kernels frontend generated with
    | .ok count => IO.println s!"checked {count} emitted integer kernel(s)"; pure 0
    | .error message => IO.eprintln message; pure 1
  | _ =>
    IO.eprintln "usage: certificate [program] AST.json Module.hs | certificate (dispatch|memory|process) Module.hs | certificate linkage Module.hs AST.json ..."
    pure 2
