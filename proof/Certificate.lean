import Lean.Data.Json
import Semantics

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

private def kernel_symbol (name : String) : String :=
  let digits := "0123456789abcdef".toList.toArray
  name.toUTF8.toList.foldl (fun symbol byte =>
    (symbol.push digits[byte.toNat / 16]!).push digits[byte.toNat % 16]!) "k_"

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

def validate_kernels (frontend generated : String) : Except String Nat := do
  let tree ← Json.parse frontend
  let lines := generated.splitOn "\n"
  unless has_normalisation lines do
    throw "generated integer normalisation differs from the model"
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
  [dispatch, computed].all sections.contains

def validate_dispatches (generated : String) : Except String Nat := do
  unless validates_dispatch_runtime generated do
    throw "dispatch runtime differs from the model"
  let lines := (generated.splitOn "\n").filter (·.startsWith "g_")
  let mut names : List String := []
  let mut signatures : List String := []
  for line in lines do
    let signature := " :: (Int, [[Int]])"
    if line.endsWith signature then
      signatures := line.take (line.length - signature.length) :: signatures
    else
      match line.splitOn " = (" with
      | [name, row] =>
        let graph ← read_dispatch row
        unless valid_dispatch graph do
          throw ("dispatch target outside its graph: " ++ name)
        names := name :: names
      | _ => throw "invalid dispatch declaration"
  if names.isEmpty || !decide names.Nodup || names != signatures then
    throw "unaccounted or missing dispatch declarations"
  else pure names.length

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

private inductive ClosedProgram where
  | direct (helpers : List (Helper Source)) (body : Command Source)
  | framed (helpers : List (Helper (Command Source))) (body : Command Source)

private def single_return (block : Json) : Bool :=
  match child_nodes block with
  | [statement] => field_text statement "kind" == "ReturnStmt" && (child_nodes statement).length == 1
  | _ => false

private def closed_source (frontend : String) : Except String ClosedProgram := do
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

def validate_program (frontend generated : String) : Except String Unit := do
  match ← closed_source frontend with
  | .direct helpers body =>
    unless validates_program helpers body generated do
      throw "emitted program differs from verified lowering"
  | .framed helpers body =>
    unless check_frame_helpers (helpers.toArray.map Helper.arity) helpers do
      throw "closed helper can fall through or use an out-of-scope call"
    unless validates_framed_program helpers body generated do
      throw "emitted program differs from verified framed lowering"

end Heresy

#print axioms Heresy.kernel_certificate_sound
#print axioms Heresy.program_certificate_sound
#print axioms Heresy.framed_program_certificate_sound
#print axioms Heresy.certified_helper_uses_bound_arguments

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["dispatch", haskell] =>
    match Heresy.validate_dispatches (← IO.FS.readFile haskell) with
    | .ok count => IO.println s!"checked dispatch equations and {count} emitted control-flow graph(s)"; pure 0
    | .error message => IO.eprintln message; pure 1
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
    else if !Heresy.validates_scalar_memory generated then
      IO.eprintln "scalar memory differs from the model"; pure 1
    else if !Heresy.validates_freeze generated then
      IO.eprintln "read-only transition differs from the model"; pure 1
    else IO.println "checked allocation, access, pointer arithmetic, release, copy, scalar and read-only equations"; pure 0
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
    IO.eprintln "usage: certificate [program] AST.json Module.hs | certificate (dispatch|memory) Module.hs"
    pure 2
