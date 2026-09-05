import Lean.Data.Json
import Proof

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

def render_target : Target → String
  | .constant value => toString value
  | .parameter index => "x" ++ toString index
  | .binary operator left right =>
    "(" ++ render_target left ++ ") " ++ operator_text operator ++ " (" ++ render_target right ++ ")"
  | .wrap width expression =>
    "normalise " ++ toString width ++ " False (" ++ render_target expression ++ ")"
  | .conditional condition yes no =>
    "if (" ++ render_target condition ++ ") == 0 then (" ++ render_target no ++ ") else (" ++ render_target yes ++ ")"

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

private def read_expression (parameters : List String) : Nat → Json → Except String Source
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
      let index ← require (parameters.idxOf? ident) "kernel references external state"
      pure (.parameter index)
    | "ParenExpr", [child] => read_expression parameters depth child
    | "ImplicitCastExpr", [child] =>
      unless field_text node "castKind" == "LValueToRValue" ||
          field_text node "castKind" == "NoOp" do
        throw "kernel cast changes the value"
      read_expression parameters depth child
    | "BinaryOperator", [left, right] =>
      .binary <$> read_operator (field_text node "opcode")
              <*> read_expression parameters depth left
              <*> read_expression parameters depth right
    | "ConditionalOperator", [condition, yes, no] =>
      .conditional <$> read_expression parameters depth condition
                   <*> read_expression parameters depth yes <*> read_expression parameters depth no
    | _, _ => throw "unsupported kernel expression"

private def kernel_symbol (name : String) : String :=
  let digits := "0123456789abcdef".toList.toArray
  name.toUTF8.toList.foldl (fun symbol byte =>
    (symbol.push digits[byte.toNat / 16]!).push digits[byte.toNat % 16]!) "k_"

private def kernel_source (node : Json) (depth : Nat) : Except String (Source × Nat) := do
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
      let source ← read_expression identifiers depth expression
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

def validate_dispatches (generated : String) : Except String Nat := do
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

def validates_shadow_copy (generated : String) : Bool :=
  let sections := generated.splitOn "\n\n"
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
  [range, shadow, copy].all sections.contains

private def closed_source (frontend : String) : Except String Source := do
  let tree ← Json.parse frontend
  unless field_text tree "kind" == "TranslationUnitDecl" do
    throw "expected a translation unit"
  let declarations := (child_nodes tree).filter fun node =>
    field_text node "kind" != "EmptyDecl" &&
      !(field_text node "kind" == "TypedefDecl" && json_field node "isImplicit" == .bool true)
  let [main] := declarations | throw "closed program must define only main"
  unless field_text main "kind" == "FunctionDecl" && field_text main "name" == "main" &&
      type_spelling main == "int (void)" do
    throw "closed program must define int main(void)"
  let [body] := child_nodes main | throw "invalid closed main definition"
  let [statement] := child_nodes body | throw "closed main must contain one return"
  let [cast] := child_nodes statement | throw "closed main must return one value"
  let [expression] := child_nodes cast | throw "closed main must cast its return value to int"
  unless field_text body "kind" == "CompoundStmt" && field_text statement "kind" == "ReturnStmt" &&
      field_text cast "kind" == "CStyleCastExpr" && field_text cast "castKind" == "IntegralCast" &&
      type_spelling cast == "int" do
    throw "closed main must return an unsigned long expression cast to int"
  read_expression [] frontend.length expression

def render_program (body : Target) : String := String.intercalate "\n" [
  "module Main where", "",
  "import Data.Bits", "import System.Exit", "",
  "normalise :: Int -> Bool -> Integer -> Integer",
  "normalise width _ value = value `mod` (2 ^ width)", "",
  "exitStatus :: Integer -> ExitCode",
  "exitStatus value = case fromInteger (value `mod` 256) of",
  "  0 -> ExitSuccess", "  code -> ExitFailure code", "",
  "main :: IO ()", "main = exitWith (exitStatus (" ++ render_target body ++ "))", ""]

def validates_program (body : Source) (generated : String) : Bool :=
  generated == render_program (lower body)

theorem program_certificate_sound (body : Source) (generated : String)
    (accepted : validates_program body generated = true) :
    ∃ target : Target, generated = render_program target ∧ target_status target = source_status body := by
  refine ⟨lower body, ?_, lower_program_correct body⟩
  simpa [validates_program] using accepted

def validate_program (frontend generated : String) : Except String Unit := do
  let body ← closed_source frontend
  unless validates_program body generated do
    throw "emitted program differs from verified lowering"

end Heresy

#print axioms Heresy.kernel_certificate_sound
#print axioms Heresy.program_certificate_sound

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["dispatch", haskell] =>
    match Heresy.validate_dispatches (← IO.FS.readFile haskell) with
    | .ok count => IO.println s!"checked {count} emitted control-flow graph(s)"; pure 0
    | .error message => IO.eprintln message; pure 1
  | ["memory", haskell] =>
    if Heresy.validates_shadow_copy (← IO.FS.readFile haskell) then
      IO.println "checked shadow copy equations"; pure 0
    else IO.eprintln "shadow copy differs from the model"; pure 1
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
