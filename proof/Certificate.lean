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

end Heresy

#print axioms Heresy.kernel_certificate_sound

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [ast, haskell] =>
    let frontend ← IO.FS.readFile ast
    let generated ← IO.FS.readFile haskell
    match Heresy.validate_kernels frontend generated with
    | .ok count => IO.println s!"checked {count} emitted integer kernel(s)"; pure 0
    | .error message => IO.eprintln message; pure 1
  | _ => IO.eprintln "usage: certificate AST.json Module.hs"; pure 2
