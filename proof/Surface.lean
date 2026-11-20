import Proof

set_option warningAsError true

namespace Heresy.Surface

private def word_char (char : Char) : Bool :=
  char.toNat < 128 && (char.isAlphanum || char == '_')

private def whitespace (char : Char) : Bool :=
  [' ', '\t', '\n', '\r', Char.ofNat 11, Char.ofNat 12].contains char

private def punctuation (char : Char) : Bool :=
  ['(', ')', '{', '}', '+', '-', '*', '&', '|', '^', '?', ':', ';'].contains char

private def doubled (char : Char) (tail : List Char) : Bool :=
  ['+', '-', '&', '|'].contains char && tail.head? == some char

private def word_boundary (chars : List Char) : Prop :=
  match chars.head? with
  | some char => word_char char = false
  | none => True

inductive Tokens : List Char → List String → Prop where
  | empty : Tokens [] []
  | space : whitespace char = true → Tokens tail tokens → Tokens (char :: tail) tokens
  | word : whitespace char = false → word_char char = true →
      (∀ letter ∈ letters, word_char letter = true) → word_boundary tail →
      Tokens tail tokens → Tokens (char :: letters ++ tail) (String.mk (char :: letters) :: tokens)
  | symbol : whitespace char = false → word_char char = false → doubled char tail = false →
      punctuation char = true → Tokens tail tokens → Tokens (char :: tail) (String.singleton char :: tokens)

private def scan : Nat → List Char → Except String (List String)
  | _, [] => .ok []
  | 0, _ => .error "incomplete C token stream"
  | fuel + 1, head :: tail => do
    if whitespace head then scan fuel tail
    else if word_char head then
      return String.mk (head :: tail.takeWhile word_char) :: (← scan fuel (tail.dropWhile word_char))
    else if doubled head tail then
      throw "unsupported compound C token"
    else if punctuation head then
      return String.singleton head :: (← scan fuel tail)
    else throw "unsupported character in closed C source"

def tokenize (input : String) : Except String (List String) := scan (input.length + 1) input.toList

private theorem word_prefix (chars : List Char) :
    ∀ letter ∈ chars.takeWhile word_char, word_char letter = true := by
  induction chars with
  | nil => simp
  | cons head tail ih =>
    by_cases word : word_char head
    · simpa [List.takeWhile_cons, word, ih]
    · simp [word]

private theorem scan_sound (fuel : Nat) (chars : List Char) (tokens : List String)
    (accepted : scan fuel chars = .ok tokens) : Tokens chars tokens := by
  induction fuel generalizing chars tokens with
  | zero =>
    cases chars with
    | nil =>
      simp [scan] at accepted
      subst tokens
      exact .empty
    | cons head tail => simp [scan] at accepted
  | succ fuel ih =>
    cases chars with
    | nil =>
      simp [scan] at accepted
      subst tokens
      exact .empty
    | cons head tail =>
      by_cases space : whitespace head
      · exact .space space (ih tail tokens (by simpa [scan, space] using accepted))
      · have notSpace := Bool.eq_false_iff.mpr space
        by_cases word : word_char head
        · cases scanned : scan fuel (tail.dropWhile word_char) with
          | error reason => simp [scan, space, word, scanned, bind, Except.bind] at accepted
          | ok rest =>
            simp [scan, space, word, scanned, bind, Except.bind, pure, Except.pure] at accepted
            subst tokens
            have boundary : word_boundary (tail.dropWhile word_char) := by
              unfold word_boundary
              cases found : (tail.dropWhile word_char).head? with
              | none => trivial
              | some char => simpa only [found] using List.head?_dropWhile_not word_char tail
            simpa only [List.cons_append, List.takeWhile_append_dropWhile] using
              Tokens.word notSpace word (word_prefix tail) boundary (ih _ rest scanned)
        · have notWord := Bool.eq_false_iff.mpr word
          by_cases compound : doubled head tail
          · simp [scan, space, word, compound] at accepted
          · have notCompound := Bool.eq_false_iff.mpr compound
            by_cases symbol : punctuation head
            · cases scanned : scan fuel tail with
              | error reason => simp [scan, space, word, compound, symbol, scanned, bind, Except.bind] at accepted
              | ok rest =>
                simp [scan, space, word, compound, symbol, scanned, bind, Except.bind, pure, Except.pure] at accepted
                subst tokens
                exact .symbol notSpace notWord notCompound symbol (ih tail rest scanned)
            · simp [scan, space, word, compound, symbol] at accepted

private theorem word_split (boundary : word_boundary tail) :
    tail.takeWhile word_char = [] ∧ tail.dropWhile word_char = tail := by
  cases tail with
  | nil => exact ⟨rfl, rfl⟩
  | cons head rest =>
    change word_char head = false at boundary
    simp [boundary]

private theorem scan_complete (derives : Tokens chars tokens) (fuel : Nat) (enough : chars.length ≤ fuel) :
    scan fuel chars = .ok tokens := by
  induction derives generalizing fuel with
  | empty => cases fuel <;> rfl
  | space space _ ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel => simp [scan, space, ih fuel (by simpa using enough)]
  | word space word letters boundary _ ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      obtain ⟨noMore, rest⟩ := word_split boundary
      have scanned := ih fuel (by simp at enough; omega)
      simp [scan, space, word, List.takeWhile_append_of_pos letters, List.dropWhile_append_of_pos letters,
        noMore, rest, scanned, bind, Except.bind, pure, Except.pure]
  | symbol space word compound symbol _ ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      simp [scan, space, word, compound, symbol, ih fuel (by simpa using enough), bind, Except.bind, pure, Except.pure]

theorem tokenize_correct (input : String) (tokens : List String) :
    tokenize input = .ok tokens ↔ Tokens input.toList tokens :=
  ⟨scan_sound _ _ _, fun derives => scan_complete derives _ (by simp [String.length])⟩

private def digit (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (10 + char.toNat - 'a'.toNat)
  else if 'A' ≤ char && char ≤ 'F' then some (10 + char.toNat - 'A'.toNat)
  else none

private def digits (base : Nat) (text : List Char) : Option Nat := do
  guard (!text.isEmpty)
  text.foldlM (fun word char => do
    let next ← digit char
    guard (next < base)
    return word * base + next) 0

def literal (token : String) : Option Nat := do
  let last :: previous :: reversed := token.toList.reverse | none
  let unsign := fun c : Char => c == 'u' || c == 'U'
  let long := fun c : Char => c == 'l' || c == 'L'
  guard ((unsign last && long previous) || (long last && unsign previous))
  let raw ← match reversed.reverse with
    | '0' :: 'x' :: rest | '0' :: 'X' :: rest => digits 16 rest
    | '0' :: rest@(_ :: _) => digits 8 rest
    | text => digits 10 text
  guard (raw < 18446744073709551616)
  return raw

def operator : String → Option Operator
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | "&" => some .band
  | "|" => some .bor
  | "^" => some .bxor
  | _ => none

inductive ExpressionSyntax : List String → Source → Prop where
  | number : literal token = some value → ExpressionSyntax [token] (.constant value)
  | group : ExpressionSyntax text expression → ExpressionSyntax ("(" :: text ++ [")"]) expression
  | binary : operator token = some op → ExpressionSyntax left lhs → ExpressionSyntax right rhs →
      ExpressionSyntax ("(" :: left ++ [token] ++ right ++ [")"]) (.binary op lhs rhs)
  | conditional : ExpressionSyntax condition tested → ExpressionSyntax yes chosen → ExpressionSyntax no alternative →
      ExpressionSyntax ("(" :: condition ++ ["?"] ++ yes ++ [":"] ++ no ++ [")"]) (.conditional tested chosen alternative)

private def parse_expression : Nat → List String → Except String (Source × List String)
  | 0, _ => .error "incomplete C expression"
  | fuel + 1, "(" :: rest => do
    let (left, tail) ← parse_expression fuel rest
    match tail with
    | ")" :: remaining => pure (left, remaining)
    | "?" :: right => do
      let (yes, separator) ← parse_expression fuel right
      match separator with
      | ":" :: alternative => do
        let (no, endGroup) ← parse_expression fuel alternative
        match endGroup with
        | ")" :: remaining => pure (.conditional left yes no, remaining)
        | _ => throw "expected closing parenthesis after C conditional"
      | _ => throw "expected colon in C conditional"
    | token :: right => do
      let some op := operator token | throw "expected a closed C operator"
      let (rhs, endGroup) ← parse_expression fuel right
      match endGroup with
      | ")" :: remaining => pure (.binary op left rhs, remaining)
      | _ => throw "expected closing parenthesis after C binary expression"
    | [] => throw "unterminated C parenthesis"
  | _ + 1, token :: rest =>
    match literal token with
    | none => .error "expected an unsigned long integer literal"
    | some value => .ok (.constant value, rest)
  | _ + 1, [] => .error "missing C expression"

private theorem parse_expression_sound (fuel : Nat) (input remaining : List String) (body : Source)
    (accepted : parse_expression fuel input = .ok (body, remaining)) :
    ∃ text, input = text ++ remaining ∧ ExpressionSyntax text body := by
  induction fuel generalizing input remaining body with
  | zero => simp [parse_expression] at accepted
  | succ fuel ih =>
    cases input with
    | nil => simp [parse_expression] at accepted
    | cons token rest =>
      by_cases opening : token = "("
      · subst token
        cases first : parse_expression fuel rest with
        | error reason => simp [parse_expression, first, bind, Except.bind] at accepted
        | ok result =>
          obtain ⟨left, tail⟩ := result
          obtain ⟨leftText, leftSplit, leftSyntax⟩ := ih rest tail left first
          cases tail with
          | nil => simp [parse_expression, first, bind, Except.bind] at accepted
          | cons token right =>
            by_cases close : token = ")"
            · subst token
              simp [parse_expression, first, bind, Except.bind, pure, Except.pure] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact ⟨"(" :: leftText ++ [")"], by simp [leftSplit, List.append_assoc], .group leftSyntax⟩
            · by_cases choice : token = "?"
              · subst token
                cases second : parse_expression fuel right with
                | error reason => simp [parse_expression, first, second, bind, Except.bind] at accepted
                | ok chosen =>
                  obtain ⟨yes, separator⟩ := chosen
                  obtain ⟨yesText, yesSplit, yesSyntax⟩ := ih right separator yes second
                  cases separator with
                  | nil => simp [parse_expression, first, second, bind, Except.bind] at accepted
                  | cons colon alternative =>
                    by_cases separated : colon = ":"
                    · subst colon
                      cases third : parse_expression fuel alternative with
                      | error reason => simp [parse_expression, first, second, third, bind, Except.bind] at accepted
                      | ok other =>
                        obtain ⟨no, endGroup⟩ := other
                        obtain ⟨noText, noSplit, noSyntax⟩ := ih alternative endGroup no third
                        cases endGroup with
                        | nil => simp [parse_expression, first, second, third, bind, Except.bind] at accepted
                        | cons endToken after =>
                          by_cases closed : endToken = ")"
                          · subst endToken
                            simp [parse_expression, first, second, third, bind, Except.bind, pure, Except.pure] at accepted
                            obtain ⟨rfl, rfl⟩ := accepted
                            refine ⟨"(" :: leftText ++ ["?"] ++ yesText ++ [":"] ++ noText ++ [")"], ?_,
                              .conditional leftSyntax yesSyntax noSyntax⟩
                            simp [leftSplit, yesSplit, noSplit, List.append_assoc]
                          · simp [parse_expression, first, second, third, bind, Except.bind, closed] at accepted
                    · simp [parse_expression, first, second, bind, Except.bind, separated] at accepted
              · cases found : operator token with
                | none => simp [parse_expression, first, bind, Except.bind, found] at accepted
                | some op =>
                  cases second : parse_expression fuel right with
                  | error reason => simp [parse_expression, first, second, bind, Except.bind, found] at accepted
                  | ok result =>
                    obtain ⟨rhs, endGroup⟩ := result
                    obtain ⟨rightText, rightSplit, rightSyntax⟩ := ih right endGroup rhs second
                    cases endGroup with
                    | nil => simp [parse_expression, first, second, bind, Except.bind, found] at accepted
                    | cons endToken after =>
                      by_cases closed : endToken = ")"
                      · subst endToken
                        simp [parse_expression, first, second, bind, Except.bind, pure, Except.pure, found] at accepted
                        obtain ⟨rfl, rfl⟩ := accepted
                        refine ⟨"(" :: leftText ++ [token] ++ rightText ++ [")"], ?_, .binary found leftSyntax rightSyntax⟩
                        simp [leftSplit, rightSplit, List.append_assoc]
                      · simp [parse_expression, first, second, bind, Except.bind, found, closed] at accepted
      · cases value : literal token with
        | none => simp [parse_expression, value] at accepted
        | some word =>
          simp [parse_expression, value] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact ⟨[token], rfl, .number value⟩

private theorem parse_expression_complete (phrase : ExpressionSyntax tokens body) (rest : List String)
    (fuel : Nat) (enough : tokens.length ≤ fuel) :
    parse_expression fuel (tokens ++ rest) = .ok (body, rest) := by
  induction phrase generalizing rest fuel with
  | number decoded =>
    rename_i token value
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have ordinary : token ≠ "(" := by
        intro same
        subst token
        contradiction
      simp [parse_expression, decoded]
  | group inner ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      simp only [List.cons_append, List.append_assoc]
      simp [parse_expression, ih _ fuel (by simp at enough; omega), bind, Except.bind, pure, Except.pure]
  | binary decoded left right ihLeft ihRight =>
    rename_i token op leftTokens lhs rightTokens rhs
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have notClose : token ≠ ")" := by intro same; subst token; contradiction
      have notChoice : token ≠ "?" := by intro same; subst token; contradiction
      have leftOk := ihLeft (token :: rightTokens ++ ")" :: rest) fuel (by simp at enough; omega)
      have rightOk := ihRight (")" :: rest) fuel (by simp at enough; omega)
      simp only [List.cons_append, List.append_assoc]
      simp only [List.cons_append] at leftOk
      simp [parse_expression, bind, Except.bind, pure, Except.pure, leftOk, rightOk, decoded]
  | conditional test chosen alternative ihTest ihChosen ihAlternative =>
    rename_i testTokens tested chosenTokens yes alternativeTokens no
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have testOk := ihTest ("?" :: chosenTokens ++ ":" :: alternativeTokens ++ ")" :: rest) fuel (by simp at enough; omega)
      have chosenOk := ihChosen (":" :: alternativeTokens ++ ")" :: rest) fuel (by simp at enough; omega)
      have alternativeOk := ihAlternative (")" :: rest) fuel (by simp at enough; omega)
      simp only [List.cons_append, List.append_assoc]
      simp only [List.cons_append, List.append_assoc] at testOk chosenOk
      simp [parse_expression, bind, Except.bind, pure, Except.pure, testOk, chosenOk, alternativeOk]

private def header : List String := ["int", "main", "(", "void", ")", "{", "return", "(", "int", ")"]

def ProgramSyntax (tokens : List String) (body : Source) : Prop :=
  ∃ expression, tokens = header ++ expression ++ [";", "}"] ∧ ExpressionSyntax expression body

def parse (input : String) : Except String Source := do
  let tokens ← tokenize input
  unless tokens.take header.length == header do
    throw "expected int main(void) with an explicitly cast return"
  let (body, remaining) ← parse_expression (tokens.length + 1) (tokens.drop header.length)
  unless remaining == [";", "}"] do throw "expected the end of the closed C main definition"
  return body

theorem parse_sound (input : String) (body : Source) (accepted : parse input = .ok body) :
    ∃ tokens, tokenize input = .ok tokens ∧ ProgramSyntax tokens body := by
  cases scanned : tokenize input with
  | error why => simp [parse, scanned, bind, Except.bind] at accepted
  | ok tokens =>
    by_cases starts : tokens.take header.length = header
    · cases decoded : parse_expression (tokens.length + 1) (tokens.drop header.length) with
      | error why => simp [parse, scanned, starts, decoded, bind, Except.bind, pure, Except.pure] at accepted
      | ok result =>
        obtain ⟨expression, remaining⟩ := result
        by_cases complete : remaining = [";", "}"]
        · simp [parse, scanned, starts, decoded, complete, bind, Except.bind, pure, Except.pure] at accepted
          subst expression
          obtain ⟨code, suffix, derives⟩ := parse_expression_sound _ _ _ _ decoded
          refine ⟨tokens, rfl, code, ?_, derives⟩
          rw [complete] at suffix
          rw [← List.take_append_drop header.length tokens, starts, suffix, List.append_assoc]
        · simp [parse, scanned, starts, decoded, complete, bind, Except.bind, pure, Except.pure] at accepted
    · simp [parse, scanned, starts, bind, Except.bind] at accepted

theorem parse_complete (input : String) (tokens : List String) (body : Source)
    (lexed : tokenize input = .ok tokens) (program : ProgramSyntax tokens body) : parse input = .ok body := by
  obtain ⟨expression, rfl, derived⟩ := program
  have enough : expression.length ≤ (header ++ expression ++ [";", "}"]).length + 1 := by
    simp [List.length_append]
    omega
  have decoded := parse_expression_complete derived [";", "}"] ((header ++ expression ++ [";", "}"]).length + 1) enough
  simp only [parse, lexed, bind, Except.bind, List.append_assoc, List.take_left, beq_self_eq_true,
    List.drop_left, List.length_append, List.length_cons, List.length_nil] at decoded ⊢
  simp [decoded, pure, Except.pure]

theorem parse_correct (input : String) (body : Source) :
    parse input = .ok body ↔ ∃ tokens, Tokens input.toList tokens ∧ ProgramSyntax tokens body := by
  constructor
  · intro accepted
    obtain ⟨tokens, lexed, syntaxProof⟩ := parse_sound input body accepted
    exact ⟨tokens, (tokenize_correct input tokens).mp lexed, syntaxProof⟩
  · rintro ⟨tokens, lexed, syntaxProof⟩
    exact parse_complete input tokens body ((tokenize_correct input tokens).mpr lexed) syntaxProof

end Heresy.Surface

#print axioms Heresy.Surface.parse_correct
