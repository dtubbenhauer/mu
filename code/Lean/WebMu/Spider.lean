import WebMu.Laurent

namespace WebMu
open Laurent

/-! Words use A=0, B=1, C=2. An upward tensor is a sparse coordinate map.
    Growth strings are read downwards; their maps are composed in reverse.
    All coefficients below are the elementary tables in the draft. -/
abbrev Word := List Nat
abbrev Tensor := Std.HashMap Word Laurent
abbrev Column := Std.HashMap (Nat × Nat) Laurent

def accumulate [BEq α] [Hashable α] (values : Std.HashMap α Laurent)
    (key : α) (value : Laurent) : Std.HashMap α Laurent :=
  let result := Laurent.add (values.getD key []) value
  if result.isEmpty then values.erase key else values.insert key result

def singleton (word : Word) (value : Laurent := one) : Tensor :=
  (∅ : Tensor).insert word value

inductive Op where
  | y | h | cup | lam | sigma
  deriving Repr, BEq, DecidableEq

abbrev Step := Op × Nat

def arity : Op → Nat
  | .y => 1
  | .cup => 0
  | _ => 2

def localTerms : Op → Word → List (Word × Laurent)
  | .y, [0] => [([0,1], one), ([1,0], monomial (-1))]
  | .y, [1] => [([0,2], one), ([2,0], monomial (-1))]
  | .y, [2] => [([1,2], one), ([2,1], monomial (-1))]
  | .cup, [] => [([0,2], one), ([1,1], monomial (-1)), ([2,0], monomial (-2))]
  | .sigma, [0,2] => [([], monomial 2)]
  | .sigma, [1,1] => [([], monomial 1)]
  | .sigma, [2,0] => [([], one)]
  | .lam, [a,b] =>
    if a == b || a > 2 || b > 2 then []
    else [([a + b - 1], monomial (if a < b then 1 else 0))]
  | .h, [0,0] => [([0,0], one)]
  | .h, [0,1] => [([1,0], one)]
  | .h, [0,2] => [([0,2], monomial 1), ([1,1], one)]
  | .h, [1,0] => [([0,1], one)]
  | .h, [1,1] => [([0,2], one), ([2,0], one)]
  | .h, [1,2] => [([2,1], one)]
  | .h, [2,0] => [([1,1], one), ([2,0], monomial (-1))]
  | .h, [2,1] => [([1,2], one)]
  | .h, [2,2] => [([2,2], one)]
  | _, _ => []

def applyStep (values : Tensor) (step : Step) : Tensor := Id.run do
  let mut result : Tensor := ∅
  let (op, i) := step
  for (word, p) in values do
    if i + arity op ≤ word.length then
      for (replacement, q) in localTerms op ((word.drop i).take (arity op)) do
        result := accumulate result (word.take i ++ replacement ++ word.drop (i + arity op))
          (mul p q)
  return result

def compose (steps : List Step) (values : Tensor) : Tensor :=
  steps.foldl applyStep values

def expand (downward : List Step) (values : Tensor) : Tensor :=
  compose downward.reverse values

def tensorProduct (left right : Tensor) : Tensor := Id.run do
  let mut result : Tensor := ∅
  for (u, p) in left do
    for (w, q) in right do
      result := accumulate result (u ++ w) (mul p q)
  return result

def encode (word : Word) : Nat := word.foldl (fun n a => 3*n+a) 0

def triple (i : Nat) : Word := [i / 9, i / 3 % 3, i % 3]

def tripod : Tensor :=
  [([0,1,2], one), ([0,2,1], monomial (-1)), ([1,0,2], monomial (-1)),
   ([1,2,0], monomial (-2)), ([2,0,1], monomial (-2)), ([2,1,0], monomial (-3))]
    |>.foldl (fun m (w,p) => accumulate m w p) ∅

def tau2 : Tensor := tensorProduct tripod tripod
def tau3 : Tensor := tensorProduct tripod tau2

open Op in
def prefixSteps : List Step := [(y,0),(y,3),(y,4),(cup,4),(h,2),(h,1),(y,0)]

open Op in
def blockSteps : List Step :=
  [(y,2),(y,6),(y,7),(h,2),(y,1),(h,2),(h,1),(y,0),(h,3),
   (y,2),(h,3),(y,4),(h,2),(y,1),(h,2),(h,1),(y,0)]

open Op in
def tailSteps : List Step := [(y,2),(y,3),(y,2),(y,1),(y,2),(y,1),(y,0),(cup,0)]

open Op in
def correctionSteps : List (List Step × List Step) := [
  (prefixSteps, []),
  ([(y,0),(y,3),(y,4),(y,3),(y,2),(h,1),(y,0)], []),
  ([(y,0),(y,2),(cup,2),(y,2),(h,1),(y,0),(y,1)], [(lam,1)]),
  ([(y,0),(y,1),(y,2),(y,1),(y,2),(h,1),(y,0),(y,1)], [(lam,0),(y,0),(lam,1)]),
  ([(y,0),(y,1),(y,0),(y,1),(y,2),(y,1),(y,1)], [(lam,1)]),
  ([(y,0),(cup,0),(y,1),(y,2),(y,1),(y,1)], [(lam,0),(y,0),(lam,1)]),
  ([(y,0),(cup,0),(y,0),(cup,0),(y,0)], [(lam,0)]),
  ([(y,0),(cup,0),(y,0),(cup,0),(y,0),(cup,0)], [(lam,0),(sigma,0)])]

open Op in
def cSteps : List Step := [(y,2),(y,6),(y,7),(h,2),(y,1)]

def fourCups : Tensor :=
  let cup := compose [(.cup,0)] (singleton [])
  tensorProduct (tensorProduct cup cup) (tensorProduct cup cup)

def splitColumn (values : Tensor) : Column :=
  values.fold (fun out word p => accumulate out (encode (word.take 3), encode (word.drop 3)) p) ∅

/-- The 28 columns of T=[B,-C; D,-[2]tau^3], constructed without K. -/
def blockColumn (i : Nat) : Column := Id.run do
  if i < 27 then
    let input := singleton (triple i)
    let mut result := splitColumn (expand blockSteps input)
    for (growth, smallMap) in correctionSteps do
      for (word, p) in expand growth (compose smallMap input) do
        result := accumulate result (27, encode word) p
    return result
  else if i == 27 then
    let mut result := splitColumn (expand cSteps fourCups)
    result := result.fold (fun acc key p => accumulate acc key (neg p)) ∅
    for (word, p) in tau3 do
      result := accumulate result (27, encode word) (neg (mul (add (monomial 1) (monomial (-1))) p))
    return result
  else return ∅

def prefixColumn (i : Nat) : Column :=
  if i < 27 then (expand prefixSteps (singleton (triple i))).fold
    (fun result word p => accumulate result (0, encode word) p) ∅
  else ∅

def tailColumn : Column := Id.run do
  let mut result := splitColumn (expand tailSteps (singleton []))
  for (word,p) in tau2 do
    result := accumulate result (27, encode word) p
  return result

/-- Downward signed boundaries. Invalid strings are rejected, not truncated. -/
def descendSigns (signs : List Bool) (step : Step) : Option (List Bool) := do
  let (op,i) := step
  let a ← signs[i]?
  let b ← signs[i+1]?
  let new ← match op with
    | .y => if a == b then some [!a] else none
    | .h => if a != b then some [b,a] else none
    | .cup => if a != b then some [] else none
    | _ => none
  return signs.take i ++ new ++ signs.drop (i+2)

def inputSigns (n : Nat) (steps : List Step) : Option (List Bool) :=
  steps.foldlM descendSigns (List.replicate n true)

end WebMu
