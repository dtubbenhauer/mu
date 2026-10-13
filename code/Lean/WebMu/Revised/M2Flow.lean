import WebMu.Spider
import WebMu.Revised.Family

/-! Exact boundary contraction of certified growth strings using the same local
Spider.localTerms tables as the corrected-family proof. States are A=0,B=1,C=2.
-/
namespace WebMu.Revised.M2Flow
open Laurent

def words : Nat → List Word
  | 0 => [[]]
  | n+1 => (List.range 3).flatMap (fun a => (words n).map (fun w => a::w))

def upperArity : Op → Nat
  | .lam => 1
  | .sigma => 0
  | _ => 2

/-- The transpose of the upward local tensor table, used for downward contraction. -/
def downwardTerms (op : Op) (upper : Word) : List (Word × Laurent) :=
  (words (arity op)).flatMap (fun lower =>
    (localTerms op lower).filterMap (fun (u,p) => if u=upper then some (lower,p) else none))

def downwardStep (values : Tensor) (step : Step) : Tensor := Id.run do
  let (op,i) := step
  let mut result : Tensor := ∅
  for (word,p) in values do
    if i+upperArity op ≤ word.length then
      for (lower,q) in downwardTerms op ((word.drop i).take (upperArity op)) do
        result := accumulate result (word.take i ++ lower ++ word.drop (i+upperArity op)) (mul p q)
  return result

def contract (steps : List Step) (boundary : Word) : Laurent :=
  ((steps.foldl downwardStep (singleton boundary)).getD [] [])

def canonicalBelow : Op → Word → Option Word
  | .y, [0,1] => some [0]
  | .y, [0,2] => some [1]
  | .y, [1,2] => some [2]
  | .cup, [0,2] => some []
  | .h, [0,1] => some [1,0]
  | .h, [1,1] => some [2,0]
  | .h, [1,2] => some [2,1]
  | _, _ => none

def canonicalStep (state : Word × List Bool) (step : Step) : Option (Word × List Bool) := do
  let (word,signs) := state
  let (op,i) := step
  if i+2 > word.length then none else do
    let signs' ← descendSigns signs step
    let replacement ← canonicalBelow op ((word.drop i).take 2)
    return (word.take i ++ replacement ++ word.drop (i+2), signs')

def validGrowth (word : Word) (steps : List Step) : Bool :=
  steps.foldlM canonicalStep (word,List.replicate word.length true) == some ([],[])

structure Entry where
  word : Word
  steps : List Step
  sourceCoordinate : Laurent
  isLaurent : Bool
  deriving Repr, Inhabited

/-- Every exported growth string must independently reduce its claimed word. -/
def entryGrowthValid (e : Entry) : Bool := validGrowth e.word e.steps

/-- Expected polynomials are checked by evaluating the actual local contractions. -/
def entryCoordinateValid (source : Word) (e : Entry) : Bool :=
  contract e.steps source == e.sourceCoordinate

end WebMu.Revised.M2Flow
