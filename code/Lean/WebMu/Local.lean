import WebMu.Spider
import WebMu.TransferData

namespace WebMu
open Laurent

abbrev SmallMatrix := Array Laurent

def entry (matrix : SmallMatrix) (i j : Nat) : Laurent := matrix[i*28+j]!

def smallMatrix (f : Nat → Nat → Laurent) : SmallMatrix :=
  (List.range 784).toArray.map fun ij => f (ij/28) (ij%28)

def productMatrix (left right : SmallMatrix) : SmallMatrix :=
  smallMatrix fun i j => (List.range 28).foldl
    (fun acc k => add acc (mul (entry left i k) (entry right k j))) []

def eMatrix (position : Nat) : SmallMatrix := smallMatrix fun i j =>
  if i < 27 && j < 27 then
    (compose [(.lam,position),(.y,position)] (singleton (triple j))).getD (triple i) []
  else []

def etaEntry (i : Nat) : Laurent :=
  if i < 27 then shiftScale (tripod.getD (triple i) []) 3 1 else monomial 1 (-1)

/-- The seven matrices (v E2, E1 E2+E2 E1, ZZ^T, I, v E1, v^2 M, I_1). -/
def gramBasis : Array SmallMatrix := Id.run do
  let e1 := eMatrix 0
  let e2 := eMatrix 1
  let e12 := productMatrix e1 e2
  let e21 := productMatrix e2 e1
  return #[e2.map (fun p => shiftScale p 1 1),
    smallMatrix (fun i j => add (entry e12 i j) (entry e21 i j)),
    smallMatrix (fun i j => mul (etaEntry i) (etaEntry j)),
    smallMatrix (fun i j => if i == j && i < 27 then one else []),
    e1.map (fun p => shiftScale p 1 1),
    smallMatrix (fun i j =>
      if i == 27 && j < 27 then shiftScale (tripod.getD (triple j) []) 2 1
      else if j == 27 && i < 27 then shiftScale (tripod.getD (triple i) []) 2 1
      else []),
    smallMatrix (fun i j => if i == 27 && j == 27 then one else [])]

def initialData : Array Laurent :=
  let s := monomial (-2)
  let alpha := add one s
  let gamma := add alpha (monomial (-4))
  let factor := mul (pow alpha 3) gamma
  #[s, [], monomial (-4), alpha, s, s, neg s].map (mul factor)

def terminalData : Array Laurent :=
  let s := monomial (-2)
  let alpha := add one s
  let gamma := add alpha (monomial (-4))
  let factor := mul (pow alpha 2) gamma
  #[shiftScale (pow alpha 4) 0 2,
    shiftScale (pow alpha 3) (-2) 8,
    add (add (add one (monomial (-2) 5)) (monomial (-4) 4)) (monomial (-6)),
    pow alpha 5, shiftScale (pow alpha 4) 0 2,
    shiftScale (pow alpha 3) 0 2, gamma].map (mul factor)

def constantK : Array Int := #[
  4,0,4,0,4,4,2, 6,1,7,0,8,9,4, 0,0,0,0,1,2,1,
  5,0,4,1,5,4,2, 3,0,3,0,5,6,3, 4,1,8,0,10,16,7,
  -5,-2,-10,0,-16,-26,-11]

def constantA : Array Int := #[0,0,0,1,0,0,0]
def constantB : Array Int := #[2,0,1,1,2,2,1]

def pairColumns (left right : Column) (matrix : SmallMatrix) : Laurent := Id.run do
  let supports := (List.range 28).toArray.map fun i =>
    (List.range 28).filterMap fun k =>
      let p := entry matrix i k
      if p.isEmpty then none else some (k,p)
  let mut result : Laurent := []
  for ((i,word),p) in left do
    for (k,s) in supports[i]! do
      if let some q := right.get? (k,word) then
        result := add result (mul (mul p s) q)
  return result

def expectedTransfer (basis : Array SmallMatrix) (j left right : Nat) : Laurent :=
  (List.range 7).foldl (fun acc i =>
    add acc (mul transferData[i*7+j]! (entry basis[i]! left right))) []

def expectedInitial (basis : Array SmallMatrix) (left right : Nat) : Laurent :=
  (List.range 7).foldl (fun acc i =>
    add acc (mul initialData[i]! (entry basis[i]! left right))) []

/-- The full, untruncated contractions, with all 28 x 28 coordinates retained. -/
def actualTransfer : Array SmallMatrix :=
  let columns := (List.range 28).toArray.map blockColumn
  gramBasis.map fun matrix => smallMatrix fun i j => pairColumns columns[i]! columns[j]! matrix

def predictedTransfer : Array SmallMatrix :=
  let basis := gramBasis
  (List.range 7).toArray.map fun j => smallMatrix (expectedTransfer basis j)

def actualInitial : SmallMatrix :=
  let columns := (List.range 28).toArray.map prefixColumn
  let identity := smallMatrix fun i j => if i == j then one else []
  smallMatrix fun i j => pairColumns columns[i]! columns[j]! identity

def predictedInitial : SmallMatrix := smallMatrix (expectedInitial gramBasis)

def actualTerminal : Array Laurent :=
  let tail := tailColumn
  gramBasis.map (pairColumns tail tail)

/-- Diagnostics retain mismatches, rather than silently accepting a partial check. -/
def localFailures : List String := Id.run do
  let basis := gramBasis
  let columns := (List.range 28).toArray.map blockColumn
  let prefixes := (List.range 28).toArray.map prefixColumn
  let tail := tailColumn
  let mut failures := []
  for j in [:7] do
    for left in [:28] do
      for right in [:28] do
        let actual := pairColumns columns[left]! columns[right]! basis[j]!
        let expected := expectedTransfer basis j left right
        if actual != expected then
          failures := s!"N(X{j})[{left},{right}]: {repr actual} != {repr expected}" :: failures
    let actual := pairColumns tail tail basis[j]!
    if actual != terminalData[j]! then
      failures := s!"terminal[{j}]: {repr actual} != {repr terminalData[j]!}" :: failures
  let identity := smallMatrix fun i j => if i == j then one else []
  for left in [:28] do
    for right in [:28] do
      let actual := pairColumns prefixes[left]! prefixes[right]! identity
      let expected := expectedInitial basis left right
      if actual != expected then
        failures := s!"initial[{left},{right}]: {repr actual} != {repr expected}" :: failures
  return failures.reverse

def integralityAndConstants : Bool :=
  transferData.size == 49 && initialData.size == 7 && terminalData.size == 7 &&
  transferData.all integralEven && initialData.all integralEven && terminalData.all integralEven &&
  transferData.map (fun p => coeff p 0) == constantK &&
  initialData.map (fun p => coeff p 0) == constantA &&
  terminalData.map (fun p => coeff p 0) == constantB

def growthTypes : Bool :=
  inputSigns 9 prefixSteps == some [true,true,true] &&
  inputSigns 12 blockSteps == some [true,true,true] &&
  inputSigns 9 tailSteps == some [] &&
  inputSigns 12 cSteps == some [true,false,false,true,true,false,false,true] &&
  (correctionSteps.map fun (steps,_) => inputSigns 9 steps) ==
    [some [true,true,true],some [true,true,true],some [true,false],some [true,false],
     some [true,false],some [true,false],some [false,true],some []]

def wordY : Word := [0,1,0,0,0,2,0,1,2]
def wordU : Word := [1,1,1,0,0,2,0,2,2]
def wordV : Word := [1,1,2,1,2,2]

def leadingEntries : Bool :=
  (List.range 28).all (fun i => (prefixColumn i).getD (0,encode wordY) [] ==
    (if i == 0 then one else [])) &&
  (List.range 28).all (fun i => (blockColumn 0).getD (i,encode wordU) [] ==
    (if i == 0 then one else [])) &&
  tailColumn.getD (0,encode wordV) [] == one

end WebMu
