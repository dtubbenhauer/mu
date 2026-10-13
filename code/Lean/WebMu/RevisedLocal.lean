import WebMu.Spider
import Std.Data.HashMap.Lemmas

/-! Exact finite local calculations for the shortened manuscript construction.
    Coefficients are in Z[v,v⁻¹]; t=v⁻¹. Words have A=0,B=1,C=2,
    left-to-right tensor order. Interface states 0,...,26 are lexicographic
    triples and 27 is the scalar summand. No paper-specific axiom occurs here.
    Large finite computations use `native_decide`; their compiler trust is
    separately reported by `#print axioms` in the audit entry point. -/
namespace WebMu.Revised
open Laurent

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Op in
def shortPrefixSteps : List Step := [(y,0),(y,3),(h,2),(h,1),(y,0)]

open Op in
def sSteps : List Step := [(h,2),(h,1),(y,0)]

open Op in
def middleSteps : List Step := [(h,3),(y,2),(h,3),(y,4),(h,2),(y,1)]

def innerSteps : List Step := sSteps ++ middleSteps ++ sSteps

open Op in
def hSteps : List (List Step × List Step) := [
  ([(y,1),(y,3),(y,4),(cup,4),(h,2),(y,1)], []),
  ([(y,1),(y,3),(y,4),(y,3),(y,2),(y,1)], []),
  ([(y,1),(y,2),(cup,2),(y,2),(y,1),(y,1)], [(lam,1)]),
  ([(y,1),(y,3),(y,4),(h,1),(y,0),(y,1),(h,1),(y,0),(y,1)],
    [(lam,0),(y,0),(lam,1)]),
  ([(y,1),(cup,1),(y,1),(y,2),(y,1),(y,1)], [(lam,1)]),
  ([(y,0),(y,3),(y,4),(y,3),(y,3),(h,2),(h,1),(y,0)], []),
  ([(y,0),(y,2),(cup,2),(y,2),(cup,2)], [(lam,1),(y,1),(lam,0)]),
  ([(y,0),(y,2),(cup,2),(y,2),(h,1),(y,0)], []),
  ([(y,0),(y,1),(y,2),(y,1),(y,2),(cup,2)], [(lam,0)]),
  ([(y,0),(y,1),(y,2),(y,1),(y,2),(h,1),(y,0),(y,1)], [(lam,1)]),
  ([(y,0),(y,1),(y,2),(y,1),(y,1),(cup,1)], [(lam,0)])]

def height (i : Nat) : Int := if i = 5 ∨ i = 7 ∨ i = 11 then 1 else 0

def eta : Nat → Laurent
  | 5 => monomial 3
  | 7 | 11 => monomial 2
  | 15 | 19 => monomial 1
  | 21 => one
  | _ => []

def d : Laurent := add (monomial 1) (monomial (-1))

def shortPrefix (i : Nat) : Tensor :=
  if i < 27 then expand shortPrefixSteps (singleton (triple i)) else ∅

def rawB (i : Nat) : Tensor := expand blockSteps (singleton (triple i))
def rawC : Tensor := expand cSteps fourCups

def sumTensor (xs : List Tensor) : Tensor :=
  xs.foldl (fun out x => x.fold (fun acc w p => accumulate acc w p) out) ∅

def scaleTensor (x : Tensor) (q : Laurent) : Tensor :=
  x.fold (fun out w p => accumulate out w (mul p q)) ∅

def summand (s : List Step × List Step) (i : Nat) : Tensor :=
  expand s.1 (compose s.2 (singleton (triple i)))

def rawD (i : Nat) : Tensor := sumTensor (correctionSteps.map (fun s => summand s i))
def rawD₀ (i : Nat) : Tensor := sumTensor ((correctionSteps.take 7).map (fun s => summand s i))
def rawH (i : Nat) : Tensor := sumTensor (hSteps.map (fun s => summand s i))

def cap (x : Tensor) : Tensor :=
  x.fold (fun out w p => accumulate out (w.drop 3) (mul p (eta (encode (w.take 3))))) ∅

def rawQ : Tensor := expand tailSteps (singleton [])
def tailTree : Tensor := expand [(.y,1),(.y,2),(.y,1),(.y,0),(.cup,0)] (singleton [])

def g (i j : Nat) : Laurent :=
  if i < 27 then (if i = j then monomial (height i) else [])
  else if i = 27 then (if j < 27 then shiftScale (eta j) (-1) 1
    else if j = 27 then monomial 0 (-1) else []) else []

def ginv (i j : Nat) : Laurent :=
  if i < 27 then (if i = j then monomial (-height i) else [])
  else if i = 27 then (if j < 27 then shiftScale (eta j) (-1-height j) 1
    else if j = 27 then monomial 0 (-1) else []) else []

def matrixProduct (a b : Nat → Nat → Laurent) (i j : Nat) : Laurent :=
  (List.range 28).foldl (fun p k => add p (mul (a i k) (b k j))) []

/-- Sparse implementation of (G ⊗ I)x, retaining the exterior order. -/
def gLeft (x : Column) : Column :=
  x.fold (fun out (i,w) p =>
    if i < 27 then
      accumulate (accumulate out (i,w) (shiftScale p (height i) 1))
        (27,w) (mul p (shiftScale (eta i) (-1) 1))
    else accumulate out (27,w) (neg p)) ∅

def scaleColumn (x : Column) (q : Laurent) : Column :=
  x.fold (fun out w p => accumulate out w (mul p q)) ∅

def addColumn (x y : Column) : Column :=
  y.fold (fun out w p => accumulate out w p) x

def block : Nat → Column := blockColumn
def tail : Column := tailColumn

def prefixHat (i : Nat) : Tensor := scaleTensor (shortPrefix i) (monomial (-height i))

/-- Actual coordinate composition G T G⁻¹; the cap identity is not assumed. -/
def blockHat (i : Nat) : Column :=
  gLeft (if i < 27 then
    addColumn (scaleColumn (block i) (monomial (-height i)))
      (scaleColumn (block 27) (shiftScale (eta i) (-1-height i) 1))
    else scaleColumn (block 27) (monomial 0 (-1)))

def tailHat : Column := gLeft tail

/-- Canonical storage and exponent bound, with t=v⁻¹. -/
def bounded (bound : Int) (p : Laurent) : Bool :=
  canonical p && p.all (fun term => term.1 ≤ bound)

def allEntries [BEq α] [Hashable α] (x : Std.HashMap α Laurent)
    (p : α → Laurent → Bool) : Bool := x.toList.all (fun (k,v) => p k v)

def sameEntries [BEq α] [Hashable α] (x y : Std.HashMap α Laurent) : Bool :=
  allEntries x (fun k p => p == y.getD k []) &&
  allEntries y (fun k p => p == x.getD k [])

/-- A complete sparse support check gives a statement at every coordinate,
    including coordinates absent from storage. -/
theorem allEntries_getD {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (p : α → Laurent → Bool)
    (h : allEntries x p = true) (hz : ∀ k, p k [] = true) (k : α) :
    p k (x.getD k []) = true := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases he : x[k]? with
  | none => simpa using hz k
  | some v =>
    have hm : (k,v) ∈ x.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr he
    exact (List.all_eq_true.mp h) (k,v) hm

theorem sameEntries_getD {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x y : Std.HashMap α Laurent) (h : sameEntries x y = true) (k : α) :
    x.getD k [] = y.getD k [] := by
  have hh : allEntries x (fun k p => p == y.getD k []) = true ∧
      allEntries y (fun k p => p == x.getD k []) = true := by
    simpa [sameEntries] using h
  rw [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getD_eq_getD_getElem?]
  cases hx : x[k]? with
  | some a =>
    have hm : (k,a) ∈ x.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hx
    have he := (List.all_eq_true.mp hh.1) (k,a) hm
    simpa [Std.HashMap.getD_eq_getD_getElem?] using (beq_iff_eq.mp he)
  | none =>
    cases hy : y[k]? with
    | none => rfl
    | some b =>
      have hm : (k,b) ∈ y.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hy
      have he := (List.all_eq_true.mp hh.2) (k,b) hm
      have he' : b = [] := by simpa [Std.HashMap.getD_eq_getD_getElem?, hx] using (beq_iff_eq.mp he)
      simp [he']

def wordY : Word := [0,1,0,0,0,2]
def wordU : Word := [1,1,1,0,0,2,0,2,2]
def wordV : Word := [1,1,2,1,2,2]
def wordEnd : Word := [0,1,2,0,1,2]
def wordBlock : Word := [0,1,2,0,1,2,0,1,2]

def constantTensor (x : Tensor) : Tensor :=
  x.fold (fun out w p => accumulate out w (monomial 0 (coeff p 0))) ∅
def constantColumn (x : Column) : Column :=
  x.fold (fun out w p => accumulate out w (monomial 0 (coeff p 0))) ∅

def signedTypes : Bool :=
  inputSigns 6 shortPrefixSteps == some [true,true,true] &&
  inputSigns 12 blockSteps == some [true,true,true] &&
  inputSigns 9 tailSteps == some [] &&
  inputSigns 12 cSteps == some [true,false,false,true,true,false,false,true] &&
  (middleSteps.foldlM descendSigns [false,false,false,true,false,false,true]) ==
    some [false,true,true,false] &&
  (innerSteps.foldlM descendSigns [true,false,false,true,true,false,false,true]) ==
    some [true,true,true] &&
  (correctionSteps.map fun (steps,_) => inputSigns 9 steps) ==
    [some [true,true,true],some [true,true,true],some [true,false],some [true,false],
      some [true,false],some [true,false],some [false,true],some []] &&
  (hSteps.map fun (steps,_) => inputSigns 9 steps) ==
    [some [true,true,true],some [true,true,true],some [true,false],some [true,false],
      some [true,false],some [true,true,true],some [false,true],some [true,true,true],
      some [false,true],some [true,false],some [false,true]]

theorem signedTypes_verified : signedTypes = true := by decide

theorem g_left_inverse (i j : Fin 28) :
    matrixProduct ginv g i j = if i = j then one else [] := by
  revert i j
  native_decide

theorem g_right_inverse (i j : Fin 28) :
    matrixProduct g ginv i j = if i = j then one else [] := by
  revert i j
  native_decide

theorem eta_table (i : Fin 27) :
    eta i = shiftScale (tripod.getD (triple i) []) 3 1 := by
  revert i
  native_decide

theorem cap_B_check : ∀ i : Fin 27,
    sameEntries (cap (rawB i)) (sumTensor [scaleTensor (rawD i) d, rawH i]) = true := by
  native_decide

theorem cap_B (i : Fin 27) (w : Word) :
    (cap (rawB i)).getD w [] =
      (sumTensor [scaleTensor (rawD i) d, rawH i]).getD w [] :=
  sameEntries_getD _ _ (cap_B_check i) w

theorem cap_C_check :
    sameEntries (cap rawC) (scaleTensor tau3 (mul d d)) = true := by native_decide

theorem cap_C (w : Word) :
    (cap rawC).getD w [] = (scaleTensor tau3 (mul d d)).getD w [] :=
  sameEntries_getD _ _ cap_C_check w

theorem cap_Q_check :
    sameEntries (cap rawQ) (sumTensor [scaleTensor tau2 d, tailTree]) = true := by
  native_decide

theorem cap_Q (w : Word) :
    (cap rawQ).getD w [] = (sumTensor [scaleTensor tau2 d, tailTree]).getD w [] :=
  sameEntries_getD _ _ cap_Q_check w

theorem d₈_check : ∀ i : Fin 27,
    sameEntries (summand correctionSteps[7]! i) (scaleTensor tau3 (eta i)) = true := by
  native_decide

theorem d₈ (i : Fin 27) (w : Word) :
    (summand correctionSteps[7]! i).getD w [] = (scaleTensor tau3 (eta i)).getD w [] :=
  sameEntries_getD _ _ (d₈_check i) w

def prefixIntegralCheck : Bool := (List.range 28).all fun i =>
  allEntries (prefixHat i) (fun _ p => bounded 0 p)

def blockIntegralCheck : Bool := (List.range 28).all fun i =>
  allEntries (blockHat i) (fun _ p => bounded 0 p)

theorem prefix_integral_check : prefixIntegralCheck = true := by native_decide
theorem block_integral_check : blockIntegralCheck = true := by native_decide
theorem tail_integral_check : allEntries tailHat (fun _ p => bounded 0 p) = true := by
  native_decide

theorem prefix_integral (i : Fin 28) (w : Word) :
    bounded 0 ((prefixHat i).getD w []) = true := by
  have hi : i.val ∈ List.range 28 := List.mem_range.mpr i.isLt
  have h := List.all_eq_true.mp prefix_integral_check i.val hi
  exact allEntries_getD _ _ h (fun _ => rfl) w

theorem block_integral (i : Fin 28) (k : Nat × Nat) :
    bounded 0 ((blockHat i).getD k []) = true := by
  have hi : i.val ∈ List.range 28 := List.mem_range.mpr i.isLt
  have h := List.all_eq_true.mp block_integral_check i.val hi
  exact allEntries_getD _ _ h (fun _ => rfl) k

theorem tail_integral (k : Nat × Nat) : bounded 0 (tailHat.getD k []) = true :=
  allEntries_getD _ _ tail_integral_check (fun _ => rfl) k

/-- A single nonzero constant on the whole sparse support. -/
def singleConstant [BEq α] [Hashable α] (x : Std.HashMap α Laurent) (key : α) : Bool :=
  coeff (x.getD key []) 0 == 1 &&
    allEntries x (fun k p => coeff p 0 == 0 || (k == key && coeff p 0 == 1))

theorem singleConstant_getD {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (key : α) (h : singleConstant x key = true) (k : α) :
    coeff (x.getD k []) 0 = if k == key then 1 else 0 := by
  have hh : coeff (x.getD key []) 0 = 1 ∧
      allEntries x (fun k p => coeff p 0 == 0 || (k == key && coeff p 0 == 1)) = true := by
    simpa [singleConstant] using h
  have hp := allEntries_getD x _ hh.2 (fun _ => rfl) k
  have hp' : coeff (x.getD k []) 0 = 0 ∨
      (k = key ∧ coeff (x.getD k []) 0 = 1) := by simpa using hp
  by_cases hk : k = key
  · simpa [hk] using hh.1
  · have hz : coeff (x.getD k []) 0 = 0 := hp'.resolve_right (by simp [hk])
    simpa [hk] using hz

theorem prefix_leading_check : singleConstant (prefixHat 0) wordY = true := by native_decide
theorem block_leading_check : singleConstant (blockHat 0) (0,encode wordU) = true := by
  native_decide
theorem tail_leading_check : singleConstant tailHat (0,encode wordV) = true := by native_decide

theorem prefix_leading (w : Word) :
    coeff ((prefixHat 0).getD w []) 0 = if w == wordY then 1 else 0 :=
  singleConstant_getD _ _ prefix_leading_check w

theorem block_leading (k : Nat × Nat) :
    coeff ((blockHat 0).getD k []) 0 = if k == (0,encode wordU) then 1 else 0 :=
  singleConstant_getD _ _ block_leading_check k

theorem tail_leading (k : Nat × Nat) :
    coeff (tailHat.getD k []) 0 = if k == (0,encode wordV) then 1 else 0 :=
  singleConstant_getD _ _ tail_leading_check k

def selectedPrefix (i : Nat) : Laurent := (prefixHat i).getD wordEnd []
def selectedBlock (i j : Nat) : Laurent := (blockHat j).getD (i,encode wordBlock) []
def selectedTail (i : Nat) : Laurent := tailHat.getD (i,encode wordEnd) []

def expectedPrefix : Nat → Laurent
  | 5 => one
  | 7 | 11 => monomial (-1)
  | _ => []

def expectedTail : Nat → Laurent
  | 5 => monomial (-1)
  | 7 | 11 => monomial (-2)
  | 27 => monomial (-2) 2
  | _ => []

def expectedABCRow : Nat → Laurent
  | 5 => [(-3,6),(-1,6)]
  | 7 => [(-4,2),(-2,5)]
  | 11 => [(-4,3),(-2,5)]
  | 15 => [(-2,2)]
  | 19 => [(-2,1)]
  | 27 => one
  | _ => []

def expectedScalarRow : Nat → Laurent
  | 5 => [(-4,6),(-2,12),(0,2)]
  | 7 => [(-5,2),(-3,8),(-1,2)]
  | 11 => [(-5,3),(-3,10),(-1,2)]
  | 15 => [(-3,2),(-1,2)]
  | 19 => [(-3,2),(-1,1)]
  | 21 => [(-2,1)]
  | 27 => [(-3,1),(-1,1)]
  | _ => []

theorem selected_prefix (i : Fin 28) : selectedPrefix i = expectedPrefix i := by
  revert i
  native_decide

theorem selected_tail (i : Fin 28) : selectedTail i = expectedTail i := by
  revert i
  native_decide

theorem selected_ABC_row (i : Fin 28) : selectedBlock 5 i = expectedABCRow i := by
  revert i
  native_decide

theorem selected_scalar_row (i : Fin 28) : selectedBlock 27 i = expectedScalarRow i := by
  revert i
  native_decide

theorem selected_prefix_constant (i : Fin 28) :
    coeff (selectedPrefix i) 0 = if i.val = 5 then 1 else 0 := by
  rw [selected_prefix]
  revert i
  decide

theorem selected_tail_constant (i : Fin 28) : coeff (selectedTail i) 0 = 0 := by
  rw [selected_tail]
  revert i
  decide

theorem selected_tail_first (i : Fin 28) :
    coeff (selectedTail i) (-1) = if i.val = 5 then 1 else 0 := by
  rw [selected_tail]
  revert i
  decide

theorem selected_ABC_constant (i : Fin 28) :
    coeff (selectedBlock 5 i) 0 = if i.val = 27 then 1 else 0 := by
  rw [selected_ABC_row]
  revert i
  decide

theorem selected_scalar_constant (i : Fin 28) :
    coeff (selectedBlock 27 i) 0 = if i.val = 5 then 2 else 0 := by
  rw [selected_scalar_row]
  revert i
  decide

def wordsOfIndex : Nat → Nat → Word
  | 0, _ => []
  | n+1, i => i / 3^n :: wordsOfIndex n (i % 3^n)

/-- Retain precisely monomials exceeding the given v-degree. -/
def above (x : Tensor) (bound : Int) : Tensor :=
  x.fold (fun out w p => accumulate out w (p.filter (fun term => bound < term.1))) ∅

def sPositiveExpected (i : Nat) : Tensor :=
  if i = 5 then singleton [0,2,0,2] (monomial 1) else ∅

def innerExcessExpected (i : Nat) : Tensor :=
  if i = 5 then singleton [0,2,0,2,0,2,0,2] (monomial 2) else ∅

theorem s_positive_check : ∀ i : Fin 27,
    sameEntries (above (expand sSteps (singleton (triple i))) 0)
      (sPositiveExpected i) = true := by native_decide

theorem s_unique_positive (i : Fin 27) (w : Word) :
    (above (expand sSteps (singleton (triple i))) 0).getD w [] =
      (sPositiveExpected i).getD w [] :=
  sameEntries_getD _ _ (s_positive_check i) w

theorem inner_excess_check : ∀ i : Fin 27,
    sameEntries (above (expand innerSteps (singleton (triple i))) (height i))
      (innerExcessExpected i) = true := by native_decide

theorem inner_unique_excess (i : Fin 27) (w : Word) :
    (above (expand innerSteps (singleton (triple i))) (height i)).getD w [] =
      (innerExcessExpected i).getD w [] :=
  sameEntries_getD _ _ (inner_excess_check i) w

theorem inner_path_nonnegative_check : ∀ i : Fin 27,
    allEntries (expand innerSteps (singleton (triple i)))
      (fun _ p => p.all (fun term => 0 < term.2)) = true := by native_decide

def outerBoundCheck : Bool := (List.range (3^8)).all fun i =>
  allEntries (expand cSteps (singleton (wordsOfIndex 8 i)))
    (fun w p => bounded (-height (encode (w.take 3))) p)

theorem outer_bound_check : outerBoundCheck = true := by native_decide

theorem outer_bound (i : Fin (3^8)) (w : Word) :
    bounded (-height (encode (w.take 3)))
      ((expand cSteps (singleton (wordsOfIndex 8 i))).getD w []) = true := by
  have hi : i.val ∈ List.range (3^8) := List.mem_range.mpr i.isLt
  have h := List.all_eq_true.mp outer_bound_check i.val hi
  exact allEntries_getD _ _ h (fun _ => rfl) w

def ascents (i : Nat) : Int :=
  (if i/9 < i/3%3 then 1 else 0) + (if i/3%3 < i%3 then 1 else 0)

theorem ascents_height (i : Fin 27) : ascents i ≤ 1 + height i := by
  revert i
  decide

theorem ascent_bounds_check : ∀ i : Fin 27,
    allEntries (rawD₀ i) (fun _ p => bounded (ascents i) p) = true ∧
    allEntries (rawH i) (fun _ p => bounded (ascents i) p) = true := by
  native_decide

theorem d₀_ascent_bound (i : Fin 27) (w : Word) :
    bounded (ascents i) ((rawD₀ i).getD w []) = true :=
  allEntries_getD _ _ (ascent_bounds_check i).1 (fun _ => rfl) w

theorem h_ascent_bound (i : Fin 27) (w : Word) :
    bounded (ascents i) ((rawH i).getD w []) = true :=
  allEntries_getD _ _ (ascent_bounds_check i).2 (fun _ => rfl) w

def ascendSigns (signs : List Bool) (step : Step) : Option (List Bool) := do
  let (op,i) := step
  match op with
  | .y =>
    let a ← signs[i]?
    return signs.take i ++ [!a,!a] ++ signs.drop (i+1)
  | .lam =>
    let a ← signs[i]?
    let b ← signs[i+1]?
    if a = b then return signs.take i ++ [!a] ++ signs.drop (i+2) else none
  | .sigma =>
    let a ← signs[i]?
    let b ← signs[i+1]?
    if a ≠ b then return signs.take i ++ signs.drop (i+2) else none
  | .h =>
    let a ← signs[i]?
    let b ← signs[i+1]?
    if a ≠ b then return signs.take i ++ [b,a] ++ signs.drop (i+2) else none
  | .cup => none -- The cup's oriented type is supplied by the downward boundary.

theorem attached_small_map_types :
    (correctionSteps ++ hSteps).all (fun (growth,small) =>
      small.foldlM ascendSigns [true,true,true] == inputSigns 9 growth) = true := by
  decide

theorem block_factorization : blockSteps = cSteps ++ innerSteps := by decide

end WebMu.Revised
