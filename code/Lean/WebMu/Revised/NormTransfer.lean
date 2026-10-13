import WebMu.Proposition42
import WebMu.Revised.NormContractionBridge
import WebMu.Revised.NormCoordinateBridge
import WebMu.Revised.OriginalTensor

namespace WebMu.Revised.ShortNorm
open Laurent Algebra NormSemantics

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def shortPrefixColumn (i : Nat) : Column :=
  (shortPrefix i).fold (fun out w p => accumulate out (0,encode w) p) ∅

def shortInitialData : Array Laurent :=
  let s := monomial (-2)
  let alpha := add one s
  #[s,[],monomial (-4),alpha,s,s,neg s].map (mul (pow alpha 2))

def identityMatrix : SmallMatrix := smallMatrix (fun i j => if i == j then one else [])

def shortInitialExpected (i j : Nat) : Laurent :=
  Laurent.sum ((List.finRange 7).map (fun k =>
    mul shortInitialData[k.val]! (entry gramBasis[k.val]! i j)))

theorem short_initial_check : ∀ i j : Fin 28,
    pairColumns (shortPrefixColumn i) (shortPrefixColumn j) identityMatrix =
      shortInitialExpected i j := by native_decide

def columnBound (n : Nat) (x : Column) : Bool :=
  allEntries x (fun key _ => key.1 < 28 && key.2 < 3^n)

theorem column_bounds_check :
    (∀ i : Fin 28, columnBound 6 (shortPrefixColumn i) = true) ∧
    (∀ i : Fin 28, columnBound 9 (blockColumn i) = true) ∧
    columnBound 6 tailColumn = true := by native_decide

theorem column_bounds (n : Nat) (x : Column) (h : columnBound n x = true) :
    ∀ term ∈ x.toList, term.1.1 < 28 ∧ term.1.2 ∈ List.range (3^n) := by
  intro term ht
  have hh := List.all_eq_true.mp h term ht
  simpa [List.mem_range] using hh

theorem entry_smallMatrix (f : Nat → Nat → Laurent) (i j : Fin 28) :
    entry (smallMatrix f) i.val j.val = f i.val j.val := by
  have hij : i.val*28+j.val < 784 := by omega
  simp [entry, smallMatrix, getElem!_pos, hij]
  have hdiv : (i.val*28+j.val)/28 = i.val := by omega
  have hmod : (i.val*28+j.val)%28 = j.val := by omega
  rw [hdiv, Nat.mod_eq_of_lt j.isLt]

theorem gramBasis_size : gramBasis.size = 7 := rfl

theorem transfer_raw (l : Fin 7) (i j : Fin 28) :
    pairColumns (blockColumn i.val) (blockColumn j.val) gramBasis[l.val]! =
      expectedTransfer gramBasis l.val i.val j.val := by
  have h := congrArg (fun a : Array SmallMatrix => entry a[l.val]! i.val j.val)
    WebMu.transfer_identities
  simpa [actualTransfer, predictedTransfer, getElem!_pos, gramBasis_size,
    l.isLt, i.isLt, j.isLt, entry_smallMatrix] using h

theorem terminal_raw (l : Fin 7) :
    pairColumns tailColumn tailColumn gramBasis[l.val]! = terminalData[l.val]! := by
  have h := congrArg (fun a : Array Laurent => a[l.val]!) WebMu.terminal_identities
  simpa [actualTerminal, getElem!_pos, gramBasis_size, l.isLt] using h

def prefixN (w : Nat) (i : Fin 28) : Poly := ofList ((shortPrefixColumn i).getD (0,w) [])
def blockN (w : Nat) (i j : Fin 28) : Poly := ofList ((blockColumn j).getD (i.val,w) [])
def tailN (w : Nat) (i : Fin 28) : Poly := ofList (tailColumn.getD (i.val,w) [])
def basisN (l : Fin 7) (i j : Fin 28) : Poly := ofList (entry gramBasis[l.val]! i j)
def initialN (l : Fin 7) : Poly := ofList shortInitialData[l.val]!

def initialWords : List Nat := List.range (3^6)
def blockWords : List Nat := List.range (3^9)
def tailWords : List Nat := List.range (3^6)

theorem fold_add_poly {ι : Type} (is : List ι) (f : ι → Laurent) (acc : Laurent) :
    ofList (is.foldl (fun p i => add p (f i)) acc) = ofList acc + total is (fun i => ofList (f i)) := by
  induction is generalizing acc with
  | nil => simp
  | cons i is ih => simp only [List.foldl_cons, ih, ofList_add, total_cons, poly_add_assoc]

theorem expectedTransfer_poly (l : Fin 7) (i j : Fin 28) :
    ofList (expectedTransfer gramBasis l i j) =
      combine WebMu.indices basisN (fun k => NormCoordinateBridge.transfer k l) i j := by
  unfold expectedTransfer
  rw [fold_add_poly]
  have hr : List.range 7 = (List.finRange 7).map Fin.val := by decide
  rw [hr, Revised.total_map, ofList_empty, poly_zero_add]
  rfl

theorem concrete_transfer (l : Fin 7) :
    normStep (List.finRange 28) blockWords blockN (basisN l) =
      combine WebMu.indices basisN (fun k => NormCoordinateBridge.transfer k l) := by
  funext i j
  have h := NormContraction.pairColumns_full (blockColumn i) (blockColumn j)
    gramBasis[l.val]! blockWords (List.nodup_range)
    (column_bounds 9 _ (column_bounds_check.2.1 i))
  rw [transfer_raw l i j, expectedTransfer_poly] at h
  exact h.symm

theorem concrete_terminal (l : Fin 7) :
    normReadout (List.finRange 28) tailWords tailN (basisN l) =
      NormCoordinateBridge.terminal l := by
  have h := NormContraction.pairColumns_full tailColumn tailColumn
    gramBasis[l.val]! tailWords (List.nodup_range)
    (column_bounds 6 _ column_bounds_check.2.2)
  rw [terminal_raw l] at h
  exact h.symm

theorem prefix_only_zero (j : Fin 28) (i w : Nat) :
    ofList ((shortPrefixColumn j).getD (i,w) []) =
      if i = 0 then prefixN w j else 0 := by
  by_cases hi : i = 0
  · subst i
    rfl
  · rw [shortPrefixColumn, hashmap_fold_poly]
    have hz : total (shortPrefix j).toList (fun (s,p) =>
        if (0,encode s) == (i,w) then ofList p else 0) =
        total (shortPrefix j).toList (fun _ => 0) := by
      apply total_congr_mem
      rintro ⟨s,p⟩ _
      simp [Ne.symm hi]
    rw [hz,total_zero,if_neg hi]

theorem double_zero_row (u v : Poly) :
    total (List.finRange 28) (fun i => total (List.finRange 28) (fun k =>
      (if i = 0 then u else 0) * (if i = k then (1:Poly) else 0) *
        (if k = 0 then v else 0))) = u*v := by
  have hz : (0 : Fin 28) ∈ List.finRange 28 := by decide
  have hi (i : Fin 28) : total (List.finRange 28) (fun k =>
      (if i = 0 then u else 0) * (if i = k then (1:Poly) else 0) *
        (if k = 0 then v else 0)) = if i = 0 then u*v else 0 := by
    by_cases h : i = 0
    · subst i
      have hf : (fun (k : Fin 28) =>
          (if (0:Fin 28) = 0 then u else 0) * (if (0:Fin 28) = k then (1:Poly) else 0) *
            (if k = 0 then v else 0)) =
          fun k => if k = 0 then u*v else 0 := by
        funext k
        by_cases hk : k = 0
        · simp [hk]
        · simp [hk,Ne.symm hk]
      rw [hf,total_delta _ (by decide) 0,if_pos hz,if_pos rfl]
    · simp [h]
  simp only [hi]
  rw [total_delta _ (by decide) 0,if_pos hz]

theorem concrete_initial : gram initialWords prefixN = combine WebMu.indices basisN initialN := by
  funext i j
  have h := NormContraction.pairColumns_full (shortPrefixColumn i) (shortPrefixColumn j)
    identityMatrix initialWords (List.nodup_range)
    (column_bounds 6 _ (column_bounds_check.1 i))
  have hId (a b : Fin 28) : ofList (entry identityMatrix a b) =
      if a = b then (1:Poly) else 0 := by
    rw [identityMatrix,entry_smallMatrix]
    simp [Fin.ext_iff]
    split <;> rfl
  have hz (w : Nat) : total (List.finRange 28) (fun a => total (List.finRange 28) (fun b =>
      ofList ((shortPrefixColumn i).getD (a.val,w) []) * ofList (entry identityMatrix a b) *
        ofList ((shortPrefixColumn j).getD (b.val,w) []))) = prefixN w i * prefixN w j := by
    simp only [prefix_only_zero,hId]
    have hh (a : Fin 28) : a.val = 0 ↔ a = 0 := ⟨fun h => Fin.ext h,congrArg Fin.val⟩
    simp only [hh]
    exact double_zero_row _ _
  simp only [hz] at h
  rw [short_initial_check, shortInitialExpected, NormCoordinateBridge.ofList_sum_total] at h
  exact h.symm

def initialEntry (i : Fin 7) : Laurent := shortInitialData[i.val]!

def coordinates : Nat → WebMu.Coordinates
  | 0 => initialEntry
  | m+1 => coordinateStep (coordinates m)

/-- The shortened construction has the same transfer and terminal row, but its
initial column is α²(s,0,s²,α,s,s,-s), where s=v⁻² and α=1+s. -/
def normPolynomial (m : Nat) : Laurent :=
  Laurent.sum (WebMu.indices.map (fun i => mul (bEntry i) (coordinates m i)))

theorem initial_support : ∀ i, EvenNonpositive (initialEntry i) := by
  simp [initialEntry, shortInitialData, pow, mul, add, one, monomial, shiftScale, neg]
  decide +kernel

theorem initial_constant : ∀ i, coeff (initialEntry i) 0 = aZero i := by
  simp [initialEntry, shortInitialData, pow, mul, add, one, monomial, shiftScale, neg]
  decide +kernel

theorem coordinates_support (m : Nat) : ∀ i, EvenNonpositive (coordinates m i) := by
  induction m with
  | zero => exact initial_support
  | succ m ih =>
    intro i
    apply support_sum
    intro p hp
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
    exact support_mul _ _ (k_support i j) (ih j)

theorem coordinates_constant (m : Nat) : ∀ i, coeff (coordinates m i) 0 = aZero i := by
  induction m with
  | zero => exact initial_constant
  | succ m ih =>
    intro i
    simp only [coordinates, coordinateStep, coeff_sum, List.map_map]
    have h : (fun j => coeff (mul (kEntry i j) (coordinates m j)) 0) =
        (fun j => kZero i j * aZero j) := by
      funext j
      rw [Laurent.coeff_mul_zero _ _ (k_support i j) (coordinates_support m j), k_constant, ih]
    simpa only [Function.comp_def, h] using constant_fixed i

theorem norm_support_constant (m : Nat) :
    EvenNonpositive (normPolynomial m) ∧ coeff (normPolynomial m) 0 = 1 := by
  constructor
  · apply support_sum
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact support_mul _ _ (b_support i) (coordinates_support m i)
  · simp only [normPolynomial, coeff_sum, List.map_map]
    have h : (fun i => coeff (mul (bEntry i) (coordinates m i)) 0) =
        (fun i => bZero i * aZero i) := by
      funext i
      rw [Laurent.coeff_mul_zero _ _ (b_support i) (coordinates_support m i),
        b_constant, coordinates_constant]
    simpa only [Function.comp_def, h] using constant_terminal

theorem coefficientIterate_short (m : Nat) :
    coefficientIterate WebMu.indices NormCoordinateBridge.transfer initialN m =
      fun i => ofList (coordinates m i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i
    simp only [coefficientIterate, ih, action, coordinates, coordinateStep,
      NormCoordinateBridge.ofList_sum_total, ofList_mul]
    rfl

theorem normPolynomial_poly (m : Nat) :
    pairing WebMu.indices NormCoordinateBridge.terminal
        (coefficientIterate WebMu.indices NormCoordinateBridge.transfer initialN m) =
      ofList (normPolynomial m) := by
  rw [coefficientIterate_short]
  simp only [pairing, normPolynomial, NormCoordinateBridge.ofList_sum_total, ofList_mul]
  rfl

theorem full_norm_polynomial (m : Nat) :
    fullNorm (List.finRange 28) initialWords blockWords tailWords prefixN blockN tailN m =
      ofList (normPolynomial m) := by
  rw [full_norm_transfer (List.finRange 28) initialWords blockWords tailWords WebMu.indices
    prefixN blockN tailN basisN NormCoordinateBridge.transfer initialN
    NormCoordinateBridge.terminal concrete_initial concrete_transfer concrete_terminal m,
    normPolynomial_poly]

/-- Independent seven-coordinate verification, valid for every parameter. -/
theorem full_norm_integral_constant_one (m : Nat) :
    (∀ d, 0 < d → coefficient
      (fullNorm (List.finRange 28) initialWords blockWords tailWords prefixN blockN tailN m) d = 0) ∧
    coefficient
      (fullNorm (List.finRange 28) initialWords blockWords tailWords prefixN blockN tailN m) 0 = 1 := by
  rw [full_norm_polynomial]
  exact ⟨fun d hd => Laurent.coeff_positive _ (norm_support_constant m).1 d hd,
    (norm_support_constant m).2⟩

end WebMu.Revised.ShortNorm
