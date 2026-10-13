import WebMu.Revised.LocalExpositionChecks
import WebMu.Revised.CoefficientBridge

/-! The printed downward covector derivation of the two selected rows.
The final gauged rows are obtained from the upper/lower formulas, rather than
from an independent evaluation of the entire gauged block. -/
namespace WebMu.Revised.SelectedRowDerivation
open Laurent Algebra GrowthPairing M2Flow LocalExpositionChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Extensional equality of tensors, retaining every Laurent coefficient. -/
def CoordinatesEqual (x y : Tensor) : Prop :=
  ∀ w, ofList (x.getD w [])=ofList (y.getD w [])

theorem equal_of_check (x y : Tensor) (h : sameEntries x y=true) :
    CoordinatesEqual x y := fun w => congrArg ofList (sameEntries_getD x y h w)

theorem coordinates_trans {x y z : Tensor} (h : CoordinatesEqual x y)
    (k : CoordinatesEqual y z) : CoordinatesEqual x z := fun w => (h w).trans (k w)

theorem pair_right_congr (x y z : Tensor) (h : CoordinatesEqual y z) :
    sparsePair x y=sparsePair x z := by
  unfold sparsePair
  apply total_congr_mem
  rintro ⟨w,p⟩ _
  dsimp only
  rw [h w]

theorem fold_congr (steps : List Step) (x y : Tensor) (h : CoordinatesEqual x y) :
    CoordinatesEqual (steps.foldl downwardStep x) (steps.foldl downwardStep y) := by
  intro w
  rw [← singleton_pair,← singleton_pair,← expand_transpose,← expand_transpose]
  exact pair_right_congr _ _ _ h

/-- The three complete covectors displayed before the last S in the proof. -/
def outerRow : Tensor := tensorOf [
  ([0,0,2,2,0,2,0,2],monomial (-2)),
  ([0,2,0,2,0,2,0,2],monomial (-1))]

def secondRow : Tensor := tensorOf [
  ([0,1,2,0,2,0,2],[(-2,1),(0,1)]),
  ([1,0,2,0,2,0,2],monomial (-1)),
  ([0,2,1,0,2,0,2],monomial (-1))]

def middleRow : Tensor := tensorOf [
  ([0,0,2,2],[(-3,1),(-1,1)]),
  ([0,2,0,2],[(-4,1),(-2,3),(0,1)]),
  ([0,2,1,1],[(-3,2),(-1,1)]),
  ([1,1,0,2],[(-3,1),(-1,1)]),
  ([1,1,1,1],monomial (-2)),
  ([1,0,1,2],monomial (-2)),
  ([0,1,2,1],monomial (-2))]

def lastRow : Tensor := sSteps.foldl downwardStep middleRow

theorem outer_row_check :
    sameEntries (downwardCovector cSteps ([0,1,2]++wordBlock)) outerRow=true := by
  native_decide

theorem second_row_check : sameEntries (sSteps.foldl downwardStep outerRow) secondRow=true := by
  native_decide

theorem middle_row_check : sameEntries (middleSteps.foldl downwardStep secondRow) middleRow=true := by
  native_decide

theorem downward_block_stages :
    CoordinatesEqual (downwardCovector blockSteps ([0,1,2]++wordBlock)) lastRow := by
  unfold downwardCovector lastRow
  rw [block_factorization]
  simp only [innerSteps,List.foldl_append]
  exact fold_congr sSteps _ _ (coordinates_trans (fold_congr middleSteps _ _
    (coordinates_trans (fold_congr sSteps _ _ (equal_of_check _ _ outer_row_check))
      (equal_of_check _ _ second_row_check))) (equal_of_check _ _ middle_row_check))

/-- Raw B row after the last S, before the gauge correction. -/
def bRow (i : Nat) : Laurent := lastRow.getD (triple i) []

theorem raw_b_row (i : Fin 27) :
    ofList ((rawB i).getD ([0,1,2]++wordBlock) [])=ofList (bRow i) := by
  rw [rawB,← covector_is_coordinate]
  exact downward_block_stages (triple i)

/-- Exact finite contraction of the initial covector with the four cups. -/
def pairLaurent (x y : Tensor) : Laurent :=
  Laurent.sum (x.toList.map (fun (w,p) => mul p (y.getD w [])))

theorem ofList_pair (x y : Tensor) : ofList (pairLaurent x y)=sparsePair x y := by
  simp only [pairLaurent,ofList_total,ofList_mul,sparsePair]

theorem cups_outer_check : pairLaurent fourCups outerRow=monomial (-1) := by native_decide

theorem raw_c_row : ofList (rawC.getD ([0,1,2]++wordBlock) [])=ofList (monomial (-1)) := by
  have h := expand_transpose cSteps fourCups (singleton ([0,1,2]++wordBlock))
  rw [pair_singleton] at h
  change ofList (rawC.getD ([0,1,2]++wordBlock) []) = _ at h
  rw [h]
  change sparsePair fourCups (downwardCovector cSteps ([0,1,2]++wordBlock))=_
  rw [pair_right_congr _ _ _ (equal_of_check _ _ outer_row_check),← ofList_pair,cups_outer_check]

/-- The two displayed sums of the D0 and H rows, zero on the other 21 inputs. -/
def dRow : Nat → Laurent
  | 5 => [(-1,3),(1,5)]
  | 7 => [(-2,1),(0,4)]
  | 11 => [(-2,2),(0,5)]
  | 15 | 19 => monomial (-1) 2
  | 21 => monomial (-2)
  | _ => []

def hRow : Nat → Laurent
  | 5 => [(-2,3),(0,8),(2,2)]
  | 7 => [(-3,1),(-1,5),(1,2)]
  | 11 => [(-3,1),(-1,6),(1,2)]
  | 15 => [(-2,1),(0,2)]
  | 19 => [(-2,1),(0,1)]
  | 21 => monomial (-1)
  | _ => []

def smallContribution (steps : List Step × List Step) (covector : Tensor) (i : Nat) : Laurent :=
  pairLaurent (compose steps.2 (singleton (triple i))) covector

theorem summand_from_prefix (steps : List Step × List Step) (covector : Tensor)
    (hp : CoordinatesEqual (downwardCovector steps.1 wordBlock) covector) (i : Nat) :
    ofList ((summand steps i).getD wordBlock [])=ofList (smallContribution steps covector i) := by
  rw [summand,← pair_singleton,expand_transpose]
  change sparsePair _ (downwardCovector steps.1 wordBlock)=_
  rw [pair_right_congr _ _ _ hp,← ofList_pair]
  rfl

theorem d_small_sum_check : ∀ i : Fin 27,
    Laurent.sum ((List.finRange 7).map (fun j =>
      smallContribution correctionSteps[j.val]! dPrefixExpected[j.val]! i))=dRow i := by
  native_decide

theorem h_small_sum_check : ∀ i : Fin 27,
    Laurent.sum ((List.finRange 11).map (fun j =>
      smallContribution hSteps[j.val]! hPrefixExpected[j.val]! i))=hRow i := by
  native_decide

theorem raw_d_row (i : Fin 27) : ofList ((rawD₀ i).getD wordBlock [])=ofList (dRow i) := by
  change ofList ((sumMap ((correctionSteps.take 7).map (fun s => summand s i))).getD wordBlock [])=_
  rw [sumMap_poly,total_map]
  have hs : correctionSteps.take 7=(List.finRange 7).map (fun j => correctionSteps[j.val]!) := by decide
  rw [hs,total_map,← d_small_sum_check i,ofList_total]
  apply total_congr_mem
  intro j _
  apply summand_from_prefix
  exact fun w => congrArg ofList (d_prefix_covector j w)

theorem raw_h_row (i : Fin 27) : ofList ((rawH i).getD wordBlock [])=ofList (hRow i) := by
  change ofList ((sumMap (hSteps.map (fun s => summand s i))).getD wordBlock [])=_
  rw [sumMap_poly,total_map]
  have hs : hSteps=(List.finRange 11).map (fun j => hSteps[j.val]!) := by decide
  rw [hs,total_map,← h_small_sum_check i,ofList_total]
  apply total_congr_mem
  intro j _
  apply summand_from_prefix
  exact fun w => congrArg ofList (h_prefix_covector j w)

/-- Only H4 and H7 supply degree two at this selected input and output. -/
theorem h_four_seven_check :
    smallContribution hSteps[3]! hPrefixExpected[3]! 5=[(0,2),(2,1)] ∧
    smallContribution hSteps[6]! hPrefixExpected[6]! 5=monomial 2 ∧
    ∀ j : Fin 11, j.val≠3 → j.val≠6 →
      bounded 0 (smallContribution hSteps[j.val]! hPrefixExpected[j.val]! 5)=true := by
  native_decide

set_option maxHeartbeats 200000

theorem add_congr_poly {a b c d : Poly} (h : a=b) (k : c=d) : a+c=b+d := by
  rw [h,k]

/-- The attribution is a statement about the actual eleven summands. -/
theorem h_summand_selected (j : Fin 11) :
    ofList ((summand hSteps[j.val]! 5).getD wordBlock [])=
      ofList (smallContribution hSteps[j.val]! hPrefixExpected[j.val]! 5) :=
  summand_from_prefix _ _ (fun w => congrArg ofList (h_prefix_covector j w)) 5

theorem h_four_seven :
    ofList ((summand hSteps[3]! 5).getD wordBlock [])=ofList [(0,2),(2,1)] ∧
    ofList ((summand hSteps[6]! 5).getD wordBlock [])=ofList (monomial 2) ∧
    ∀ j : Fin 11, j.val≠3 → j.val≠6 → ∀ e, 0<e →
      coeff ((summand hSteps[j.val]! 5).getD wordBlock []) e=0 := by
  refine ⟨(h_summand_selected 3).trans (congrArg ofList h_four_seven_check.1),
    (h_summand_selected 6).trans (congrArg ofList h_four_seven_check.2.1),?_⟩
  intro j h3 h6 e he
  have h := h_four_seven_check.2.2 j h3 h6
  have hp : Nonpositive (smallContribution hSteps[j.val]! hPrefixExpected[j.val]! 5) :=
    (show canonical _=true ∧ _ from by simpa only [bounded,Bool.and_eq_true] using h).2
  have hc := congrArg (fun p => coefficient p e) (h_summand_selected j)
  exact hc.trans (coeff_positive _ hp e he)

/-- Shift and sign changes respect extensional polynomial equality. -/
theorem shift_congr {p q : Laurent} (h : ofList p=ofList q) (e c : Int) :
    ofList (shiftScale p e c)=ofList (shiftScale q e c) := by
  apply poly_ext
  intro n
  simp only [coefficient_ofList,coeff_shiftScale]
  exact congrArg (fun x => coefficient x (n-e) * c) h

theorem neg_congr {p q : Laurent} (h : ofList p=ofList q) :
    ofList (neg p)=ofList (neg q) := by
  apply poly_ext
  intro n
  simp only [coefficient_ofList,Algebra.coeff_neg]
  exact congrArg (fun x => -coefficient x n) h

def upperRowFormula (i : Nat) : Laurent :=
  shiftScale (add ((rawB i).getD ([0,1,2]++wordBlock) [])
    (neg (mul (rawC.getD ([0,1,2]++wordBlock) []) (shiftScale (eta i) (-1) 1))))
    (1-height i) 1

def lowerRowFormula (i : Nat) : Laurent :=
  shiftScale (add (add (shiftScale ((rawD₀ i).getD wordBlock []) (-2) 1)
    (shiftScale ((rawH i).getD wordBlock []) (-1) 1))
    (neg (shiftScale (mul (tau3.getD wordBlock []) (eta i)) (-4) 1))) (-height i) 1

def upperArithmetic (i : Nat) : Laurent :=
  shiftScale (add (bRow i)
    (neg (mul (monomial (-1)) (shiftScale (eta i) (-1) 1)))) (1-height i) 1

def lowerArithmetic (i : Nat) : Laurent :=
  shiftScale (add (add (shiftScale (dRow i) (-2) 1) (shiftScale (hRow i) (-1) 1))
    (neg (shiftScale (eta i) (-4) 1))) (-height i) 1

theorem upper_arithmetic : ∀ i : Fin 27, upperArithmetic i=expectedABCRow i := by native_decide

theorem lower_arithmetic : ∀ i : Fin 27, lowerArithmetic i=expectedScalarRow i := by native_decide

theorem tripod_row_check : tau3.getD wordBlock []=one := by native_decide

theorem upper_row_formula_value (i : Fin 27) :
    ofList (upperRowFormula i)=ofList (expectedABCRow i) := by
  have h : ofList (upperRowFormula i)=ofList (upperArithmetic i) := by
    apply shift_congr
    rw [ofList_add,ofList_add,raw_b_row]
    congr 1
    apply neg_congr
    rw [ofList_mul,ofList_mul,raw_c_row]
  exact h.trans (congrArg ofList (upper_arithmetic i))

theorem lower_row_formula_value (i : Fin 27) :
    ofList (lowerRowFormula i)=ofList (expectedScalarRow i) := by
  have h : ofList (lowerRowFormula i)=ofList (lowerArithmetic i) := by
    apply shift_congr
    rw [ofList_add,ofList_add,ofList_add,ofList_add]
    have hd := shift_congr (raw_d_row i) (-2) 1
    have hh := shift_congr (raw_h_row i) (-1) 1
    have ht : ofList (mul (tau3.getD wordBlock []) (eta i))=ofList (eta i) := by
      rw [tripod_row_check,ofList_mul]
      exact poly_one_mul _
    exact add_congr_poly
      (add_congr_poly hd hh) (neg_congr (shift_congr ht (-4) 1))
  exact h.trans (congrArg ofList (lower_arithmetic i))

/-- Substitution of the upper formula into the printed raw covector derivation. -/
theorem selected_upper_row
    (hu : ∀ i : Fin 27, ofList (selectedBlock 5 i)=ofList (upperRowFormula i))
    (hs : ofList (selectedBlock 5 27)=ofList
      (shiftScale (rawC.getD ([0,1,2]++wordBlock) []) 1 1)) (i : Fin 28) :
    ofList (selectedBlock 5 i)=ofList (expectedABCRow i) := by
  by_cases hi : i.val<27
  · exact (hu ⟨i.val,hi⟩).trans (upper_row_formula_value ⟨i.val,hi⟩)
  · have hi' : i.val=27 := by omega
    simp only [hi']
    exact hs.trans ((shift_congr raw_c_row 1 1).trans (by rfl))

/-- Substitution of the atlas-derived lower formula into the D0/H prefix sums. -/
theorem selected_lower_row
    (hl : ∀ i : Fin 27, ofList (selectedBlock 27 i)=ofList (lowerRowFormula i))
    (hs : ofList (selectedBlock 27 27)=ofList
      (shiftScale (mul (tau3.getD wordBlock []) d) (-2) 1)) (i : Fin 28) :
    ofList (selectedBlock 27 i)=ofList (expectedScalarRow i) := by
  by_cases hi : i.val<27
  · exact (hl ⟨i.val,hi⟩).trans (lower_row_formula_value ⟨i.val,hi⟩)
  · have hi' : i.val=27 := by omega
    simp only [hi']
    rw [hs,tripod_row_check]
    exact congrArg ofList (show shiftScale (mul one d) (-2) 1=expectedScalarRow 27 from by native_decide)

/-- The resulting two rows have precisely the support and constants of K. -/
theorem two_closed_rows
    (hu : ∀ i : Fin 27, ofList (selectedBlock 5 i)=ofList (upperRowFormula i))
    (hus : ofList (selectedBlock 5 27)=ofList
      (shiftScale (rawC.getD ([0,1,2]++wordBlock) []) 1 1))
    (hl : ∀ i : Fin 27, ofList (selectedBlock 27 i)=ofList (lowerRowFormula i))
    (hls : ofList (selectedBlock 27 27)=ofList
      (shiftScale (mul (tau3.getD wordBlock []) d) (-2) 1)) (i : Fin 28) :
    coeff (selectedBlock 5 i) 0=(if i.val=27 then 1 else 0) ∧
    coeff (selectedBlock 27 i) 0=(if i.val=5 then 2 else 0) := by
  have hu' := congrArg (fun p => coefficient p 0) (selected_upper_row hu hus i)
  have hl' := congrArg (fun p => coefficient p 0) (selected_lower_row hl hls i)
  have hc : ∀ j : Fin 28,
      coeff (expectedABCRow j) 0=(if j.val=27 then 1 else 0) ∧
      coeff (expectedScalarRow j) 0=(if j.val=5 then 2 else 0) := by decide
  exact ⟨hu'.trans (hc i).1,hl'.trans (hc i).2⟩

#print axioms raw_b_row
#print axioms raw_d_row
#print axioms raw_h_row
#print axioms two_closed_rows
end WebMu.Revised.SelectedRowDerivation
