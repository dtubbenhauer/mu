import WebMu.Revised.SelectedWeightRows

/-! The selected-row calculation with the printed weight restriction first:
only six tensor inputs and the scalar column are evaluated. The remaining
21 inputs vanish by the uniform signed-weight theorem. -/
namespace WebMu.Revised.WeightConservation
open Laurent Algebra Bar AtlasRealization CapDiagram SelectedRowDerivation
open LocalDegreeProof LocalExpositionChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sixInput (k : Fin 6) : Fin 27 :=
  [⟨5,by decide⟩,⟨7,by decide⟩,⟨11,by decide⟩,⟨15,by decide⟩,⟨19,by decide⟩,⟨21,by decide⟩][k.val]'(by exact k.isLt)

theorem six_input_words : (List.finRange 6).map (fun k => triple (sixInput k))=
    [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]] := by decide

theorem six_exhaust : ∀ j : Fin 28, j.val∈[5,7,11,15,19,21,27] →
    (∃ k : Fin 6, j=(sixInput k).castSucc) ∨ j=27 := by decide

/-- The seven and eleven small-map sums are computed on exactly the six
weight-zero tensor words in the printed order. -/
theorem small_six_checks : ∀ k : Fin 6,
    Laurent.sum ((List.finRange 7).map (fun j =>
      smallContribution correctionSteps[j.val]! dPrefixExpected[j.val]! (sixInput k)))=dRow (sixInput k) ∧
    Laurent.sum ((List.finRange 11).map (fun j =>
      smallContribution hSteps[j.val]! hPrefixExpected[j.val]! (sixInput k)))=hRow (sixInput k) := by native_decide

theorem raw_d_six (k : Fin 6) :
    ofList ((rawD₀ (sixInput k)).getD wordBlock [])=ofList (dRow (sixInput k)) := by
  change ofList ((sumMap ((correctionSteps.take 7).map (fun s => summand s (sixInput k)))).getD wordBlock [])=_
  rw [sumMap_poly,total_map]
  have hs : correctionSteps.take 7=(List.finRange 7).map (fun j => correctionSteps[j.val]!) := by decide
  rw [hs,total_map,← (small_six_checks k).1,ofList_total]
  apply total_congr_mem
  intro j _
  apply summand_from_prefix
  exact fun w => congrArg ofList (d_prefix_covector j w)

theorem raw_h_six (k : Fin 6) :
    ofList ((rawH (sixInput k)).getD wordBlock [])=ofList (hRow (sixInput k)) := by
  change ofList ((sumMap (hSteps.map (fun s => summand s (sixInput k)))).getD wordBlock [])=_
  rw [sumMap_poly,total_map]
  have hs : hSteps=(List.finRange 11).map (fun j => hSteps[j.val]!) := by decide
  rw [hs,total_map,← (small_six_checks k).2,ofList_total]
  apply total_congr_mem
  intro j _
  apply summand_from_prefix
  exact fun w => congrArg ofList (h_prefix_covector j w)

theorem arithmetic_six : ∀ k : Fin 6,
    upperArithmetic (sixInput k)=expectedABCRow (sixInput k) ∧
    lowerArithmetic (sixInput k)=expectedScalarRow (sixInput k) := by native_decide

theorem upper_formula_six (k : Fin 6) :
    ofList (upperRowFormula (sixInput k))=ofList (expectedABCRow (sixInput k)) := by
  have h : ofList (upperRowFormula (sixInput k))=ofList (upperArithmetic (sixInput k)) := by
    apply shift_congr
    rw [ofList_add,ofList_add,raw_b_row]
    congr 1
    apply neg_congr
    rw [ofList_mul,ofList_mul,raw_c_row]
  exact h.trans (congrArg ofList (arithmetic_six k).1)

theorem lower_formula_six (k : Fin 6) :
    ofList (lowerRowFormula (sixInput k))=ofList (expectedScalarRow (sixInput k)) := by
  have h : ofList (lowerRowFormula (sixInput k))=ofList (lowerArithmetic (sixInput k)) := by
    apply shift_congr
    rw [ofList_add,ofList_add,ofList_add,ofList_add]
    have hd := shift_congr (raw_d_six k) (-2) 1
    have hh := shift_congr (raw_h_six k) (-1) 1
    have ht : ofList (mul (tau3.getD wordBlock []) (eta (sixInput k)))=ofList (eta (sixInput k)) := by
      rw [tripod_row_check,ofList_mul]
      exact poly_one_mul _
    exact add_congr_poly (add_congr_poly hd hh) (neg_congr (shift_congr ht (-4) 1))
  exact h.trans (congrArg ofList (arithmetic_six k).2)

theorem selected_six_values (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (T : BoundaryTripodReferences R F) (k : Fin 6) :
    ofList (selectedBlock 5 (sixInput k))=ofList (expectedABCRow (sixInput k)) ∧
    ofList (selectedBlock 27 (sixInput k))=ofList (expectedScalarRow (sixInput k)) := by
  exact ⟨(upper_formula (sixInput k) 5 wordBlock (by decide)).trans (upper_formula_six k),
    (lower_formula R A F G T (sixInput k) wordBlock (by decide)).trans (lower_formula_six k)⟩

/-- The manuscript's two-row proof: exclude other weights, compute the six
permutations and scalar, and read their constants. -/
theorem selected_rows_from_weights_and_diagrams (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (T : BoundaryTripodReferences R F) (j : Fin 28) :
    coeff (selectedBlock 5 j) 0=(if j.val=27 then 1 else 0) ∧
    coeff (selectedBlock 27 j) 0=(if j.val=5 then 2 else 0) := by
  by_cases hj : j.val∈[5,7,11,15,19,21,27]
  · rcases six_exhaust j hj with ⟨k,rfl⟩|rfl
    · have hh := selected_six_values R A F G T k
      have hc : ∀ k : Fin 6,
          coeff (expectedABCRow (sixInput k)) 0=(if (sixInput k).val=27 then 1 else 0) ∧
          coeff (expectedScalarRow (sixInput k)) 0=(if (sixInput k).val=5 then 2 else 0) := by decide
      exact ⟨(congrArg (fun p => coefficient p 0) hh.1).trans (hc k).1,
        (congrArg (fun p => coefficient p 0) hh.2).trans (hc k).2⟩
    · have hu := upper_scalar_raw_formula 5 wordBlock (by decide)
      have hl := lower_scalar_formula R A F G wordBlock (by decide)
      have hc := shift_congr raw_c_row 1 1
      have hu' := hu.trans hc
      have hl' : coeff (shiftScale (mul (tau3.getD wordBlock []) d) (-2) 1) 0=0 := by native_decide
      exact ⟨congrArg (fun p => coefficient p 0) hu',
        (congrArg (fun p => coefficient p 0) hl).trans hl'⟩
  · have hz := selected_rows_outside_weight_zero R A j hj
    have h27 : j.val≠27 := by intro he; simp [he] at hj
    have h5 : j.val≠5 := by intro he; simp [he] at hj
    rw [if_neg h27,if_neg h5]
    exact ⟨congrArg (fun p => coefficient p 0) hz.1,congrArg (fun p => coefficient p 0) hz.2⟩

#print axioms selected_rows_from_weights_and_diagrams
end WebMu.Revised.WeightConservation
