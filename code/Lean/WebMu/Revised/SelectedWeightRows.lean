import WebMu.Revised.WeightConservation
import WebMu.Revised.LocalRowFormulas
import WebMu.Revised.OriginalBar

/-! The weight-conservation restriction at the start of the selected-row
proof. It follows from primitive signed weights and the actual gauge; no
whole selected row is evaluated to establish the vanishing outside weight 0. -/
namespace WebMu.Revised.WeightConservation
open Laurent Algebra Bar LocalDegreeProof
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def stateWeight (i : Fin 28) : Weight :=
  if i.val<27 then weight (positive 3) (triple i) else (0,0)

theorem state_upper (i : Fin 27) : stateWeight i.castSucc=weight (positive 3) (triple i) := by
  change (if i.val<27 then weight (positive 3) (triple i.val) else (0,0))=_
  rw [if_pos i.isLt]

theorem state_scalar : stateWeight 27=(0,0) := rfl

theorem plus_zero (w : Weight) : plus w (0,0)=w := by cases w; simp [plus]

theorem exterior_neutral : weight (positive 9) wordBlock=(0,0) := by decide

theorem output_weight (i : Fin 27) :
    weight (positive 3++positive 9) (triple i++wordBlock)=stateWeight i.castSucc := by
  rw [weight_append (positive 3) (positive 9) (triple i) wordBlock ((Bar.validWord_iff _ _).mp (Bar.triple_valid i)).1.symm,
    exterior_neutral,plus_zero,state_upper]

theorem split_state (i : Fin 28) : (∃ k : Fin 27, i=k.castSucc) ∨ i=27 := by
  by_cases h : i.val<27
  · exact Or.inl ⟨⟨i.val,h⟩,by apply Fin.ext; rfl⟩
  · exact Or.inr (by apply Fin.ext; omega)

/-- Fixing the weight-zero exterior decoration preserves interface weight. -/
theorem original_selected_weight (R : BarReferences) (A : AtomicCoordinates R)
    (i j : Fin 28) (h : stateWeight i≠stateWeight j) :
    originalBlock (encode wordBlock) i j=0 := by
  have hw : wordBlock.length=9 ∧ ∀ a ∈ wordBlock, a<3 := by decide
  rcases split_state i with ⟨i,rfl⟩|rfl <;> rcases split_state j with ⟨j,rfl⟩|rfl
  · rw [← Bar.webState_eq_castSucc,← Bar.webState_eq_castSucc,originalBlock_B i j wordBlock hw,← b_circuit j]
    apply circuit_weight_zero R A bCircuit _ (Bar.triple_valid j)
    rw [output_weight,← state_upper]
    exact h
  · rw [← Bar.webState_eq_castSucc,originalBlock_C i wordBlock hw,ofList_neg_factor,← c_circuit]
    rw [circuit_weight_zero R A cCircuit [] (by decide) _ (by
      rw [output_weight]
      exact h),poly_zero_mul]
  · rw [← Bar.webState_eq_castSucc,originalBlock_D j wordBlock hw,← d_circuit j]
    apply circuit_weight_zero R A dCircuit _ (Bar.triple_valid j)
    rw [exterior_neutral,← state_upper]
    exact h
  · exact False.elim (h rfl)

/-- The cap has weight zero; the remaining part of the gauge is diagonal.
This tiny finite check is only of η and the diagonal gauge formulas. -/
theorem gauge_weight : ∀ i j : Fin 28, stateWeight i≠stateWeight j →
    g i j=[] ∧ ginv i j=[] := by decide

theorem matmul_weight (a b : Fin 28 → Fin 28 → Poly)
    (ha : ∀ i j, stateWeight i≠stateWeight j → a i j=0)
    (hb : ∀ i j, stateWeight i≠stateWeight j → b i j=0)
    (i j : Fin 28) (h : stateWeight i≠stateWeight j) :
    matmul interfaceIndices a b i j=0 := by
  apply total_eq_zero_of_each
  intro k _
  by_cases hk : stateWeight i=stateWeight k
  · rw [hb k j (by simpa only [← hk] using h),poly_mul_zero]
  · rw [ha i k hk,poly_zero_mul]

/-- The actual G T G⁻¹ selected block, retaining its interface ordering. -/
theorem gauged_selected_weight (R : BarReferences) (A : AtomicCoordinates R)
    (i j : Fin 28) (h : stateWeight i≠stateWeight j) :
    ofList (selectedBlock i j)=0 := by
  change ofList ((blockHat j).getD (i.val,encode wordBlock) [])=0
  rw [block_gauge]
  apply matmul_weight
  · exact fun i j h => matmul_weight gaugeMatrix (originalBlock (encode wordBlock))
      (fun k l h => congrArg ofList (gauge_weight k l h).1)
      (original_selected_weight R A) i j h
  · exact fun k l h => congrArg ofList (gauge_weight k l h).2
  · exact h

/-- Exactly the six permutations of ABC and the scalar have weight zero. -/
theorem neutral_states : ∀ i : Fin 28,
    stateWeight i=(0,0) ↔ i.val ∈ [5,7,11,15,19,21,27] := by decide

theorem selected_rows_outside_weight_zero (R : BarReferences) (A : AtomicCoordinates R)
    (j : Fin 28) (h : j.val ∉ [5,7,11,15,19,21,27]) :
    ofList (selectedBlock 5 j)=0 ∧ ofList (selectedBlock 27 j)=0 := by
  have hw : stateWeight j≠(0,0) := fun he => h ((neutral_states j).mp he)
  exact ⟨gauged_selected_weight R A 5 j (Ne.symm hw),
    gauged_selected_weight R A 27 j (Ne.symm hw)⟩

#print axioms original_selected_weight
#print axioms gauged_selected_weight
#print axioms selected_rows_outside_weight_zero
end WebMu.Revised.WeightConservation
