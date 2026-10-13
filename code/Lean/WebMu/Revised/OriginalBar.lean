import WebMu.Revised.BarCoordinates
import WebMu.Revised.Reindex

/-! Identification of the typed original spider circuit with the original
tensor contraction, followed by its bar invariance. -/
namespace WebMu.Revised.Bar
open Algebra

theorem webState_eq_castSucc (i : Fin 27) : webState i = i.castSucc := rfl

theorem upperCoefficient_step (e : Word) (es : List Word) (v : Word) (i : Fin 27)
    (he : validWord 9 e = true) :
    wordAction interfaceIndices originalBlock (originalTail (encode v))
        ((e::es).map encode) i.castSucc =
      total (List.finRange 27) (fun j =>
        ofList ((rawB j).getD (triple i++e) []) *
          wordAction interfaceIndices originalBlock (originalTail (encode v))
            (es.map encode) j.castSucc) +
      ofList ((evalSparse (.neg cCircuit) []).getD (triple i++e) []) *
        wordAction interfaceIndices originalBlock (originalTail (encode v)) (es.map encode) 27 := by
  have he' := (Bar.validWord_iff 9 e).mp he
  rw [List.map_cons, wordAction, action_fin28]
  simp only [← webState_eq_castSucc, originalBlock_B i _ e he', originalBlock_C i e he',
    evalSparse_neg_coefficient, c_circuit, ofList_neg]

theorem lowerCoefficient_step (e : Word) (es : List Word) (v : Word)
    (he : validWord 9 e = true) :
    wordAction interfaceIndices originalBlock (originalTail (encode v))
        ((e::es).map encode) 27 =
      total (List.finRange 27) (fun j =>
        ofList ((rawD j).getD e []) *
          wordAction interfaceIndices originalBlock (originalTail (encode v))
            (es.map encode) j.castSucc) +
      ofList ((evalSparse (.neg (.scaleD tauThreeCircuit)) []).getD e []) *
        wordAction interfaceIndices originalBlock (originalTail (encode v)) (es.map encode) 27 := by
  have he' := (Bar.validWord_iff 9 e).mp he
  rw [List.map_cons, wordAction, action_fin28]
  simp only [← webState_eq_castSucc, originalBlock_D _ e he', originalBlock_scalar e he',
    evalSparse_neg_coefficient, evalSparse_scaleD_coefficient, tau_three_circuit,
    ofList_mul, ofList_neg]
  rw [poly_mul_comm (ofList d * ofList (Laurent.monomial 0 (-1)))
    (ofList (tau3.getD e [])), ← poly_mul_assoc]

/-- Both interface sectors, proved simultaneously for arbitrary exterior words. -/
theorem circuit_interface_coordinates (R : BarReferences) (C : CoordinateReferences R)
    (es : List Word) (v : Word) (hes : ∀ w ∈ es, validWord 9 w = true)
    (hv : validWord 6 v = true) :
    (∀ i : Fin 27, upperCoordinate R C es v i =
      wordAction interfaceIndices originalBlock (originalTail (encode v)) (es.map encode) i.castSucc) ∧
    lowerCoordinate R C es v =
      wordAction interfaceIndices originalBlock (originalTail (encode v)) (es.map encode) 27 := by
  induction es with
  | nil =>
    constructor
    · intro i
      rw [upperCoordinate_nil R C v i hv]
      exact (originalTail_upper i v ((Bar.validWord_iff 6 v).mp hv)).symm
    · rw [lowerCoordinate_nil R C v hv]
      exact (originalTail_scalar v ((Bar.validWord_iff 6 v).mp hv)).symm
  | cons e es ih =>
    have he : validWord 9 e = true := hes e (by simp)
    have het : ∀ w ∈ es, validWord 9 w = true := by
      intro w hw
      exact hes w (by simp [hw])
    have iht := ih het
    constructor
    · intro i
      rw [upperCoordinate_cons R C e es v i he het hv, upperCoefficient_step e es v i he]
      simp only [iht.1, iht.2]
    · rw [lowerCoordinate_cons R C e es v he het hv, lowerCoefficient_step e es v he]
      simp only [iht.1, iht.2]

/-- The bar-invariant circuit evaluates to exactly the unchanged tensor. -/
theorem circuitTensor_eq_original (R : BarReferences) (C : CoordinateReferences R)
    (m : Nat) : circuitTensor R C m = tensorOriginal m := by
  funext b
  rw [circuitTensor_prefix]
  unfold tensorOriginal
  rw [pairing_fin28 _ _ (prefix_scalar_zero b.initial)]
  have he : ∀ w ∈ b.blocks, validWord 9 w = true := by
    intro w hw
    exact (Bar.validWord_iff 9 w).mpr (b.blocks_valid w hw)
  have hv : validWord 6 b.terminal = true :=
    (Bar.validWord_iff 6 b.terminal).mpr ⟨b.terminal_length,b.terminal_ternary⟩
  simp only [(circuit_interface_coordinates R C b.blocks b.terminal he hv).1]

/-- The actual manuscript tensor is bar fixed for every m; G is not involved. -/
theorem tensorOriginal_fixed (R : BarReferences) (C : CoordinateReferences R) (m : Nat) :
    C.tensorBar m (tensorOriginal m) = tensorOriginal m := by
  rw [← circuitTensor_eq_original R C m]
  exact circuitTensor_fixed R C m

end WebMu.Revised.Bar
