import WebMu.Revised.LocalEndpointPaths
import WebMu.Revised.LocalRowFormulas

/-! The selected end rows, from their individual elementary paths, followed
by the actual gauge formulas. -/
namespace WebMu.Revised.LocalPaths
open Laurent Algebra Bar LocalDegreeProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem selected_prefix_from_paths (j : Fin 28) :
    ofList (selectedPrefix j)=ofList (expectedPrefix j) := by
  by_cases hj : j.val<27
  · let i : Fin 27 := ⟨j.val,hj⟩
    change ofList ((scaleTensor (shortPrefix i) (monomial (-height i))).getD wordEnd [])=_
    rw [scaleTensor_coordinate,raw_selected_prefix]
    have ha : ∀ i : Fin 27, mul (rawPrefixExpected i) (monomial (-height i)) = expectedPrefix i := by
      native_decide
    exact congrArg ofList (ha i)
  · have he : j.val=27 := by omega
    rw [selectedPrefix,prefixHat,scaleTensor_coordinate]
    simp [shortPrefix,he,expectedPrefix]

theorem selected_tail_upper_from_paths (j : Fin 27) :
    ofList (selectedTail j)=ofList (expectedTail j) := by
  rw [selectedTail,tail_upper_formula j wordEnd (by decide)]
  rw [ofList_shift,raw_selected_tail]
  have ha : ∀ i : Fin 27, mul (rawTailExpected i) (monomial (height i)) = expectedTail i := by
    native_decide
  exact congrArg ofList (ha j)


theorem selected_tail_scalar_from_paths (R : BarReferences) (A : AtomicCoordinates R)
    (F : AtlasRealization.RibbonFunctorReferences R) (G : CapDiagram.PositiveRibbonReferences R A F) :
    ofList (selectedTail 27)=ofList (monomial (-2) 2) := by
  rw [selectedTail,tail_scalar_formula R A F G wordEnd (by decide)]
  rw [ofList_add,ofList_shift,ofList_shift,tau2_selected_coordinate,tree_selected_coordinate]
  exact congrArg ofList (show add (mul one (monomial (-2)))
    (mul (monomial (-1)) (monomial (-1))) = monomial (-2) 2 from by native_decide)

theorem selected_tail_from_paths (R : BarReferences) (A : AtomicCoordinates R)
    (F : AtlasRealization.RibbonFunctorReferences R) (G : CapDiagram.PositiveRibbonReferences R A F)
    (j : Fin 28) : ofList (selectedTail j)=ofList (expectedTail j) := by
  by_cases hj : j.val<27
  · exact selected_tail_upper_from_paths ⟨j.val,hj⟩
  · have he : j.val=27 := by omega
    simpa only [he,expectedTail] using selected_tail_scalar_from_paths R A F G

theorem selected_prefix_constant_from_paths (j : Fin 28) :
    coeff (selectedPrefix j) 0 = if j.val=5 then 1 else 0 := by
  have h := congrArg (fun p => coefficient p 0) (selected_prefix_from_paths j)
  have ht : ∀ j : Fin 28, coeff (expectedPrefix j) 0 = if j.val=5 then 1 else 0 := by decide
  exact h.trans (ht j)

theorem selected_tail_constant_from_paths (R : BarReferences) (A : AtomicCoordinates R)
    (F : AtlasRealization.RibbonFunctorReferences R) (G : CapDiagram.PositiveRibbonReferences R A F)
    (j : Fin 28) : coeff (selectedTail j) 0 = 0 := by
  have h := congrArg (fun p => coefficient p 0) (selected_tail_from_paths R A F G j)
  have ht : ∀ j : Fin 28, coeff (expectedTail j) 0 = 0 := by decide
  exact h.trans (ht j)

theorem selected_tail_first_from_paths (R : BarReferences) (A : AtomicCoordinates R)
    (F : AtlasRealization.RibbonFunctorReferences R) (G : CapDiagram.PositiveRibbonReferences R A F)
    (j : Fin 28) : coeff (selectedTail j) (-1) = if j.val=5 then 1 else 0 := by
  have h := congrArg (fun p => coefficient p (-1)) (selected_tail_from_paths R A F G j)
  have ht : ∀ j : Fin 28, coeff (expectedTail j) (-1) = if j.val=5 then 1 else 0 := by decide
  exact h.trans (ht j)

end WebMu.Revised.LocalPaths
