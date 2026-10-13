import WebMu.Revised.LocalPathConsequences

/-! End tensors and their nonpositive paths. The finite comparisons here
identify literal tensor-product definitions with their displayed cup/Y strings;
degree conclusions then follow from the individual paths. -/
namespace WebMu.Revised.LocalPaths
open Laurent Algebra Bar LocalDegreeProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def tripodString : List Step := [(.y,0),(.cup,0)]
def twoTripodString : List Step := tripodString ++ tripodString
def threeTripodString : List Step := tripodString ++ twoTripodString

theorem tripod_strings :
    sameEntries (expand tripodString (singleton [])) tripod = true ∧
    sameEntries (expand twoTripodString (singleton [])) tau2 = true ∧
    sameEntries (expand threeTripodString (singleton [])) tau3 = true := by native_decide

theorem nonpositive_tripod_paths :
    (downPaths tripodString []).all (fun p => p.degree ≤ 0) = true ∧
    (downPaths twoTripodString []).all (fun p => p.degree ≤ 0) = true ∧
    (downPaths threeTripodString []).all (fun p => p.degree ≤ 0) = true := by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply List.all_eq_true.mpr
    intro p hp
    exact decide_eq_true (AAAOuter.nonpositive _ (by simp [tripodString,twoTripodString,threeTripodString,GrowthBridge.opBound]) [] p hp)

theorem tau2_degree (w : Word) : DegreeLE (tau2.getD w []) 0 := by
  rw [← sameEntries_getD _ _ tripod_strings.2.1]
  apply paths_degree_bound
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp nonpositive_tripod_paths.2.1 p hp)

theorem tau3_degree (w : Word) : DegreeLE (tau3.getD w []) 0 := by
  rw [← sameEntries_getD _ _ tripod_strings.2.2]
  apply paths_degree_bound
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp nonpositive_tripod_paths.2.2 p hp)

theorem tree_nonpositive_paths :
    (downPaths [(.y,1),(.y,2),(.y,1),(.y,0),(.cup,0)] []).all (fun p => p.degree ≤ 0) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  exact decide_eq_true (AAAOuter.nonpositive _ (by simp [GrowthBridge.opBound]) [] p hp)

theorem tailTree_degree (w : Word) : DegreeLE (tailTree.getD w []) 0 := by
  apply paths_degree_bound
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp tree_nonpositive_paths p hp)

end WebMu.Revised.LocalPaths
