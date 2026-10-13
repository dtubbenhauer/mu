import WebMu.Revised.AtlasClosedSemantics
import WebMu.Revised.Sparse

/-! The semantic atlas theorems with their inputs tied to the defining
capped block, growth strings, shortened prefix, tail and four closed cores. -/
namespace WebMu.Revised.Atlas
open Laurent Algebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def identityBijection (g : Graph) : Bijection :=
  ⟨g.rotations.map (fun (v,_) => (v,v)),g.edges.map (fun (e,_) => (e,e))⟩

def constructedRoot : Graph := constructRoot.getD default

def constructedSummand (i : Nat) : Graph :=
  let (gs,sm) := (correctionSteps ++ hSteps)[i]!
  (constructSummand gs sm).getD default

theorem constructed_open_sources_exist :
    constructRoot = some constructedRoot ∧
    ∀ i : Fin 19, let (gs,sm) := (correctionSteps ++ hSteps)[i.val]!
      constructSummand gs sm = some (constructedSummand i.val) := by native_decide

theorem constructed_root_admissible : OpenAdmissible constructedRoot := by
  refine ⟨graphColor constructedRoot,?_⟩
  native_decide

theorem constructed_summand_admissible (i : Fin 19) :
    OpenAdmissible (constructedSummand i.val) := by
  have h : ∀ i : Fin 19,
      graphValid (constructedSummand i.val) (graphColor (constructedSummand i.val)) = true ∧
      discValid (constructedSummand i.val) = true := by native_decide
  exact ⟨_,h i⟩

theorem capped_block_evaluation (R : OpenSpiderReferences) :
    R.eval constructedRoot = openValue R 0 := by
  exact R.isotopy _ _ rootBijection constructed_root_admissible
    (open_node_admissible 0) (by native_decide)

theorem growth_summand_evaluation (R : OpenSpiderReferences) (i : Fin 19) :
    R.eval (constructedSummand i.val) = summandValue R i.val := by
  have h : ∀ i : Fin 19, bijectionValid (constructedSummand i.val)
      atlasSummands[i.val]! (identityBijection (constructedSummand i.val)) = true := by native_decide
  exact R.isotopy _ _ _ (constructed_summand_admissible i) (summand_admissible i) (h i)

/-- ηB=dD+H in every evaluation satisfying the uniform spider relations,
with the root constructed from blockSteps and terminals from the defining
correctionSteps/hSteps. Boundary names and cyclic orders are fixed. -/
theorem open_growth_identity (R : OpenSpiderReferences) :
    R.eval constructedRoot =
      ofList d * total (List.range 8) (fun i => R.eval (constructedSummand i)) +
      total (List.range' 8 11) (fun i => R.eval (constructedSummand i)) := by
  rw [capped_block_evaluation,open_atlas_identity]
  have hD : total (List.range 8) (summandValue R) =
      total (List.range 8) (fun i => R.eval (constructedSummand i)) := by
    apply total_congr_mem
    intro i hi
    have hi' := List.mem_range.mp hi
    exact (growth_summand_evaluation R ⟨i,by omega⟩).symm
  have hH : total (List.range' 8 11) (summandValue R) =
      total (List.range' 8 11) (fun i => R.eval (constructedSummand i)) := by
    apply total_congr_mem
    intro i hi
    have hi' := List.mem_range'.mp hi
    exact (growth_summand_evaluation R ⟨i,by omega⟩).symm
  rw [hD,hH]

/-- Same order as closedTargets: B,H,D,prefix,tail and the four cores. -/
def constructedClosedSources : List Graph :=
  [ (closeTripods atlasNodes[0]!.graph 12).getD default,
    (closeTripods atlasNodes[1]!.graph 12).getD default,
    (closeTripods atlasNodes[23]!.graph 12).getD default,
    constructClosedShortPrefix.getD default,
    constructClosedTail.getD default,
    closedCores[0]!,closedCores[1]!,closedCores[2]!,closedCores[3]! ]

theorem constructed_closed_sources_exist :
    (∀ i : Fin 3, closeTripods atlasNodes[([0,1,23] : List Nat)[i.val]!]!.graph 12 =
      some constructedClosedSources[i.val]!) ∧
    constructClosedShortPrefix = some constructedClosedSources[3]! ∧
    constructClosedTail = some constructedClosedSources[4]! := by native_decide

theorem constructed_closed_admissible (i : Fin 9) :
    ClosedAdmissible constructedClosedSources[i.val]! := by
  have h : ∀ i : Fin 9,
      closedGraphValid constructedClosedSources[i.val]!
        (graphColor constructedClosedSources[i.val]!) = true ∧
      closedPlanar constructedClosedSources[i.val]! = true := by native_decide
  exact ⟨_,h i⟩

theorem constructed_closed_evaluation (R : ClosedSpiderReferences) (i : Fin 9) :
    R.eval constructedClosedSources[i.val]! = closedEvaluation R closedRoots[i.val]! := by
  have hi : ∀ i : Fin 9, closedRoots[i.val]! < 209 := by native_decide
  have he : ∀ i : Fin 9, closedBijectionValid constructedClosedSources[i.val]!
      closedNodes[closedRoots[i.val]!]!.graph
      (identityBijection constructedClosedSources[i.val]!) = true := by native_decide
  exact R.isotopy _ _ _ (constructed_closed_admissible i)
    (closed_node_admissible ⟨_,hi i⟩) (he i)

/-- The scalar evaluations of the nine actual defining closed graphs. -/
theorem closed_sources_evaluated (R : ClosedSpiderReferences) :
    constructedClosedSources.map R.eval = closedTargets.map ofList := by
  rw [← closed_atlas_evaluations R]
  change [R.eval constructedClosedSources[0]!, R.eval constructedClosedSources[1]!,
    R.eval constructedClosedSources[2]!, R.eval constructedClosedSources[3]!,
    R.eval constructedClosedSources[4]!, R.eval constructedClosedSources[5]!,
    R.eval constructedClosedSources[6]!, R.eval constructedClosedSources[7]!,
    R.eval constructedClosedSources[8]!] = _
  have h (i : Nat) (hi : i < 9) : R.eval constructedClosedSources[i]! =
      closedEvaluation R closedRoots[i]! := constructed_closed_evaluation R ⟨i,hi⟩
  rw [h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),
    h 4 (by decide),h 5 (by decide),h 6 (by decide),h 7 (by decide),h 8 (by decide)]
  rfl

#print axioms open_growth_identity
#print axioms closed_sources_evaluated
end WebMu.Revised.Atlas
