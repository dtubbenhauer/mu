import WebMu.Revised.TripodGraphChecks

namespace WebMu.Revised.TripodGraphs
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem each_tripod_deletion_valid (i : Fin 95) :
    tripodEntryValid i.val tripodData[i.val]! = true :=
  List.all_eq_true.mp all_95_tripod_deletions.2.2.2 i.val (List.mem_range.mpr i.isLt)

/-- Existential form of the graph correspondence, rather than only the
aggregate Boolean certificate. All graph constructions succeed. -/
theorem tripod_deletion_correspondence (i : Fin 95) :
    ∃ padded shortened deleted : Atlas.Graph,
      growthGraph 33 tripodData[i.val]!.paddedSteps = some padded ∧
      growthGraph 30 shortenedSteps[i.val]! = some shortened ∧
      deleteTripod padded = some deleted ∧
      allPositiveGraphValid 33 padded = true ∧
      allPositiveGraphValid 30 shortened = true ∧
      discValidN 33 padded = true ∧ discValidN 30 shortened = true ∧
      allPositiveGraphValid 30 deleted = true ∧ discValidN 30 deleted = true ∧
      Atlas.closedBijectionValid deleted shortened tripodData[i.val]!.iso = true ∧
      (boundaryNames 30).all (fun v => Atlas.lookup tripodData[i.val]!.iso.vertices v == some v) = true := by
  have h := each_tripod_deletion_valid i
  cases hp : growthGraph 33 tripodData[i.val]!.paddedSteps with
  | none => simp [tripodEntryValid,hp] at h
  | some padded =>
    cases hs : growthGraph 30 shortenedSteps[i.val]! with
    | none => simp [tripodEntryValid,hp,hs] at h
    | some shortened =>
      cases hd : deleteTripod padded with
      | none => simp [tripodEntryValid,hp,hs,hd] at h
      | some deleted =>
        simp only [tripodEntryValid,hp,hs,hd,Bool.and_eq_true] at h
        rcases h.2 with ⟨⟨⟨⟨ha,hb⟩,hc⟩,hd'⟩,⟨⟨⟨he,hf⟩,hg⟩,hh⟩⟩
        exact ⟨padded,shortened,deleted,rfl,rfl,hd,ha,hb,hc,hd',he,hf,hg,hh⟩

/-- Explicit preservation of the two bipartite vertex types by each
ribbon isomorphism, in addition to fixed boundary names and cyclic orders. -/
def tripodOrientationPreserved (i : Nat) : Bool :=
  let p := (growthGraph 33 tripodData[i]!.paddedSteps).getD default
  let q := (growthGraph 30 shortenedSteps[i]!).getD default
  let g := (deleteTripod p).getD default
  let sg := boundaryColor 30 g
  let sq := boundaryColor 30 q
  tripodData[i]!.iso.vertices.all (fun (v,w) => Atlas.lookup sg v == Atlas.lookup sq w)

theorem all_95_orientations_preserved :
    ∀ i : Fin 95, tripodOrientationPreserved i.val = true := by native_decide

#print axioms all_95_tripod_deletions
#print axioms tripod_deletion_correspondence
#print axioms all_95_orientations_preserved
end WebMu.Revised.TripodGraphs
