import WebMu.Revised.CapDiagramSources

/-! The two small cap proofs as literal oriented ribbon reductions.
C is reduced by two successive digons; Q by its right-hand square and the
left-hand digon in the first smoothing. The terminal isomorphisms fix all
output labels and cyclic orders. All graph evaluations below are defined
using the actual typed spider functor and standard tensor coordinates. -/
namespace WebMu.Revised.CapDiagram
open Atlas AtlasSurgery AtlasRealization Bar Algebra Laurent
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Signed incidence validation for an arbitrary all-positive ordered
boundary. The signs on all internal vertices and every edge are checked. -/
def positiveGraphValid (n : Nat) (g : Graph) (signs : List (String × Bool)) : Bool :=
  let names := outputNames n
  g.circles == 0 &&
  decide ((g.edges.map Prod.fst).Nodup) &&
  decide ((g.rotations.map Prod.fst).Nodup) &&
  decide ((signs.map Prod.fst).Nodup) &&
  signs.length == g.rotations.length &&
  g.edges.all (fun (e,a,b) => e < g.nextEdge && a != b &&
    (lookup g.rotations a).isSome && (lookup g.rotations b).isSome &&
    match lookup signs a,lookup signs b with
      | some sa,some sb => sa != sb
      | _,_ => false) &&
  g.rotations.all (fun (v,r) =>
    decide r.Nodup && r.length == (if names.contains v then 1 else 3) &&
    r.all (fun e => (other g e v).isSome) &&
    (g.edges.filter (fun (_,a,b) => a == v || b == v)).length == r.length) &&
  names.all (fun v => (lookup g.rotations v).isSome && lookup signs v == some true)

/-- The boundary rim is adjoined in the prescribed circular order; orbit
and Euler checks certify its oriented disc embedding, as in AtlasPlanarity. -/
def positiveRim (n : Nat) (g : Graph) : Graph :=
  let names := outputNames n
  let es := (List.range n).map fun i => (g.nextEdge+i,names[i]!,names[(i+1)%n]!)
  let rs := g.rotations.map fun (v,r) =>
    if names.contains v then
      let i := names.idxOf v
      (v,r ++ [g.nextEdge+i,g.nextEdge+(i+n-1)%n])
    else (v,r)
  ⟨g.edges++es,rs,g.nextEdge+n,g.circles⟩

def positiveDiscValid (n : Nat) (g : Graph) : Bool :=
  let g := positiveRim n g
  let ds := darts g
  let walks := ds.map fun d => orbit g d (ds.length+1) d []
  let faces := (List.range ds.length).filter fun i => match walks[i]! with
    | none => false
    | some ws => ws.all fun d => i ≤ ds.idxOf d
  let reached := reachable g g.rotations.length ["b1"]
  g.rotations.all (fun (v,_) => reached.contains v) &&
  walks.all (fun o => match o with
    | none => false
    | some ws => decide ws.Nodup && ws.all ds.contains) &&
  g.rotations.length + faces.length == g.edges.length + 2

def Admissible (n : Nat) (g : Graph) : Prop :=
  ∃ signs, positiveGraphValid n g signs=true ∧ positiveDiscValid n g=true

def boundaryIsomorphism (n : Nat) (g h : Graph) (iso : Bijection) : Bool :=
  closedBijectionValid g h iso && (outputNames n).all (fun v => lookup iso.vertices v==some v)

def diagramCoordinate (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (n : Nat) (g : Graph) (w : Word) : Poly :=
  A.coord (positive n) (F.graph [] (outputNames n) [] (positive n) g R.vacuum) w

/-- The ordinary isotopy, square and digon laws, uniform over all positive
boundaries and actual spider-functor coordinates. No C, Q, growth compiler,
evaluator, or cap identity appears in these prior-work inputs. -/
structure PositiveRibbonReferences (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) where
  isotopy : ∀ n g h iso, Admissible n g → Admissible n h →
    boundaryIsomorphism n g h iso=true → ∀ w,
    diagramCoordinate R A F n g w=diagramCoordinate R A F n h w
  square : ∀ n g f h k, Admissible n g → Admissible n h → Admissible n k →
    f.vertices.length=4 → resolvedTo g f [(0,1),(2,3)] h=true →
    resolvedTo g f [(1,2),(3,0)] k=true → ∀ w,
    diagramCoordinate R A F n g w=
      diagramCoordinate R A F n h w+diagramCoordinate R A F n k w
  digon : ∀ n g f h, Admissible n g → Admissible n h →
    f.vertices.length=2 → resolvedTo g f [(0,1)] h=true → ∀ w,
    diagramCoordinate R A F n g w=ofList d*diagramCoordinate R A F n h w

theorem c_admissible : Admissible 9 cRoot ∧ Admissible 9 cMiddle ∧ Admissible 9 cEnd := by
  exact ⟨⟨cRootSigns,by native_decide,by native_decide⟩,
    ⟨cMiddleSigns,by native_decide,by native_decide⟩,
    ⟨cEndSigns,by native_decide,by native_decide⟩⟩

theorem q_admissible : Admissible 6 qRoot ∧ Admissible 6 qDigonBranch ∧
    Admissible 6 qTreeBranch ∧ Admissible 6 qEnd := by
  exact ⟨⟨qRootSigns,by native_decide,by native_decide⟩,
    ⟨qDigonBranchSigns,by native_decide,by native_decide⟩,
    ⟨qTreeBranchSigns,by native_decide,by native_decide⟩,
    ⟨qEndSigns,by native_decide,by native_decide⟩⟩

theorem terminal_admissible : Admissible 9 (sourceGraph 2) ∧
    Admissible 6 (sourceGraph 3) ∧ Admissible 6 (sourceGraph 4) := by
  exact ⟨⟨terminalSigns[0]!,by native_decide,by native_decide⟩,
    ⟨terminalSigns[1]!,by native_decide,by native_decide⟩,
    ⟨terminalSigns[2]!,by native_decide,by native_decide⟩⟩

/-- Explicit faces and the complete before/after incidence and rotation
lists are checked independently of tensor evaluation. -/
theorem c_reductions :
    resolvedTo cRoot cFirstFace [(0,1)] cMiddle=true ∧
    resolvedTo cMiddle cSecondFace [(0,1)] cEnd=true ∧
    boundaryIsomorphism 9 cEnd (sourceGraph 2) cTerminalIso=true := by native_decide

theorem q_reductions :
    resolvedTo qRoot qSquareFace [(0,1),(2,3)] qDigonBranch=true ∧
    resolvedTo qRoot qSquareFace [(1,2),(3,0)] qTreeBranch=true ∧
    resolvedTo qDigonBranch qDigonFace [(0,1)] qEnd=true ∧
    boundaryIsomorphism 6 qEnd (sourceGraph 3) qTripodIso=true ∧
    boundaryIsomorphism 6 qTreeBranch (sourceGraph 4) qTreeIso=true := by native_decide

theorem c_graph_identity (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F) (w : Word) :
    diagramCoordinate R A F 9 cRoot w =
      ofList d*(ofList d*diagramCoordinate R A F 9 (sourceGraph 2) w) := by
  rw [G.digon 9 cRoot cFirstFace cMiddle c_admissible.1 c_admissible.2.1 rfl c_reductions.1,
    G.digon 9 cMiddle cSecondFace cEnd c_admissible.2.1 c_admissible.2.2 rfl c_reductions.2.1,
    G.isotopy 9 cEnd (sourceGraph 2) cTerminalIso c_admissible.2.2 terminal_admissible.1 c_reductions.2.2]

theorem q_graph_identity (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F) (w : Word) :
    diagramCoordinate R A F 6 qRoot w =
      ofList d*diagramCoordinate R A F 6 (sourceGraph 3) w+
        diagramCoordinate R A F 6 (sourceGraph 4) w := by
  rw [G.square 6 qRoot qSquareFace qDigonBranch qTreeBranch q_admissible.1
      q_admissible.2.1 q_admissible.2.2.1 rfl q_reductions.1 q_reductions.2.1,
    G.digon 6 qDigonBranch qDigonFace qEnd q_admissible.2.1 q_admissible.2.2.2 rfl q_reductions.2.2.1,
    G.isotopy 6 qEnd (sourceGraph 3) qTripodIso q_admissible.2.2.2 terminal_admissible.2.1 q_reductions.2.2.2.1,
    G.isotopy 6 qTreeBranch (sourceGraph 4) qTreeIso q_admissible.2.2.1 terminal_admissible.2.2 q_reductions.2.2.2.2]

/-- Full tensor-coordinate eta C identity obtained from two diagrammatic
digon removals, not from `cap_C` or `cap_C_check`. -/
theorem cap_C_diagrammatic (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (w : Word) (hw : validWord 9 w=true) :
    ofList ((cap rawC).getD w [])=ofList d*(ofList d*ofList (tau3.getD w [])) := by
  have h := c_graph_identity R A F G w
  unfold diagramCoordinate at h
  rw [c_root_interpretation, A.closed_circuit cCappedCircuit w hw] at h
  have he := sameEntries_getD _ _ source_tensor_checks.2.2.2.2.2.1 w
  rw [he] at h
  change _ = ofList d*(ofList d*A.coord (positive (sourceWidth 2))
    (F.graph [] (sourceNames 2) [] (positive (sourceWidth 2)) (sourceGraph 2) R.vacuum) w) at h
  rw [source_interpretation, A.closed_circuit (sourceCircuit 2) w hw,
    sameEntries_getD _ _ source_tensor_checks.2.2.1 w] at h
  exact h

/-- Full tensor-coordinate eta Q identity obtained from the displayed
right-hand square and its left digon branch, not from `cap_Q_check`. -/
theorem cap_Q_diagrammatic (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (w : Word) (hw : validWord 6 w=true) :
    ofList ((cap rawQ).getD w [])=ofList d*ofList (tau2.getD w [])+ofList (tailTree.getD w []) := by
  have h := q_graph_identity R A F G w
  unfold diagramCoordinate at h
  rw [q_root_interpretation, A.closed_circuit qCappedCircuit w hw,
    sameEntries_getD _ _ source_tensor_checks.2.2.2.2.2.2 w] at h
  change _ = ofList d*A.coord (positive (sourceWidth 3))
      (F.graph [] (sourceNames 3) [] (positive (sourceWidth 3)) (sourceGraph 3) R.vacuum) w+
    A.coord (positive (sourceWidth 4))
      (F.graph [] (sourceNames 4) [] (positive (sourceWidth 4)) (sourceGraph 4) R.vacuum) w at h
  rw [source_interpretation, source_interpretation,
    A.closed_circuit (sourceCircuit 3) w hw,A.closed_circuit (sourceCircuit 4) w hw,
    sameEntries_getD _ _ source_tensor_checks.2.2.2.1 w,
    sameEntries_getD _ _ source_tensor_checks.2.2.2.2.1 w] at h
  exact h

#print axioms cap_C_diagrammatic
#print axioms cap_Q_diagrammatic
end WebMu.Revised.CapDiagram
