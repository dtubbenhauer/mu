import WebMu.Revised.CapDiagramTripod

/-! The six-boundary core displayed in the two-digon figure is the literal
core of C; both spectator tripods remain untouched in each local reduction. -/
namespace WebMu.Revised.CapDiagram
open Atlas AtlasSurgery AtlasRealization Bar
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def cCoreAtoms : List Atom := [.merge 0,.split 1,.merge 0,.arc 1,.merge 0,.arc 0]
def cCoreNames := ["o0","o1","o2"] ++ outputNames 3
def cCoreTrace := (trace (start cCoreNames) cCoreAtoms).getD []
def cCoreGraph := cCoreTrace.getLast!.graph

def withoutSpectators (g : Graph) : Graph :=
  {g with
    edges := g.edges.filter (fun (_,a,_) => !(cSpectatorVertices.contains a)),
    rotations := g.rotations.filter (fun (v,_) => !(cSpectatorVertices.contains v))}

/-- Exact disjoint union: all six spectator leaves, both centers, all six
edges, and their cyclic orders are unchanged; every other incidence belongs
to the complementary core. -/
def unchangedSpectators (g : Graph) : Bool :=
  let core := withoutSpectators g
  decide ((core.rotations.map Prod.fst ++ cSpectatorGraph.rotations.map Prod.fst).Nodup) &&
  core.edges.all (fun (_,a,b) =>
    !(cSpectatorVertices.contains a) && !(cSpectatorVertices.contains b)) &&
  cSpectatorGraph.edges.all (fun (_,a,b) =>
    cSpectatorVertices.contains a && cSpectatorVertices.contains b) &&
  sameGraph g ⟨core.edges++cSpectatorGraph.edges,
    core.rotations++cSpectatorGraph.rotations,g.nextEdge,0⟩

/-- The displayed downward string Y0 H0 a1 Y0 a0 is expanded into its
literal primitive vertices and arcs, and all six boundary labels are fixed. -/
theorem c_core_source :
    cCoreAtoms=[(.y,0),(.h,0),(.cup,1),(.y,0),(.cup,0)].flatMap expandGrowth ∧
    traceValid cCoreTrace cCoreAtoms=true ∧
    cCoreTrace.head?=some (start cCoreNames) ∧
    cCoreTrace.getLast!.signs=[] ∧
    completionRelation cCoreTrace.getLast! cCoreGraph []=true ∧
    closedBijectionValid (withoutSpectators (sourceGraph 0)) cCoreGraph cCoreIso=true ∧
    cCoreNames.all (fun v => lookup cCoreIso.vertices v==some v)=true ∧
    unchangedSpectators (sourceGraph 0)=true := by native_decide

/-- This is the precise meaning of suppressing the two common tripods in
the figure: both local face replacements act entirely in the core. -/
theorem c_spectators_unchanged :
    unchangedSpectators cRoot=true ∧ unchangedSpectators cMiddle=true ∧
    unchangedSpectators cEnd=true ∧
    cFirstFace.vertices.all (fun v => !(cSpectatorVertices.contains v))=true ∧
    cSecondFace.vertices.all (fun v => !(cSpectatorVertices.contains v))=true := by
  native_decide

/-- The displayed core string has the stated leading word ABACBC. -/
theorem c_core_leading_word :
    singleConstant (expand [(.y,0),(.h,0),(.cup,1),(.y,0),(.cup,0)] (singleton []))
      [0,1,0,2,1,2]=true := by native_decide

#print axioms c_core_source
#print axioms c_spectators_unchanged
end WebMu.Revised.CapDiagram
