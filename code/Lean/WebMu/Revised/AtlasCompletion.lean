import WebMu.Revised.AtlasSurgery

/-! Literal identity-wire completion and trivalent boundary contractions.
All source bindings below are verified against these declarative graph
relations, rather than assumed from a growth compiler. -/
namespace WebMu.Revised.AtlasSurgery
open Atlas Bar
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Attach a named degree-one boundary vertex to each ordered free port.
The order of `names` is the tensor input order, not circular boundary order. -/
def completionRelation (s : Build) (g : Graph) (names : List String) : Bool :=
  names.length == s.active.length && names.length == s.signs.length &&
  decide names.Nodup && names.all (freshVertex s) &&
  s.active.all (openPort s) &&
  let zs := (s.active.zip names).zipIdx
  g == ⟨s.graph.edges ++ zs.map (fun ((p,v),i) => (s.graph.nextEdge+i,p.1,v)),
    plugged s.graph.rotations (zs.map (fun ((p,_),i) => (p,s.graph.nextEdge+i))) ++
      zs.map (fun ((_,v),i) => (v,[s.graph.nextEdge+i])),
    s.graph.nextEdge+names.length,s.graph.circles⟩

/-- Fuse three named degree-one boundary points to the explicitly ordered
ports of a single trivalent vertex. Only those three incidences change. -/
def trivalentClosureRelation (g h : Graph) (names : List String) (v : String) : Bool :=
  names.length == 3 && decide names.Nodup && !(g.rotations.any fun z => z.1 == v) &&
  (names.all fun n => (rot g n).length == 1) &&
  let es := names.map (fun n => (rot g n)[0]!)
  decide es.Nodup &&
  let rename := fun w => if names.contains w then v else w
  h == ⟨g.edges.map (fun (e,a,b) => (e,rename a,rename b)),
    (g.rotations.filter fun (w,_) => !(names.contains w)) ++ [(v,es)],g.nextEdge,g.circles⟩

def inputNames : List String := ["b12","b11","b10"]
def prefixInputNames : List String := ["b9","b8","b7"]
def uncappedRoot : Graph := (attachInputs rootTrace.getLast!).getD default

theorem terminal_completion_checks : ∀ j : Fin 19,
    completionRelation (terminalTrace j.val).getLast! (constructedSummand j.val) inputNames=true := by
  native_decide

theorem root_completion_check : completionRelation rootTrace.getLast! uncappedRoot inputNames=true := by
  native_decide

theorem root_cap_check :
    trivalentClosureRelation uncappedRoot constructedRoot ["o0","o1","o2"] "eta"=true := by
  native_decide

theorem tail_complete_check : completionRelation tailTrace.getLast! tailTrace.getLast!.graph []=true := by
  native_decide

/-- The ordinary trivalent positive cap, expressed using one trivalent map
and one evaluation edge. No multi-step growth program occurs here. -/
def capPrimitive (r : Signs) : Circuit (positive 3 ++ r) r :=
  .up _ _ [(.lam,0),(.sigma,0)] (by simp [positive,ascendSigns])

def cappedRootCircuit : Circuit (positive 3) (positive 9) :=
  .compose rootCircuit (capPrimitive (positive 9))

theorem capped_root_tensor_check : ∀ i : Fin 27,
    sameEntries (evalSparse cappedRootCircuit (triple i)) (cap (rawB i))=true := by
  native_decide

theorem capped_root_tensor (i : Fin 27) (w : Word) :
    (evalSparse cappedRootCircuit (triple i)).getD w []=(cap (rawB i)).getD w [] :=
  sameEntries_getD _ _ (capped_root_tensor_check i) w

end WebMu.Revised.AtlasSurgery
