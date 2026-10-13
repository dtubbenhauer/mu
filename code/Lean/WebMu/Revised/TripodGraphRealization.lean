import WebMu.Revised.TripodGraphPresentation
import WebMu.Revised.InsertionRealization

/-! A uniform disjoint-tripod functor law and its complete geometric witnesses.
The law is about a literal disjoint component and ordered boundary relabeling;
it mentions neither deleteTripod nor graph-growth execution. -/
namespace WebMu.Revised.TripodGraphRealization
open Atlas AtlasSurgery AtlasRealization TripodGraphs TripodGraphPresentation Bar
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure RemovalWitness where
  remainder : Graph
  center : String
  edges : Nat × Nat × Nat
  centerRotation : List Nat
  iso : Bijection
  deriving Inhabited

def relabelAfter (k n : Nat) (v : String) : String :=
  (lookup ((List.range n).map (fun i => (s!"b{k+4+i}",s!"b{k+1+i}"))) v).getD v

def relabelGraph (f : String → String) (g : Graph) : Graph :=
  {g with
    edges := g.edges.map (fun (e,a,b) => (e,f a,f b)),
    rotations := g.rotations.map (fun (v,r) => (f v,r))}

/-- Exact disjoint-union decomposition, followed by an oriented ribbon
isomorphism fixing the surviving ordered boundary after its stated renaming.
The tripod's cyclic order is a,c,b, matching the positive tensor tau. -/
def removalRelation (k n : Nat) (g h : Graph) (w : RemovalWitness) : Bool :=
  let a := s!"b{k+1}"
  let b := s!"b{k+2}"
  let c := s!"b{k+3}"
  let (ea,eb,ec) := w.edges
  let removed := [a,b,c,w.center]
  decide removed.Nodup && decide [ea,eb,ec].Nodup &&
  !(outputNames (k+3+n)).contains w.center &&
  w.remainder.rotations.all (fun (v,_) => !(removed.contains v)) &&
  w.remainder.edges.all (fun (e,u,v) =>
    !([ea,eb,ec].contains e) && !(removed.contains u) && !(removed.contains v)) &&
  cyclicEqual w.centerRotation [ea,ec,eb] &&
  sameGraph g ⟨w.remainder.edges ++ [(ea,a,w.center),(eb,b,w.center),(ec,c,w.center)],
    w.remainder.rotations ++ [(a,[ea]),(b,[eb]),(c,[ec]),(w.center,w.centerRotation)],
    g.nextEdge,w.remainder.circles⟩ &&
  closedBijectionValid (relabelGraph (relabelAfter k n) w.remainder) h w.iso &&
  (outputNames (k+n)).all (fun v => lookup w.iso.vertices v == some v)

/-- The tensor functor's ordinary monoidal rule for a disjoint elementary
tripod at arbitrary prefix/suffix lengths, and ordinary ordered isotopy.
No particular source family or compiler is an assumption. -/
structure References (R : BarReferences) (F : RibbonFunctorReferences R) where
  disjoint_tripod : ∀ k n g h w,
    Diagram g [] (outputNames (k+3+n)) [] ((positive k++positive 3)++positive n) →
    Diagram h [] (outputNames (k+n)) [] (positive k++positive n) →
    removalRelation k n g h w=true → ∀ x,
    F.graph [] (outputNames (k+3+n)) [] ((positive k++positive 3)++positive n) g x =
      R.tensorMap (R.tensorMap (id : R.Space (positive k) → R.Space (positive k))
        (R.interpret tripodCircuit)) (id : R.Space (positive n) → R.Space (positive n))
        (castSpace R (by simp)
          (F.graph [] (outputNames (k+n)) [] (positive k++positive n) h x))

def sourceWitness (i : Fin 95) : RemovalWitness :=
  let g := graph (true,i)
  let ea := (rot g "b7")[0]!
  let eb := (rot g "b8")[0]!
  let ec := (rot g "b9")[0]!
  let v := (other g ea "b7").getD ""
  let removed := ["b7","b8","b9",v]
  ⟨{g with
      edges := g.edges.filter (fun (_,a,b) => !(removed.contains a || removed.contains b)),
      rotations := g.rotations.filter (fun (a,_) => !(removed.contains a))},
    v,(ea,eb,ec),rot g v,tripodData[i.val]!.iso⟩

theorem all_removal_relations : ∀ i : Fin 95,
    removalRelation 6 24 (graph (true,i)) (graph (false,i)) (sourceWitness i)=true := by
  native_decide

/-- All 95 actual graph morphisms factor through the literal after-six
insertion. The graph-to-original-growth identification is supplied separately
by primitive growth realization, not by the disjoint-union reference law. -/
theorem all_graph_factorizations (R : BarReferences) (F : RibbonFunctorReferences R)
    (G : References R F) (i : Fin 95) (x : R.Space []) :
    F.graph [] (outputNames 33) [] (positive 33) (graph (true,i)) x =
      R.interpret (Insertion.insertionCircuit 24)
        (F.graph [] (outputNames 30) [] (positive 30) (graph (false,i)) x) := by
  exact G.disjoint_tripod 6 24 _ _ (sourceWitness i)
    (source_diagram (true,i)) (source_diagram (false,i)) (all_removal_relations i) x

theorem all_circuit_factorizations (R : BarReferences) (F : RibbonFunctorReferences R)
    (G : References R F) (i : Fin 95) (x : R.Space []) :
    R.interpret (sourceCircuit (true,i)) x =
      R.interpret (Insertion.insertionCircuit 24)
        (R.interpret (sourceCircuit (false,i)) x) := by
  have h := all_graph_factorizations R F G i x
  have hp : F.graph [] (outputNames 33) [] (positive 33) (graph (true,i)) x =
      R.interpret (sourceCircuit (true,i)) x := source_graph_interpretation R F (true,i) x
  have hq : F.graph [] (outputNames 30) [] (positive 30) (graph (false,i)) x =
      R.interpret (sourceCircuit (false,i)) x := source_graph_interpretation R F (false,i) x
  exact hp.symm.trans (h.trans (congrArg (R.interpret (Insertion.insertionCircuit 24)) hq))

#print axioms all_circuit_factorizations
end WebMu.Revised.TripodGraphRealization
