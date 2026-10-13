import WebMu.Revised.CapDiagram
import WebMu.Revised.TripodGraphRealization

/-! The local D1 = P tensor tau factorization, as an actual disjoint
component of the ordered ribbon graph. The input boundary stays fixed. -/
namespace WebMu.Revised.CapDiagram
open Atlas AtlasSurgery AtlasRealization Bar TripodGraphRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def prefixRemovalWitness : RemovalWitness :=
  ⟨prefixRemainder,prefixTripodCenter,prefixTripodEdges,prefixTripodRotation,prefixTripodIso⟩

theorem prefix_geometry :
    completionRelation prefixTrace.getLast! prefixGraph inputNames=true ∧
    removalRelation 6 0 (constructedSummand 0) prefixGraph prefixRemovalWitness=true ∧
    inputNames.all (fun v => lookup prefixTripodIso.vertices v==some v)=true := by
  native_decide

theorem prefix_diagram :
    Diagram prefixGraph inputNames (outputNames 6) (positive 3) (positive 6) := by
  exact diagram_input_cast source_input_signs.2.2.1
    (Diagram.completion (outputNames 6) inputNames prefixTrace.getLast! prefixGraph
      prefix_presented prefix_geometry.1)

theorem prefix_graph_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (x : R.Space (positive 3)) :
    F.graph inputNames (outputNames 6) (positive 3) (positive 6) prefixGraph x =
      R.interpret AtlasSurgery.prefixCircuit x := by
  exact completed_path_interpretation R F (outputNames 6) inputNames (by decide)
    prefixGraph prefixPath prefix_presented prefix_geometry.1 source_input_signs.2.2.1 x

/-- Ordinary monoidality for a disjoint positive tripod appended after an
arbitrary open tensor map. The identity on the surviving ordered input
boundary is required explicitly in addition to the output labels. -/
structure BoundaryTripodReferences (R : BarReferences) (F : RibbonFunctorReferences R) where
  disjoint_tripod : ∀ k ins s g h witness,
    Diagram g ins (outputNames (k+3)) s (positive k++positive 3) →
    Diagram h ins (outputNames k) s (positive k) →
    removalRelation k 0 g h witness=true →
    ins.all (fun v => lookup witness.iso.vertices v==some v)=true → ∀ x,
    F.graph ins (outputNames (k+3)) s (positive k++positive 3) g x =
      R.interpret ((Circuit.tensor (.identity (positive k)) tripodCircuit).cast (by simp) rfl)
        (F.graph ins (outputNames k) s (positive k) h x)

/-- No coefficient comparison establishes the disjoint component: the
literal incidence lists isolate the final three output leaves and center,
and the survivor isomorphism preserves every input and output label. -/
theorem D1_graph_factorization (R : BarReferences) (F : RibbonFunctorReferences R)
    (G : BoundaryTripodReferences R F) (x : R.Space (positive 3)) :
    F.graph inputNames (outputNames 9) (positive 3) (positive 9) (constructedSummand 0) x =
      R.interpret Insertion.prefixCircuit
        (F.graph inputNames (outputNames 6) (positive 3) (positive 6) prefixGraph x) := by
  exact G.disjoint_tripod 6 inputNames (positive 3) (constructedSummand 0) prefixGraph
    prefixRemovalWitness (.open (constructed_summand_admissible 0)) prefix_diagram
    prefix_geometry.2.1 prefix_geometry.2.2 x

/-- The actual typed tensor maps satisfy D1 = P tensor tau, with tau in
positions seven through nine. The source maps are realized by the proved
primitive-presentation interpreter. -/
theorem D1_circuit_factorization (R : BarReferences) (F : RibbonFunctorReferences R)
    (G : BoundaryTripodReferences R F) (x : R.Space (positive 3)) :
    R.interpret (terminalCircuit 0) x =
      R.interpret Insertion.prefixCircuit (R.interpret AtlasSurgery.prefixCircuit x) := by
  have h := D1_graph_factorization R F G x
  exact (terminal_graph_interpretation R F (0 : Fin 19) x).symm.trans
    (h.trans (congrArg (R.interpret Insertion.prefixCircuit) (prefix_graph_interpretation R F x)))

#print axioms D1_circuit_factorization
end WebMu.Revised.CapDiagram
