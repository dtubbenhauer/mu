import WebMu.Revised.RestrictedSelectedRows
import WebMu.Revised.LocalLatticeProof
import WebMu.Revised.LocalEndpointRows
import WebMu.Revised.WrittenProofMain

/-! Every field of the global proof's local package is discharged here.
No lattice, leading-state or selected-row conclusion is a reference input. -/
namespace WebMu.Revised.WrittenProof
open Laurent Algebra Bar LocalDegreeProof AtlasRealization CapDiagram

def localProperties (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (T : BoundaryTripodReferences R F) : Properties where
  prefix_nonpositive := prefix_nonpositive_from_paths
  block_nonpositive := block_nonpositive_from_local R A F G T
  tail_nonpositive := tail_nonpositive_from_local R A F G
  prefix_constant := prefix_constant_from_paths
  block_constant := block_constant_from_local R A F G T
  tail_constant := tail_constant_from_local R A F G
  selected_prefix_constant := by
    intro i
    simpa only [Fin.ext_iff] using LocalPaths.selected_prefix_constant_from_paths i
  selected_tail_constant := LocalPaths.selected_tail_constant_from_paths R A F G
  selected_ABC_row := by
    intro i
    simpa only [Fin.ext_iff] using (WeightConservation.selected_rows_from_weights_and_diagrams R A F G T i).1
  selected_scalar_row := by
    intro i
    simpa only [Fin.ext_iff] using (WeightConservation.selected_rows_from_weights_and_diagrams R A F G T i).2
  selected_tail_ABC_first := by
    simpa using LocalPaths.selected_tail_first_from_paths R A F G 5
  selected_tail_scalar_first := by
    simpa using LocalPaths.selected_tail_first_from_paths R A F G 27

#print axioms localProperties
end WebMu.Revised.WrittenProof
