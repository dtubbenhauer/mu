import WebMu.Revised.WrittenProofEndpoint
import WebMu.Revised.RSKCellReferences

/-! Preferred endpoints: the actual row-insertion and recording algorithms
are supplied by the proved three-block bumping calculation. Only the cited
cell classification, not a row-reading conclusion, remains an input. The
local properties used below are assembled from the staged written proof. -/
namespace WebMu.Revised
open Bar AtlasRealization CapDiagram Family

theorem paper_canonicality_faithful (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (T : BoundaryTripodReferences R F)
    (C : CanonicalReferences A.tensorBar) (m : Nat) :
    tensorOriginal m=C.canonical m (leadingBoundary m) :=
  paper_canonicality_written R A F G T C m

theorem paper_main_faithful (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (T : BoundaryTripodReferences R F)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (D : FKKReferences A.tensorBar C K) (S : RSKBumping.CellClassification)
    (B : Bruhat.References) (r : Nat) :
    SubwordFamilyConclusion K (RSKBumping.cellReferences S) r :=
  paper_main_written R A F G T C K D (RSKBumping.cellReferences S) B r

theorem paper_unbounded_faithful (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (T : BoundaryTripodReferences R F)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (D : FKKReferences A.tensorBar C K) (S : RSKBumping.CellClassification) (bound : Nat) :
    ∃ r, (bound:Int)<ordinaryMu K (xPermutation (2*r)) (yPermutation (2*r)) ∧
      S.sameLeftCell (xPermutation (2*r)) (yPermutation (2*r)) :=
  paper_unbounded_written R A F G T C K D (RSKBumping.cellReferences S) bound

#print axioms paper_canonicality_faithful
#print axioms paper_main_faithful
#print axioms paper_unbounded_faithful
end WebMu.Revised
