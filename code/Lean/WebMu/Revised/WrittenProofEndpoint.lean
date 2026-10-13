import WebMu.Revised.WrittenProofLocal

/-! Fully discharged endpoints for the written local proof. All local
properties are constructed from proved path, degree, diagram, and row
lemmas. Only the uniform prior-work interfaces remain arguments. -/
namespace WebMu.Revised
open Bar AtlasRealization CapDiagram Family

theorem paper_canonicality_written (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (T : BoundaryTripodReferences R F)
    (C : CanonicalReferences A.tensorBar) (m : Nat) :
    tensorOriginal m=C.canonical m (leadingBoundary m) :=
  WrittenProof.canonicality (WrittenProof.localProperties R A F G T) R A C m

theorem paper_main_written (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (T : BoundaryTripodReferences R F)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (D : FKKReferences A.tensorBar C K) (S : CellReferences)
    (B : Bruhat.References) (r : Nat) : SubwordFamilyConclusion K S r :=
  WrittenProof.main (WrittenProof.localProperties R A F G T) R A C K D S B r

theorem paper_unbounded_written (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (T : BoundaryTripodReferences R F)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (D : FKKReferences A.tensorBar C K) (S : CellReferences) (bound : Nat) :
    ∃ r, (bound:Int)<ordinaryMu K (xPermutation (2*r)) (yPermutation (2*r)) ∧
      S.sameLeftCell (xPermutation (2*r)) (yPermutation (2*r)) :=
  WrittenProof.unbounded (WrittenProof.localProperties R A F G T) R A C K D S bound

#print axioms paper_canonicality_written
#print axioms paper_main_written
#print axioms paper_unbounded_written
end WebMu.Revised
