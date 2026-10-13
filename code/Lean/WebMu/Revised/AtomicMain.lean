import WebMu.Revised.CircuitRealization
import WebMu.Revised.BruhatBridge

/-! Main endpoints with no unproved executable-coordinate realization input.
The old `CoordinateReferences` is constructed by the proved interpreter theorem
from atomic standard-basis and elementary-web inputs. Bruhat order is the
manuscript's concrete reduced-subword order. -/
namespace WebMu.Revised
open Family

theorem paper_canonicality_atomic (R : Bar.BarReferences) (A : Bar.AtomicCoordinates R)
    (C : CanonicalReferences A.tensorBar) (m : Nat) :
    tensorOriginal m = C.canonical m (leadingBoundary m) :=
  paper_canonicality R A.toCoordinateReferences C m

theorem paper_main_atomic (R : Bar.BarReferences) (A : Bar.AtomicCoordinates R)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (F : FKKReferences A.tensorBar C K) (S : CellReferences)
    (B : Bruhat.References) (r : Nat) : SubwordFamilyConclusion K S r :=
  paper_main_subword R A.toCoordinateReferences C K F S B r

theorem paper_unbounded_atomic (R : Bar.BarReferences) (A : Bar.AtomicCoordinates R)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (F : FKKReferences A.tensorBar C K) (S : CellReferences) (bound : Nat) :
    ∃ r, (bound:Int) < ordinaryMu K (xPermutation (2*r)) (yPermutation (2*r)) ∧
      S.sameLeftCell (xPermutation (2*r)) (yPermutation (2*r)) :=
  paper_unbounded R A.toCoordinateReferences C K F S bound

#print axioms paper_canonicality_atomic
#print axioms paper_main_atomic
#print axioms paper_unbounded_atomic

end WebMu.Revised
