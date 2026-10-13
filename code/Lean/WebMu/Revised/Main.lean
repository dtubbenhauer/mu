import WebMu.Revised.OriginalBar
import WebMu.Revised.Conclusion

/-! Main conditional endpoint. In addition to published theory,
`CoordinateReferences` currently assumes realization of the custom whole-circuit
evaluator. The bridge from atomic coordinate laws has not been proved.
The exact coefficient construction, gauge cancellation, full lattice induction,
closed rows, parameter substitution and top transfer are proved; this endpoint
alone is not a complete reference-only verification of the manuscript.
See SEMANTIC_REAUDIT.txt for the source-to-paper audit. -/
namespace WebMu.Revised
open Algebra Family

/-- Canonicality of the original shortened tensor for every number of blocks. -/
theorem paper_canonicality (R : Bar.BarReferences) (E : Bar.CoordinateReferences R)
    (C : CanonicalReferences E.tensorBar) (m : Nat) :
    tensorOriginal m = C.canonical m (leadingBoundary m) :=
  canonical_from_original_bar E.tensorBar C m (Bar.tensorOriginal_fixed R E m)

/-- The manuscript's complete main theorem, including actual permutations,
strict order, length gap, ordinary μ, common left cell and rectangular Q. -/
theorem paper_main (R : Bar.BarReferences) (E : Bar.CoordinateReferences R)
    (C : CanonicalReferences E.tensorBar) (K : KLReferences)
    (F : FKKReferences E.tensorBar C K) (S : CellReferences) (r : Nat) :
    FamilyConclusion K S r :=
  conclusion_from_original_bar E.tensorBar C K F S r (Bar.tensorOriginal_fixed R E (2*r))

/-- The coefficient formula is unbounded, even within a common left cell. -/
theorem paper_unbounded (R : Bar.BarReferences) (E : Bar.CoordinateReferences R)
    (C : CanonicalReferences E.tensorBar) (K : KLReferences)
    (F : FKKReferences E.tensorBar C K) (S : CellReferences) (bound : Nat) :
    ∃ r, (bound:Int) < ordinaryMu K (xPermutation (2*r)) (yPermutation (2*r)) ∧
      S.sameLeftCell (xPermutation (2*r)) (yPermutation (2*r)) := by
  refine ⟨bound,?_,(paper_main R E C K F S bound).common_left_cell⟩
  rw [(paper_main R E C K F S bound).mu_value]
  exact powers_two_grow bound

#print axioms paper_canonicality
#print axioms paper_main
#print axioms paper_unbounded

end WebMu.Revised
