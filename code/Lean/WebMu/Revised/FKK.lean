import WebMu.Revised.Canonical
import WebMu.Revised.Labels
import WebMu.Revised.KLReferences

/-! FKK Theorem 2.5', with (1.4), (1.6), (2.16), (2.17), supplies the
following uniform dictionary. Here z=-v, q=v², and the coset representative
reads C positions, then B positions, then A positions. A tensor coordinate
is unchanged by the explicit parenthesization of its ordered outputs. -/
namespace WebMu.Revised
open Algebra Laurent Family

structure FKKReferences (bar : TensorBar) (C : CanonicalReferences bar) (K : KLReferences) : Prop where
  dictionary : ∀ m (a c : Boundary m) n,
    Balanced a.familyWord n → Balanced c.familyWord n →
    Dominant c.familyWord →
    RankLe (permutation a.familyWord) (permutation c.familyWord) →
    C.canonical m c a = ofList (substituteKL
      ((coxeterLength (permutation c.familyWord) : Int) -
       (coxeterLength (permutation a.familyWord) : Int))
      (K.parabolic n (permutation a.familyWord) (permutation c.familyWord)))

/-- The exact ordinary μ-value follows from prior canonical/FKK/KL inputs and
bar invariance of the original tensor. Integrality, leading state, exponent
alignment, ordinary/parabolic top transfer, and the readout are proved here. -/
theorem mu_from_original_bar (bar : TensorBar) (C : CanonicalReferences bar)
    (K : KLReferences) (F : FKKReferences bar C K) (r : Nat)
    (hbar : bar (2*r) (tensorOriginal (2*r)) = tensorOriginal (2*r)) :
    ordinaryMu K (xPermutation (2*r)) (yPermutation (2*r)) = (2:Int)^r := by
  have hcan := canonical_from_original_bar bar C (2*r) hbar
  have hdict := F.dictionary (2*r) (sourceBoundary (2*r)) (leadingBoundary (2*r))
    (N (2*r)) (by simpa [Balanced] using content_a (2*r))
    (by simpa [Balanced] using content_c (2*r))
    (by simpa using dominant_c (2*r)) (by simpa using family_rank_order (2*r))
  have hvalue := tensorOriginal_source_even r
  rw [hcan] at hvalue
  rw [hdict] at hvalue
  simp only [source_familyWord,leading_familyWord] at hvalue
  have hg := coxeter_length_gap (2*r)
  have hd : (coxeterLength (yPermutation (2*r)) : Int) -
      (coxeterLength (xPermutation (2*r)) : Int) = 2*((17*r+5 : Nat):Int)+1 := by
    omega
  change coeff (substituteKL
    ((coxeterLength (yPermutation (2*r)) : Int) - (coxeterLength (xPermutation (2*r)) : Int))
    (K.parabolic (N (2*r)) (xPermutation (2*r)) (yPermutation (2*r)))) (-1) = _ at hvalue
  rw [substituteKL_coefficient _ _ _ hd] at hvalue
  rw [← ordinary_parabolic_top K r]
  exact hvalue

end WebMu.Revised
