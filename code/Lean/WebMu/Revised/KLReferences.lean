import WebMu.Revised.Family
import WebMu.Revised.KLTop
import WebMu.Revised.Parameter

/-! An explicit prior-work interface. These are hypotheses, not proved theorems.
The statements are uniform in the words/permutations, never in this paper's family.

* `ordinary_support`: the diagonal/strict-length support and ordinary degree bound.
* `alternating`: Deodhar's alternating parabolic formula, with the identity removed.
* `nonidentity`: the remaining terms have h ≠ 1, hence positive Coxeter length.
* `length_additive`: the standard minimal-right-coset length property.

A term records (xh, ℓ(h)). The supplied polynomial functions are the actual
ordinary/parabolic KL polynomials; the interface does not define them by this
paper's answer. -/
namespace WebMu.Revised
open Laurent Algebra
open Family

abbrev PermutationWord := List Nat

def Balanced (w : Family.Word) (n : Nat) : Prop := ∀ a, Family.count a w = n

structure KLReferences where
  ordinary : PermutationWord → PermutationWord → Laurent
  parabolic : Nat → PermutationWord → PermutationWord → Laurent
  terms : Nat → PermutationWord → PermutationWord → List (PermutationWord × Nat)
  ordinary_support : ∀ x y k, coeff (ordinary x y) (k:Int) ≠ 0 →
    (x = y ∧ k = 0) ∨ (x ≠ y ∧ 2*k + coxeterLength x + 1 ≤ coxeterLength y)
  nonidentity : ∀ n u w, Balanced u n → Balanced w n →
    ∀ h ∈ terms n (permutation u) (permutation w), 0 < h.2
  length_additive : ∀ n u w, Balanced u n → Balanced w n →
    ∀ h ∈ terms n (permutation u) (permutation w),
      coxeterLength h.1 = coxeterLength (permutation u) + h.2
  alternating : ∀ n u w, Balanced u n → Balanced w n →
    Family.RankLe (permutation u) (permutation w) → ∀ k : Nat,
    coeff (parabolic n (permutation u) (permutation w)) (k:Int) =
      coeff (ordinary (permutation u) (permutation w)) (k:Int) +
      KLTop.alternatingRest (terms n (permutation u) (permutation w)) Prod.snd
        (fun h d => coeff (ordinary h.1 (permutation w)) (d:Int)) k

/-- The manuscript's critical coefficient, zero unless x < y and the
length gap is odd. On permutations the uniform rank criterion identifies
the displayed rank-order guard with the ordinary strict Bruhat order. -/
noncomputable def ordinaryMu (R : KLReferences) (x y : PermutationWord) : Int := by
  classical
  let delta := coxeterLength y - coxeterLength x
  exact if RankLe x y ∧ x ≠ y ∧ delta % 2 = 1 then
    coeff (R.ordinary x y) (((delta-1)/2 : Nat):Int) else 0

theorem ordinaryMu_zero_outside_strict_order (R : KLReferences)
    (x y : PermutationWord) (h : ¬ (RankLe x y ∧ x ≠ y)) :
    ordinaryMu R x y = 0 := by
  classical
  simp only [ordinaryMu]
  split
  · next hp => exact False.elim (h ⟨hp.1,hp.2.1⟩)
  · rfl

/-- The manuscript's top-degree deduction from the explicitly supplied prior work. -/
theorem ordinary_parabolic_top (R : KLReferences) (r : Nat) :
    coeff (R.parabolic (N (2*r)) (xPermutation (2*r)) (yPermutation (2*r)))
      ((17*r+5 : Nat):Int) = ordinaryMu R (xPermutation (2*r)) (yPermutation (2*r)) := by
  have hx := content_a (2*r)
  have hy := content_c (2*r)
  have hg := coxeter_length_gap (2*r)
  have hd : coxeterLength (yPermutation (2*r)) - coxeterLength (xPermutation (2*r)) =
      34*r+11 := by omega
  have hs : ∀ h ∈ R.terms (N (2*r)) (xPermutation (2*r)) (yPermutation (2*r)),
      KLTop.OrdinarySupport (34*r+11) h.2
        (fun d => coeff (R.ordinary h.1 (yPermutation (2*r))) (d:Int)) := by
    intro h hh k hk
    have hl := R.length_additive (N (2*r)) (aWord (2*r)) (cWord (2*r)) hx hy h hh
    obtain he | hn := R.ordinary_support h.1 (yPermutation (2*r)) k hk
    · left
      have hlen := congrArg coxeterLength he.1
      change coxeterLength h.1 = coxeterLength (xPermutation (2*r)) + h.2 at hl
      omega
    · right
      change coxeterLength h.1 = coxeterLength (xPermutation (2*r)) + h.2 at hl
      omega
  have htop := KLTop.family_top_transfer r
    (R.terms (N (2*r)) (xPermutation (2*r)) (yPermutation (2*r))) Prod.snd
    (fun h d => coeff (R.ordinary h.1 (yPermutation (2*r))) (d:Int))
    (fun d => coeff (R.ordinary (xPermutation (2*r)) (yPermutation (2*r))) (d:Int))
    (fun d => coeff (R.parabolic (N (2*r)) (xPermutation (2*r)) (yPermutation (2*r))) (d:Int))
    (R.nonidentity (N (2*r)) (aWord (2*r)) (cWord (2*r)) hx hy) hs
    (R.alternating (N (2*r)) (aWord (2*r)) (cWord (2*r)) hx hy
      (family_rank_order (2*r)) (17*r+5))
  unfold ordinaryMu
  rw [hd]
  have hmod : (34*r+11)%2 = 1 := by omega
  have hdiv : (34*r+11-1)/2 = 17*r+5 := by omega
  rw [if_pos ⟨family_rank_order (2*r), (family_strict_rank_order (2*r)).2, hmod⟩, hdiv]
  exact htop

end WebMu.Revised
