import WebMu.Revised.FKK
import WebMu.Revised.Tableaux

namespace WebMu.Revised
open Algebra Family Tableaux

/-- The cell-theoretic references are uniform in all permutations/tableaux. -/
structure CellReferences where
  insertion : List Nat → List (List Nat)
  recording : List Nat → List (List Nat)
  sameLeftCell : List Nat → List Nat → Prop
  rowReading : RowReadingTheorems insertion recording
  leftCellCriterion : ∀ p q n,
    p.Perm (List.range' 1 n) → q.Perm (List.range' 1 n) →
    recording p = recording q → sameLeftCell p q

structure FamilyConclusion (K : KLReferences) (S : CellReferences) (r : Nat) : Prop where
  x_permutation : (xPermutation (2*r)).Perm (List.range' 1 (12+18*r))
  y_permutation : (yPermutation (2*r)).Perm (List.range' 1 (12+18*r))
  strict_bruhat_rank : RankLe (xPermutation (2*r)) (yPermutation (2*r)) ∧
    xPermutation (2*r) ≠ yPermutation (2*r)
  length_gap : coxeterLength (yPermutation (2*r)) =
    coxeterLength (xPermutation (2*r)) + 34*r+11
  mu_value : ordinaryMu K (xPermutation (2*r)) (yPermutation (2*r)) = (2:Int)^r
  common_left_cell : S.sameLeftCell (xPermutation (2*r)) (yPermutation (2*r))
  x_recording : S.recording (xPermutation (2*r)) = rectangularRecording (4+6*r)
  y_recording : S.recording (yPermutation (2*r)) = rectangularRecording (4+6*r)

theorem conclusion_from_original_bar (bar : TensorBar) (C : CanonicalReferences bar)
    (K : KLReferences) (F : FKKReferences bar C K) (S : CellReferences) (r : Nat)
    (hbar : bar (2*r) (tensorOriginal (2*r)) = tensorOriginal (2*r)) :
    FamilyConclusion K S r := by
  have hgap := coxeter_length_gap (2*r)
  have hr := family_RSK S.insertion S.recording S.rowReading (2*r)
  refine ⟨?_,?_,family_strict_rank_order (2*r),by omega,
    mu_from_original_bar bar C K F r hbar,
    family_common_left_cell S.insertion S.recording S.sameLeftCell
      S.rowReading S.leftCellCriterion (2*r), ?_,?_⟩
  · simpa [length_a,← Nat.mul_assoc] using permutation_perm_range (aWord (2*r))
  · simpa [length_c,← Nat.mul_assoc] using permutation_perm_range (cWord (2*r))
  · simpa [N,← Nat.mul_assoc] using hr.2.2.1
  · simpa [N,← Nat.mul_assoc] using hr.2.2.2

theorem powers_two_grow (r : Nat) : (r:Int) < (2:Int)^r := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Int.pow_succ]
    have hr : (0:Int) ≤ r := Int.natCast_nonneg r
    push_cast
    omega

end WebMu.Revised
