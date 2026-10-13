import WebMu.Revised.Main

/-!
The rank comparison in `paper_main` is now linked to the manuscript's literal
reduced-subword definition of Bruhat order. The only added prior-work input is
the ordinary symmetric-group rank criterion, uniformly in all permutations:
Björner--Brenti, *Combinatorics of Coxeter Groups*, Theorem 2.1.5 together with
Theorem 2.2.2 / Corollary 2.2.3 (pp. 32--34). The source uses counts >= k;
the conversion from this paper's counts <= k is proved below.

Simple generators have the manuscript's one-based indices: s_i swaps i,i+1
for 1 <= i < n. Products act by usual function composition; no inverse or
change of permutation convention is introduced. Reduced means genuinely
shortest among expressions in those generators, not a new name for a rank
predicate or an assumed length formula.
-/
namespace WebMu.Revised.Bruhat
open Family

def simpleReflection (i a : Nat) : Nat :=
  if a = i then i+1 else if a = i+1 then i else a

theorem simpleReflection_left (i : Nat) : simpleReflection i i = i+1 := by
  simp [simpleReflection]

theorem simpleReflection_right (i : Nat) : simpleReflection i (i+1) = i := by
  simp [simpleReflection]

theorem simpleReflection_fixed (i a : Nat) (ha : a ≠ i) (hb : a ≠ i+1) :
    simpleReflection i a = a := by simp [simpleReflection,ha,hb]

theorem simpleReflection_involutive (i a : Nat) :
    simpleReflection i (simpleReflection i a) = a := by
  by_cases ha : a = i
  · subst a; simp [simpleReflection]
  · by_cases hb : a = i+1
    · subst a; simp [simpleReflection]
    · simp [simpleReflection,ha,hb]

def ValidExpression (n : Nat) (w : List Nat) : Prop :=
  ∀ i ∈ w, 1 ≤ i ∧ i < n

/-- `[i₁,...,iₖ]` evaluates as s_i₁ ∘ ... ∘ s_iₖ. -/
def product : List Nat → Nat → Nat
  | [], a => a
  | i::w, a => simpleReflection i (product w a)

def evaluate (n : Nat) (w : List Nat) : List Nat :=
  (List.range' 1 n).map (product w)

theorem product_append (u v : List Nat) (a : Nat) :
    product (u++v) a = product u (product v a) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, product, ih]

/-- These examples fix the order of multiplication independently of the ranks. -/
theorem generators_in_S3 : evaluate 3 [1] = [2,1,3] ∧
    evaluate 3 [2] = [1,3,2] ∧ evaluate 3 [1,2] = [2,3,1] := by decide

def ReducedExpression (n : Nat) (p w : List Nat) : Prop :=
  ValidExpression n w ∧ evaluate n w = p ∧
    ∀ u, ValidExpression n u → evaluate n u = p → w.length ≤ u.length

/-- Some reduced expression of p occurs as a subword of one of q. -/
def SubwordLe (n : Nat) (p q : List Nat) : Prop :=
  ∃ u v, ReducedExpression n p u ∧ ReducedExpression n q v ∧ u.Sublist v

def SubwordLt (n : Nat) (p q : List Nat) : Prop := SubwordLe n p q ∧ p ≠ q

def atLeast (k : Nat) : List Nat → Nat
  | [] => 0
  | a::w => (if k ≤ a then 1 else 0) + atLeast k w

def dotRank (p : List Nat) (j k : Nat) : Nat := atLeast k (p.take j)

theorem complementary_counts (w : List Nat) (k : Nat) :
    natSmaller k w + atLeast k w = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [natSmaller,atLeast,List.length_cons]
    by_cases h : a < k
    · simp only [if_pos h,if_neg (show ¬ k ≤ a by omega)]; omega
    · simp only [if_neg h,if_pos (show k ≤ a by omega)]; omega

theorem atLeast_zero (w : List Nat) : atLeast 0 w = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [atLeast,ih,Nat.add_comm]

theorem rankLe_iff_dotRank (p q : List Nat) (hlen : p.length = q.length) :
    RankLe p q ↔ ∀ j k, dotRank p j k ≤ dotRank q j k := by
  constructor
  · intro h j k
    cases k with
    | zero => simp [dotRank,atLeast_zero,List.length_take,hlen]
    | succ k =>
      have hr := h.2 j k
      have hp := complementary_counts (p.take j) (k+1)
      have hq := complementary_counts (q.take j) (k+1)
      have hl : (p.take j).length = (q.take j).length := by simp [hlen]
      change natSmaller (k+1) (q.take j) ≤ natSmaller (k+1) (p.take j) at hr
      unfold dotRank
      omega
  · intro h
    refine ⟨hlen,?_⟩
    intro j k
    have hr := h j (k+1)
    have hp := complementary_counts (p.take j) (k+1)
    have hq := complementary_counts (q.take j) (k+1)
    have hl : (p.take j).length = (q.take j).length := by simp [hlen]
    unfold dotRank at hr
    unfold rankCount
    omega

/-- A uniform cited theorem, with no reference to this paper's words or family.
The ranks are extended to all natural thresholds; outside [1,n] the comparisons
are automatic. This is the usual dot criterion and subword property. -/
structure References : Prop where
  dotCriterion : ∀ n p q,
    p.Perm (List.range' 1 n) → q.Perm (List.range' 1 n) →
    ((∀ j k, dotRank p j k ≤ dotRank q j k) ↔ SubwordLe n p q)

theorem subword_of_rank (B : References) (n : Nat) (p q : List Nat)
    (hp : p.Perm (List.range' 1 n)) (hq : q.Perm (List.range' 1 n))
    (h : RankLe p q) : SubwordLe n p q :=
  (B.dotCriterion n p q hp hq).mp ((rankLe_iff_dotRank p q h.1).mp h)

end WebMu.Revised.Bruhat

namespace WebMu.Revised
open Family

/-- The earlier conclusion, strengthened to the paper's subword definition. -/
structure SubwordFamilyConclusion (K : KLReferences) (S : CellReferences) (r : Nat) : Prop
    extends FamilyConclusion K S r where
  strict_bruhat : Bruhat.SubwordLt (12+18*r) (xPermutation (2*r)) (yPermutation (2*r))

theorem paper_main_subword (R : Bar.BarReferences) (E : Bar.CoordinateReferences R)
    (C : CanonicalReferences E.tensorBar) (K : KLReferences)
    (F : FKKReferences E.tensorBar C K) (S : CellReferences)
    (B : Bruhat.References) (r : Nat) : SubwordFamilyConclusion K S r := by
  have h := paper_main R E C K F S r
  exact ⟨h, Bruhat.subword_of_rank B _ _ _ h.x_permutation h.y_permutation
    h.strict_bruhat_rank.1, h.strict_bruhat_rank.2⟩

#print axioms paper_main_subword
#print axioms Bruhat.rankLe_iff_dotRank
#print axioms Bruhat.simpleReflection_involutive

end WebMu.Revised
