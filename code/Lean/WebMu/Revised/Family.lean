import Std

/-!
The shortened family, with A < B < C and one-based boundary positions.
All statements in this file are kernel proofs, without reference axioms.
`permutation` is C positions, B positions, A positions, each in increasing order.
`Dominant` is the nonnegative two-difference prefix walk.
-/
namespace WebMu.Revised.Family

inductive Letter | A | B | C deriving DecidableEq, BEq, Repr
open Letter
abbrev Word := List Letter

def Y : Word := [A,B,A,A,A,C]
def U : Word := [B,B,B,A,A,C,A,C,C]
def V₀ : Word := [B,B,C,B,C,C]
def ABC : Word := [A,B,C]
def wordPower (w : Word) : Nat → Word
  | 0 => []
  | n+1 => w ++ wordPower w n

def N (m : Nat) : Nat := 4 + 3*m
def aWord (m : Nat) : Word := wordPower ABC (N m)
def cWord (m : Nat) : Word := Y ++ wordPower U m ++ V₀

def count (x : Letter) : Word → Nat
  | [] => 0
  | a::w => (if a = x then 1 else 0) + count x w

theorem count_append (x : Letter) (u v : Word) :
    count x (u ++ v) = count x u + count x v := by
  induction u with
  | nil => simp [count]
  | cons a u ih => simp [count, ih, Nat.add_assoc]

theorem count_repeat (x : Letter) (w : Word) (m : Nat) :
    count x (wordPower w m) = m * count x w := by
  induction m with
  | zero => simp [wordPower, count]
  | succ m ih => simp [wordPower, count_append, ih, Nat.add_mul, Nat.add_comm]

theorem length_repeat (w : Word) (m : Nat) :
    (wordPower w m).length = m * w.length := by
  induction m with
  | zero => simp [wordPower]
  | succ m ih => simp [wordPower, ih, Nat.add_mul, Nat.add_comm]

theorem content_a (m : Nat) (x : Letter) : count x (aWord m) = N m := by
  cases x <;> simp [aWord, count_repeat, ABC, count]

theorem content_c (m : Nat) (x : Letter) : count x (cWord m) = N m := by
  cases x <;> simp [cWord, count_append, count_repeat, Y, U, V₀, count, N] <;> omega

theorem length_a (m : Nat) : (aWord m).length = 12+9*m := by
  simp [aWord, length_repeat, ABC, N, Nat.add_mul, Nat.mul_assoc]
  omega

theorem length_c (m : Nat) : (cWord m).length = 12+9*m := by
  simp [cWord, length_repeat, Y, U, V₀, Nat.mul_comm]
  omega

abbrev Chamber := Int × Int

def step (s : Chamber) : Letter → Chamber
  | A => (s.1+1,s.2)
  | B => (s.1-1,s.2+1)
  | C => (s.1,s.2-1)

def run (s : Chamber) : Word → Chamber
  | [] => s
  | x::w => run (step s x) w

def Safe (s : Chamber) : Word → Prop
  | [] => 0 ≤ s.1 ∧ 0 ≤ s.2
  | x::w => (0 ≤ s.1 ∧ 0 ≤ s.2) ∧ Safe (step s x) w

instance safeDecidable (s : Chamber) (w : Word) : Decidable (Safe s w) :=
  match w with
  | [] => inferInstanceAs (Decidable (0 ≤ s.1 ∧ 0 ≤ s.2))
  | x::w => @instDecidableAnd _ _ inferInstance (safeDecidable (step s x) w)

def Dominant (w : Word) : Prop := Safe (0,0) w

theorem safe_append (s : Chamber) (u v : Word) :
    Safe s (u ++ v) ↔ Safe s u ∧ Safe (run s u) v := by
  induction u generalizing s with
  | nil =>
    simp only [List.nil_append, Safe, run]
    constructor
    · intro hv
      have hhead : 0 ≤ s.1 ∧ 0 ≤ s.2 := by
        cases v with
        | nil => exact hv
        | cons x v => exact hv.1
      exact ⟨hhead, hv⟩
    · exact And.right
  | cons x u ih => simp [Safe, run, ih, and_assoc]

theorem run_append (s : Chamber) (u v : Word) :
    run s (u ++ v) = run (run s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons x u ih => exact ih _

theorem repeat_cycle (s : Chamber) (w : Word)
    (hsafe : Safe s w) (hcycle : run s w = s) (m : Nat) :
    Safe s (wordPower w m) ∧ run s (wordPower w m) = s := by
  induction m with
  | zero =>
    constructor
    · cases w with
      | nil => exact hsafe
      | cons x w => exact hsafe.1
    · rfl
  | succ m ih =>
    constructor
    · rw [wordPower, safe_append, hcycle]
      exact ⟨hsafe, ih.1⟩
    · rw [wordPower, run_append, hcycle]
      exact ih.2

theorem dominant_a (m : Nat) : Dominant (aWord m) := by
  exact (repeat_cycle (0,0) ABC (by decide) (by decide) (N m)).1

theorem dominant_c (m : Nat) : Dominant (cWord m) := by
  have hY : Safe (0,0) Y := by decide
  have rY : run (0,0) Y = (3,0) := by decide
  have hU := repeat_cycle (3,0) U (by decide) (by decide) m
  have hV : Safe (3,0) V₀ := by decide
  unfold Dominant cWord
  rw [safe_append, safe_append, run_append, rY, hU.2]
  exact ⟨⟨hY, hU.1⟩, hV⟩

/-- The prefix walk agrees with the differences of the three letter counts. -/
theorem run_counts (s : Chamber) (w : Word) :
    run s w = (s.1 + (count A w : Int) - count B w,
      s.2 + (count B w : Int) - count C w) := by
  induction w generalizing s with
  | nil => simp [run, count]
  | cons x w ih =>
    rw [run, ih]
    cases x <;> apply Prod.ext <;> simp [step, count, Int.natCast_add] <;> omega

/-- Every decomposition into a prefix and suffix satisfies the count inequalities. -/
theorem dominant_prefix_counts (w p q : Word) (hw : Dominant w) (heq : w = p ++ q) :
    count B p ≤ count A p ∧ count C p ≤ count B p := by
  subst w
  have hs := (safe_append (0,0) p q).mp hw
  have hs0 : 0 ≤ (run (0,0) p).1 ∧ 0 ≤ (run (0,0) p).2 := by
    cases q with
    | nil => exact hs.2
    | cons x q => exact hs.2.1
  rw [run_counts] at hs0
  simp only at hs0
  omega

theorem total_counts (w : Word) :
    count A w + count B w + count C w = w.length := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simp [count] <;> omega

theorem take_ABC_A (n k : Nat) :
    count A ((wordPower ABC n).take k) = min n ((k+2)/3) := by
  induction n generalizing k with
  | zero => simp [wordPower, count]
  | succ n ih =>
    cases k with
    | zero => simp [count]
    | succ k =>
      cases k with
      | zero => simp [wordPower, ABC, count]
      | succ k =>
        cases k with
        | zero => simp [wordPower, ABC, count]
        | succ k =>
          have h := ih k
          simp only [ABC] at h
          simp [wordPower, ABC, count]
          omega

theorem take_ABC_C (n k : Nat) :
    count C ((wordPower ABC n).take k) = min n (k/3) := by
  induction n generalizing k with
  | zero => simp [wordPower, count]
  | succ n ih =>
    cases k with
    | zero => simp [count]
    | succ k =>
      cases k with
      | zero => simp [wordPower, ABC, count]
      | succ k =>
        cases k with
        | zero => simp [wordPower, ABC, count]
        | succ k =>
          have h := ih k
          simp only [ABC] at h
          simp [wordPower, ABC, count]
          omega

/-- The extremal prefix inequalities used in the manuscript's Bruhat argument. -/
theorem alternating_prefix_extrema (w : Word) (n k : Nat)
    (hdom : Dominant w) (hcontent : ∀ x, count x w = n) :
    count A ((wordPower ABC n).take k) ≤ count A (w.take k) ∧
    count C (w.take k) ≤ count C ((wordPower ABC n).take k) := by
  have htotal := total_counts w
  simp only [hcontent] at htotal
  by_cases hk : k ≤ w.length
  · have hd := dominant_prefix_counts w (w.take k) (w.drop k)
      hdom (List.take_append_drop k w).symm
    have ht := total_counts (w.take k)
    rw [List.length_take, Nat.min_eq_left hk] at ht
    rw [take_ABC_A, take_ABC_C]
    omega
  · rw [List.take_of_length_le (by omega : w.length ≤ k), hcontent A, hcontent C,
      take_ABC_A, take_ABC_C]
    omega

theorem family_prefix_order (m k : Nat) :
    count A ((aWord m).take k) ≤ count A ((cWord m).take k) ∧
    count C ((cWord m).take k) ≤ count C ((aWord m).take k) :=
  alternating_prefix_extrema (cWord m) (N m) k (dominant_c m) (content_c m)

/-- The three rank-count formulas at thresholds j, N+j, 2N+j. -/
def wordRanks (w : Word) (k j : Nat) : Nat × Nat × Nat :=
  let p := w.take k
  (min (count C p) j,
    min (p.length-count A p) (count C p+j),
    min p.length (p.length-count A p+j))

theorem wordRanks_monotone (u w : Word) (k j : Nat)
    (hlen : u.length = w.length)
    (hA : count A (u.take k) ≤ count A (w.take k))
    (hC : count C (w.take k) ≤ count C (u.take k)) :
    (wordRanks w k j).1 ≤ (wordRanks u k j).1 ∧
    (wordRanks w k j).2.1 ≤ (wordRanks u k j).2.1 ∧
    (wordRanks w k j).2.2 ≤ (wordRanks u k j).2.2 := by
  simp only [wordRanks, List.length_take, hlen]
  omega

theorem family_rank_inequalities (m k j : Nat) :
    (wordRanks (cWord m) k j).1 ≤ (wordRanks (aWord m) k j).1 ∧
    (wordRanks (cWord m) k j).2.1 ≤ (wordRanks (aWord m) k j).2.1 ∧
    (wordRanks (cWord m) k j).2.2 ≤ (wordRanks (aWord m) k j).2.2 := by
  exact wordRanks_monotone _ _ k j (by rw [length_a, length_c])
    (family_prefix_order m k).1 (family_prefix_order m k).2

/-- One-based positions of a letter, in boundary order. -/
def positionsFrom (i : Nat) (x : Letter) : Word → List Nat
  | [] => []
  | a::w => if a = x then i :: positionsFrom (i+1) x w else positionsFrom (i+1) x w

def permutation (w : Word) : List Nat :=
  positionsFrom 1 C w ++ positionsFrom 1 B w ++ positionsFrom 1 A w

def xPermutation (m : Nat) : List Nat := permutation (aWord m)
def yPermutation (m : Nat) : List Nat := permutation (cWord m)

theorem length_positions (i : Nat) (x : Letter) (w : Word) :
    (positionsFrom i x w).length = count x w := by
  induction w generalizing i with
  | nil => rfl
  | cons a w ih =>
    simp only [positionsFrom, count]
    split <;> simp_all [Nat.add_comm]

theorem permutation_lengths (m : Nat) :
    (xPermutation m).length = 12+9*m ∧ (yPermutation m).length = 12+9*m := by
  simp [xPermutation, yPermutation, permutation, length_positions, content_a, content_c, N]
  omega

/-- The same permutation with an arbitrary initial boundary label. -/
def permutationFrom (i : Nat) (w : Word) : List Nat :=
  positionsFrom i C w ++ positionsFrom i B w ++ positionsFrom i A w

theorem permutationFrom_perm_range (i : Nat) (w : Word) :
    (permutationFrom i w).Perm (List.range' i w.length) := by
  induction w generalizing i with
  | nil => simp [permutationFrom, positionsFrom]
  | cons x w ih =>
    rw [List.length_cons, List.range'_succ]
    apply List.Perm.trans (l₂ := i :: permutationFrom (i+1) w)
    · cases x with
      | A => simpa [permutationFrom, positionsFrom] using
          (List.perm_middle (a := i)
            (l₁ := positionsFrom (i+1) C w ++ positionsFrom (i+1) B w)
            (l₂ := positionsFrom (i+1) A w))
      | B => simp [permutationFrom, positionsFrom, List.append_assoc]
      | C => simp [permutationFrom, positionsFrom]
    · exact (ih (i+1)).cons i

theorem permutation_perm_range (w : Word) :
    (permutation w).Perm (List.range' 1 w.length) := permutationFrom_perm_range 1 w

theorem permutation_nodup (w : Word) : (permutation w).Nodup :=
  (permutation_perm_range w).nodup_iff.mpr (List.nodup_range')

theorem positions_lower_bound (i : Nat) (x : Letter) (w : Word) :
    ∀ j ∈ positionsFrom i x w, i ≤ j := by
  induction w generalizing i with
  | nil => simp [positionsFrom]
  | cons a w ih =>
    intro j hj
    simp only [positionsFrom] at hj
    split at hj
    · simp only [List.mem_cons] at hj
      obtain rfl | hj := hj
      · omega
      · have h := ih (i+1) j hj; omega
    · have h := ih (i+1) j hj; omega

def natSmaller (i : Nat) : List Nat → Nat
  | [] => 0
  | j::l => (if j < i then 1 else 0) + natSmaller i l

/-- The ordinary inversion definition of the Coxeter length in S_n. -/
def coxeterLength : List Nat → Nat
  | [] => 0
  | i::l => natSmaller i l + coxeterLength l

theorem natSmaller_append (i : Nat) (l k : List Nat) :
    natSmaller i (l ++ k) = natSmaller i l + natSmaller i k := by
  induction l with
  | nil => simp [natSmaller]
  | cons j l ih => simp [natSmaller, ih, Nat.add_assoc]

theorem natSmaller_above (i : Nat) (l : List Nat) (h : ∀ j ∈ l, i ≤ j) :
    natSmaller i l = 0 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hj := h j (by simp)
    have ht : ∀ j ∈ l, i ≤ j := by intro j hj; exact h j (by simp [hj])
    simp [natSmaller, show ¬ j < i by omega, ih ht]

theorem coxeterLength_insert_min (i : Nat) (l k : List Nat)
    (h : ∀ j ∈ l ++ k, i < j) :
    coxeterLength (l ++ i::k) = l.length + coxeterLength (l ++ k) := by
  induction l with
  | nil =>
    have hk : ∀ j ∈ k, i ≤ j := by intro j hj; have h' := h j hj; omega
    simp [coxeterLength, natSmaller_above i k hk]
  | cons j l ih =>
    have hj : i < j := h j (by simp)
    have ht : ∀ j ∈ l ++ k, i < j := by
      intro j hj
      exact h j (by simp only [List.cons_append, List.mem_cons]; exact Or.inr hj)
    simp only [List.cons_append, coxeterLength, List.length_cons, ih ht,
      natSmaller_append, natSmaller, if_pos hj]
    omega

theorem positions_sorted (i : Nat) (x : Letter) (w : Word) :
    (positionsFrom i x w).Pairwise (fun a b => a < b) := by
  induction w generalizing i with
  | nil => simp [positionsFrom]
  | cons a w ih =>
    simp only [positionsFrom]
    split
    · rw [List.pairwise_cons]
      constructor
      · intro j hj
        have h := positions_lower_bound (i+1) x w j hj
        omega
      · exact ih (i+1)
    · exact ih (i+1)

theorem natSmaller_take (k j : Nat) (l : List Nat)
    (hs : l.Pairwise (fun a b => a < b)) :
    natSmaller k (l.take j) = min j (natSmaller k l) := by
  induction l generalizing j with
  | nil => simp [natSmaller]
  | cons a l ih =>
    obtain ⟨hsHead, hsTail⟩ := List.pairwise_cons.mp hs
    cases j with
    | zero => simp [natSmaller]
    | succ j =>
      by_cases ha : a < k
      · simp only [List.take_succ_cons, natSmaller, if_pos ha, ih j hsTail]
        omega
      · have hz : natSmaller k l = 0 :=
          natSmaller_above k l (by intro b hb; have h := hsHead b hb; omega)
        simp only [List.take_succ_cons, natSmaller, if_neg ha, ih j hsTail, hz]
        omega

theorem natSmaller_positions (i k : Nat) (x : Letter) (w : Word) :
    natSmaller k (positionsFrom i x w) = count x (w.take (k-i)) := by
  induction w generalizing i with
  | nil => simp [positionsFrom, natSmaller, count]
  | cons a w ih =>
    by_cases hi : i < k
    · have hk : k-i = (k-(i+1))+1 := by omega
      simp only [positionsFrom, hk, List.take_succ_cons, count]
      split
      · simp only [natSmaller, if_pos hi, ih]
      · simpa using ih (i+1)
    · have hge : k ≤ i := by omega
      have hz : natSmaller k (positionsFrom i x (a::w)) = 0 :=
        natSmaller_above k _ (by
          intro j hj
          have hh := positions_lower_bound i x (a::w) j hj
          omega)
      rw [hz, Nat.sub_eq_zero_of_le hge]
      rfl

/-- Rank matrix: entries ≤ k among the first j entries of one-line notation. -/
def rankCount (p : List Nat) (j k : Nat) : Nat := natSmaller (k+1) (p.take j)

theorem rankCount_positions (x : Letter) (w : Word) (j k : Nat) :
    rankCount (positionsFrom 1 x w) j k = min j (count x (w.take k)) := by
  unfold rankCount
  rw [natSmaller_take _ _ _ (positions_sorted 1 x w), natSmaller_positions]
  simp

theorem rankCount_permutation (w : Word) (n j k : Nat)
    (hcontent : ∀ x, count x w = n) :
    rankCount (permutation w) j k =
      min j (count C (w.take k)) + min (j-n) (count B (w.take k)) +
      min (j-2*n) (count A (w.take k)) := by
  simp only [rankCount, permutation, List.take_append, natSmaller_append,
    List.length_append, length_positions, hcontent]
  rw [natSmaller_take _ _ _ (positions_sorted 1 C w),
    natSmaller_take _ _ _ (positions_sorted 1 B w),
    natSmaller_take _ _ _ (positions_sorted 1 A w)]
  simp only [natSmaller_positions, Nat.add_sub_cancel]
  congr 3
  omega

theorem count_take_le (x : Letter) (w : Word) (k : Nat) :
    count x (w.take k) ≤ count x w := by
  have hh := count_append x (w.take k) (w.drop k)
  rw [List.take_append_drop] at hh
  omega

/-- The prefix order implies the actual rank matrix inequalities. -/
theorem rankCount_monotone (u w : Word) (n j k : Nat)
    (hu : ∀ x, count x u = n) (hw : ∀ x, count x w = n)
    (hA : count A (u.take k) ≤ count A (w.take k))
    (hC : count C (w.take k) ≤ count C (u.take k)) :
    rankCount (permutation w) j k ≤ rankCount (permutation u) j k := by
  rw [rankCount_permutation w n j k hw, rankCount_permutation u n j k hu]
  have huA := count_take_le A u k
  have huB := count_take_le B u k
  have huC := count_take_le C u k
  have hwA := count_take_le A w k
  have hwB := count_take_le B w k
  have hwC := count_take_le C w k
  have huT := total_counts u
  have hwT := total_counts w
  simp only [hu, hw] at huA huB huC hwA hwB hwC huT hwT
  have hlen : u.length = w.length := by omega
  have hpu := total_counts (u.take k)
  have hpw := total_counts (w.take k)
  simp only [List.length_take, hlen] at hpu hpw
  omega

/-- Bruhat's rank criterion on the concrete one-line permutations. -/
def RankLe (p q : List Nat) : Prop :=
  p.length = q.length ∧ ∀ j k, rankCount q j k ≤ rankCount p j k

theorem family_rank_order (m : Nat) : RankLe (xPermutation m) (yPermutation m) := by
  constructor
  · have h := permutation_lengths m; omega
  · intro j k
    exact rankCount_monotone (aWord m) (cWord m) (N m) j k
      (content_a m) (content_c m) (family_prefix_order m k).1 (family_prefix_order m k).2

def larger (x : Letter) (w : Word) : Nat :=
  match x with
  | A => count B w + count C w
  | B => count C w
  | C => 0

def ascendingPairs : Word → Nat
  | [] => 0
  | x::w => larger x w + ascendingPairs w

theorem permutation_coxeterLength (i : Nat) (w : Word) :
    coxeterLength (permutationFrom i w) = ascendingPairs w := by
  induction w generalizing i with
  | nil => rfl
  | cons x w ih =>
    have hpos : ∀ (l : Letter) (j : Nat), j ∈ positionsFrom (i+1) l w → i < j := by
      intro l j hj
      have hh := positions_lower_bound (i+1) l w j hj
      omega
    have hABC : ∀ j ∈ permutationFrom (i+1) w, i < j := by
      intro j hj
      simp only [permutationFrom, List.mem_append] at hj
      obtain (hj | hj) | hj := hj
      · exact hpos C j hj
      · exact hpos B j hj
      · exact hpos A j hj
    cases x with
    | A =>
      have hh := coxeterLength_insert_min i
        (positionsFrom (i+1) C w ++ positionsFrom (i+1) B w)
        (positionsFrom (i+1) A w) hABC
      simpa [permutationFrom, positionsFrom, ascendingPairs, larger,
        length_positions, Nat.add_comm] using hh.trans
          (congrArg (fun n => (positionsFrom (i+1) C w ++
            positionsFrom (i+1) B w).length + n) (ih (i+1)))
    | B =>
      have hh := coxeterLength_insert_min i (positionsFrom (i+1) C w)
        (positionsFrom (i+1) B w ++ positionsFrom (i+1) A w)
        (by simpa [permutationFrom, List.append_assoc] using hABC)
      have hi := ih (i+1)
      simp only [permutationFrom, List.append_assoc] at hi
      rw [hi] at hh
      simpa [permutationFrom, positionsFrom, ascendingPairs, larger,
        List.append_assoc, length_positions] using hh
    | C =>
      have hz : natSmaller i (permutationFrom (i+1) w) = 0 :=
        natSmaller_above i _ (by intro j hj; have h := hABC j hj; omega)
      simpa [permutationFrom, positionsFrom, ascendingPairs, larger, coxeterLength]
        using show natSmaller i (permutationFrom (i+1) w) +
          coxeterLength (permutationFrom (i+1) w) = ascendingPairs w by rw [hz, ih]; omega

/-- Descending unequal-letter pairs in boundary order. -/
def smaller (x : Letter) (w : Word) : Nat :=
  match x with
  | A => 0
  | B => count A w
  | C => count A w + count B w

def inversions : Word → Nat
  | [] => 0
  | x::w => smaller x w + inversions w

def cross (u v : Word) : Nat :=
  count B u * count A v + count C u * (count A v + count B v)

theorem inversions_append (u v : Word) :
    inversions (u ++ v) = inversions u + inversions v + cross u v := by
  induction u with
  | nil => simp [inversions, cross, count]
  | cons x u ih =>
    cases x <;>
      simp [inversions, smaller, cross, count, count_append, ih,
        Nat.add_mul, Nat.mul_add] <;> omega

theorem seed_inversions : inversions Y = 3 ∧ inversions U = 10 ∧ inversions V₀ = 1 := by decide

theorem cross_values : cross Y U = 9 ∧ cross Y V₀ = 3 ∧ cross U U = 27 ∧ cross U V₀ = 9 := by decide

theorem inv_U_succ (m : Nat) :
    inversions (wordPower U (m+1)) = inversions (wordPower U m) + 27*m + 10 := by
  simp [wordPower, count_repeat, U, inversions, smaller, count, Nat.mul_comm]
  omega

theorem inv_ABC_succ (m : Nat) :
    inversions (wordPower ABC (m+1)) = inversions (wordPower ABC m) + 3*m := by
  simp [wordPower, count_repeat, ABC, inversions, smaller, count]
  omega

theorem inv_U_doubled (m : Nat) :
    2 * inversions (wordPower U m) + 7*m = 27*m*m := by
  induction m with
  | zero => simp [wordPower, inversions]
  | succ m ih =>
    rw [inv_U_succ]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega

theorem inv_ABC_doubled (n : Nat) :
    2 * inversions (wordPower ABC n) + 3*n = 3*n*n := by
  induction n with
  | zero => simp [wordPower, inversions]
  | succ n ih =>
    rw [inv_ABC_succ]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega

theorem inv_c_formula (m : Nat) :
    inversions (cWord m) = inversions (wordPower U m) + 18*m + 7 := by
  simp [cWord, inversions_append, cross, count_append, count_repeat,
    Y, U, V₀, inversions, smaller, count]
  omega

theorem inv_c_doubled (m : Nat) :
    2 * inversions (cWord m) = 27*m*m + 29*m + 14 := by
  rw [inv_c_formula]
  have h := inv_U_doubled m
  omega

theorem inv_a_doubled (m : Nat) :
    2 * inversions (aWord m) + 3*N m = 3*N m*N m :=
  inv_ABC_doubled (N m)

theorem ascending_inversions (w : Word) :
    ascendingPairs w + inversions w =
      count A w * count B w + count A w * count C w + count B w * count C w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases x <;> simp [ascendingPairs, inversions, larger, smaller, count,
      Nat.add_mul, Nat.mul_add] <;> omega

/-- The length statistic for words of equal content. -/
def lengthStatistic (w : Word) (n : Nat) : Nat := 3*n*n - inversions w

theorem coxeterLength_statistic (w : Word) (n : Nat)
    (hcontent : ∀ x, count x w = n) :
    coxeterLength (permutation w) = lengthStatistic w n := by
  have h := ascending_inversions w
  have hp := permutation_coxeterLength 1 w
  change coxeterLength (permutation w) = ascendingPairs w at hp
  simp only [hcontent] at h
  unfold lengthStatistic
  rw [hp]
  simp only [Nat.mul_assoc]
  omega

theorem length_a_doubled (m : Nat) :
    2 * lengthStatistic (aWord m) (N m) = 3*N m*(N m+1) := by
  have h := inv_a_doubled m
  unfold lengthStatistic
  simp only [Nat.mul_add, Nat.mul_one]
  omega

theorem length_y_doubled (m : Nat) :
    2 * lengthStatistic (cWord m) (N m) = 27*m*m + 115*m + 82 := by
  have h := inv_c_doubled m
  unfold lengthStatistic N
  simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] at *
  simp only [← Nat.mul_assoc] at *
  omega

theorem length_gap (m : Nat) :
    lengthStatistic (cWord m) (N m) = lengthStatistic (aWord m) (N m) + 17*m + 11 := by
  have hx := length_a_doubled m
  have hy := length_y_doubled m
  simp only [N, Nat.mul_add, Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] at *
  simp only [← Nat.mul_assoc] at *
  omega

theorem coxeter_length_gap (m : Nat) :
    coxeterLength (yPermutation m) = coxeterLength (xPermutation m) + 17*m + 11 := by
  unfold xPermutation yPermutation
  rw [coxeterLength_statistic _ (N m) (content_c m),
    coxeterLength_statistic _ (N m) (content_a m)]
  exact length_gap m

theorem family_strict_rank_order (m : Nat) :
    RankLe (xPermutation m) (yPermutation m) ∧ xPermutation m ≠ yPermutation m := by
  constructor
  · exact family_rank_order m
  · intro heq
    have hgap := coxeter_length_gap m
    rw [heq] at hgap
    omega

theorem coxeter_lengths (m : Nat) :
    coxeterLength (xPermutation m) = (3*N m*(N m+1))/2 ∧
    coxeterLength (yPermutation m) = (27*m*m+115*m+82)/2 := by
  have hx := length_a_doubled m
  have hy := length_y_doubled m
  unfold xPermutation yPermutation
  rw [coxeterLength_statistic _ (N m) (content_a m),
    coxeterLength_statistic _ (N m) (content_c m)]
  omega

theorem even_parameter_gap (r : Nat) :
    lengthStatistic (cWord (2*r)) (N (2*r)) =
      lengthStatistic (aWord (2*r)) (N (2*r)) + 34*r + 11 := by
  have h := length_gap (2*r)
  omega

theorem even_parameter_degree (r : Nat) : (34*r+11-1)/2 = 17*r+5 := by omega

theorem size_even_parameter (r : Nat) :
    (xPermutation (2*r)).length = 12+18*r ∧ (yPermutation (2*r)).length = 12+18*r := by
  have h := permutation_lengths (2*r)
  omega

example : permutation ABC = [3,2,1] := by decide
example : permutation (ABC ++ ABC) = [3,6,2,5,1,4] := by decide
example : coxeterLength (xPermutation 0) = 30 := by decide
example : coxeterLength (yPermutation 0) = 41 := by decide
example : coxeterLength (xPermutation 1) = 84 := by decide
example : coxeterLength (yPermutation 1) = 112 := by decide
example : coxeterLength (xPermutation 2) = 165 := by decide
example : coxeterLength (yPermutation 2) = 210 := by decide
example : cWord 0 = [A,B,A,A,A,C,B,B,C,B,C,C] := by decide

def letterCode : Letter → Nat
  | A => 0
  | B => 1
  | C => 2

def encodeLetters (w : Word) : List Nat := w.map letterCode

theorem wordPower_add (w : Word) (n m : Nat) :
    wordPower w (n+m) = wordPower w n ++ wordPower w m := by
  induction n with
  | zero => simp [wordPower]
  | succ n ih =>
    rw [show n+1+m = (n+m)+1 by omega, wordPower, ih]
    simp [wordPower, List.append_assoc]

theorem wordPower_mul (w : Word) (n m : Nat) :
    wordPower w (n*m) = wordPower (wordPower w n) m := by
  induction m with
  | zero => simp [wordPower]
  | succ m ih =>
    rw [show n*(m+1) = n+n*m by simp [Nat.mul_add, Nat.add_comm], wordPower_add, ih]
    rfl

theorem map_wordPower (w : Word) (m : Nat) :
    encodeLetters (wordPower w m) = (List.replicate m (encodeLetters w)).flatten := by
  induction m with
  | zero => simp [wordPower, encodeLetters]
  | succ m ih =>
    simp only [wordPower, encodeLetters, List.map_append, List.replicate_succ,
      List.flatten_cons]
    exact congrArg (fun l => w.map letterCode ++ l) ih

theorem aWord_blocks (m : Nat) :
    aWord m = wordPower ABC 2 ++ wordPower (wordPower ABC 3) m ++ wordPower ABC 2 := by
  unfold aWord N
  rw [show 4+3*m = (2+3*m)+2 by omega, wordPower_add, wordPower_add, wordPower_mul]

theorem encoded_a (m : Nat) :
    encodeLetters (aWord m) = [0,1,2,0,1,2] ++
      (List.replicate m [0,1,2,0,1,2,0,1,2]).flatten ++ [0,1,2,0,1,2] := by
  rw [aWord_blocks]
  simp only [encodeLetters, List.map_append]
  change encodeLetters (wordPower ABC 2) ++
    encodeLetters (wordPower (wordPower ABC 3) m) ++
    encodeLetters (wordPower ABC 2) = _
  rw [map_wordPower (wordPower ABC 3) m]
  rfl

theorem encoded_c (m : Nat) :
    encodeLetters (cWord m) = [0,1,0,0,0,2] ++
      (List.replicate m [1,1,1,0,0,2,0,2,2]).flatten ++ [1,1,2,1,2,2] := by
  unfold cWord
  simp only [encodeLetters, List.map_append]
  change encodeLetters Y ++ encodeLetters (wordPower U m) ++ encodeLetters V₀ = _
  rw [map_wordPower]
  rfl

#print axioms dominant_c
#print axioms coxeter_length_gap
#print axioms family_strict_rank_order
end WebMu.Revised.Family
