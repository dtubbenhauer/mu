import WebMu.Revised.Family

/-!
Concrete standard tableaux for the shortened family. Reference input:
Gillespie–Hocevar–Kulshrestha–Upadhyay, *Iterating the RSK Bijection* (2021),
https://arxiv.org/pdf/2103.04707, Theorem 2.11 and Lemma 3.3.
Definition 2.7 reads French rows top to bottom, hence C,B,A here.
`RowReadingTheorems` is their general statement specialized to every three-row
rectangle, not an assumption about this paper's chosen words.
-/
namespace WebMu.Revised.Tableaux
open Family Family.Letter

def ColumnsLT : List Nat → List Nat → Prop
  | [], [] => True
  | x::a, y::b => x < y ∧ ColumnsLT a b
  | _, _ => False

/-- Strict column inequalities from sorted, disjoint rows and prefix counts. -/
theorem columns_of_prefix_counts (a b : List Nat)
    (ha : a.Pairwise (fun x y => x < y)) (hb : b.Pairwise (fun x y => x < y))
    (hlen : a.length = b.length)
    (hd : ∀ x ∈ a, x ∉ b)
    (hc : ∀ k, natSmaller k b ≤ natSmaller k a) :
    ColumnsLT a b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [ColumnsLT]
  | cons x a ih =>
    cases b with
    | nil => simp at hlen
    | cons y b =>
      obtain ⟨hxa, hat⟩ := List.pairwise_cons.mp ha
      obtain ⟨hyb, hbt⟩ := List.pairwise_cons.mp hb
      have hxy : x < y := by
        have hne : x ≠ y := by
          intro heq
          subst y
          exact hd x (by simp) (by simp)
        by_cases hlt : x < y
        · exact hlt
        · have hz : natSmaller (y+1) (x::a) = 0 :=
            natSmaller_above _ _ (by
              intro z hz
              simp only [List.mem_cons] at hz
              obtain rfl | hz := hz
              · omega
              · have h := hxa z hz; omega)
          have hh := hc (y+1)
          rw [hz] at hh
          simp only [natSmaller, show y < y+1 by omega, ↓reduceIte] at hh
          omega
      change x < y ∧ ColumnsLT a b
      refine ⟨hxy, ?_⟩
      apply ih b hat hbt (by simpa using hlen)
      · intro z hz hzb
        exact hd z (by simp [hz]) (by simp [hzb])
      · intro k
        have hh := hc k
        by_cases hxk : x < k
        · by_cases hyk : y < k
          · simp only [natSmaller, if_pos hxk, if_pos hyk] at hh
            omega
          · have hz : natSmaller k b = 0 := natSmaller_above _ _ (by
              intro z hz
              have h := hyb z hz
              omega)
            rw [hz]
            omega
        · have hyk : ¬ y < k := by omega
          simpa only [natSmaller, if_neg hxk, if_neg hyk, Nat.zero_add] using hh

theorem positions_disjoint (i : Nat) (x y : Letter) (w : Word) (hxy : x ≠ y) :
    ∀ j ∈ positionsFrom i x w, j ∉ positionsFrom i y w := by
  induction w generalizing i with
  | nil => simp [positionsFrom]
  | cons a w ih =>
    intro j hj hother
    by_cases hx : a = x
    · have hy : a ≠ y := by intro hh; exact hxy (hx.symm.trans hh)
      simp only [positionsFrom, if_pos hx, if_neg hy, List.mem_cons] at hj hother
      obtain heq | hj := hj
      · subst j
        have h := positions_lower_bound (i+1) y w i hother
        omega
      · exact ih (i+1) j hj hother
    · by_cases hy : a = y
      · simp only [positionsFrom, if_neg hx, if_pos hy, List.mem_cons] at hj hother
        obtain heq | hother := hother
        · subst j
          have h := positions_lower_bound (i+1) x w i hj
          omega
        · exact ih (i+1) j hj hother
      · simp only [positionsFrom, if_neg hx, if_neg hy] at hj hother
        exact ih (i+1) j hj hother

structure Tableau3 where
  first : List Nat
  second : List Nat
  third : List Nat
  deriving DecidableEq, Repr

def Tableau3.rows (t : Tableau3) : List (List Nat) := [t.first,t.second,t.third]
def Tableau3.reading (t : Tableau3) : List Nat := t.third ++ t.second ++ t.first

/-- Conventional three-row rectangular standard tableau, in English row order. -/
structure Standard3 (n : Nat) (t : Tableau3) : Prop where
  positive : 0 < n
  first_length : t.first.length = n
  second_length : t.second.length = n
  third_length : t.third.length = n
  first_sorted : t.first.Pairwise (fun x y => x < y)
  second_sorted : t.second.Pairwise (fun x y => x < y)
  third_sorted : t.third.Pairwise (fun x y => x < y)
  first_second : ColumnsLT t.first t.second
  second_third : ColumnsLT t.second t.third
  entries : t.reading.Perm (List.range' 1 (3*n))

def wordTableau (w : Word) : Tableau3 :=
  ⟨positionsFrom 1 A w, positionsFrom 1 B w, positionsFrom 1 C w⟩

theorem reading_wordTableau (w : Word) : (wordTableau w).reading = permutation w := rfl

theorem standard_wordTableau (w : Word) (n : Nat) (hn : 0 < n)
    (hdom : Dominant w) (hcontent : ∀ x, count x w = n) :
    Standard3 n (wordTableau w) := by
  have hlen : w.length = 3*n := by
    have hh := total_counts w
    simp only [hcontent] at hh
    omega
  have hpref (k : Nat) := dominant_prefix_counts w (w.take k) (w.drop k)
    hdom (List.take_append_drop k w).symm
  have hAB : ∀ k, natSmaller k (positionsFrom 1 B w) ≤ natSmaller k (positionsFrom 1 A w) := by
    intro k
    rw [natSmaller_positions, natSmaller_positions]
    exact (hpref (k-1)).1
  have hBC : ∀ k, natSmaller k (positionsFrom 1 C w) ≤ natSmaller k (positionsFrom 1 B w) := by
    intro k
    rw [natSmaller_positions, natSmaller_positions]
    exact (hpref (k-1)).2
  refine ⟨hn, ?_, ?_, ?_, positions_sorted 1 A w, positions_sorted 1 B w,
    positions_sorted 1 C w, ?_, ?_, ?_⟩
  · exact (length_positions 1 A w).trans (hcontent A)
  · exact (length_positions 1 B w).trans (hcontent B)
  · exact (length_positions 1 C w).trans (hcontent C)
  · exact columns_of_prefix_counts _ _ (positions_sorted 1 A w) (positions_sorted 1 B w)
      (by simp [wordTableau, length_positions, hcontent]) (positions_disjoint 1 A B w (by decide)) hAB
  · exact columns_of_prefix_counts _ _ (positions_sorted 1 B w) (positions_sorted 1 C w)
      (by simp [wordTableau, length_positions, hcontent]) (positions_disjoint 1 B C w (by decide)) hBC
  · rw [reading_wordTableau, ← hlen]
    exact permutation_perm_range w

def rectangularRecording (n : Nat) : List (List Nat) :=
  [List.range' 1 n, List.range' (n+1) n, List.range' (2*n+1) n]

/-- Published RSK row-reading results, with P and Q supplied by the surrounding
formalization of RSK. Both clauses quantify over every standard rectangle. -/
structure RowReadingTheorems (insertion recording : List Nat → List (List Nat)) : Prop where
  insertion_reading : ∀ n t, Standard3 n t → insertion t.reading = t.rows
  recording_reading : ∀ n t, Standard3 n t → recording t.reading = rectangularRecording n

theorem family_RSK (insertion recording : List Nat → List (List Nat))
    (href : RowReadingTheorems insertion recording) (m : Nat) :
    insertion (xPermutation m) = (wordTableau (aWord m)).rows ∧
    insertion (yPermutation m) = (wordTableau (cWord m)).rows ∧
    recording (xPermutation m) = rectangularRecording (N m) ∧
    recording (yPermutation m) = rectangularRecording (N m) := by
  have ha := standard_wordTableau (aWord m) (N m) (by unfold N; omega)
    (dominant_a m) (content_a m)
  have hc := standard_wordTableau (cWord m) (N m) (by unfold N; omega)
    (dominant_c m) (content_c m)
  exact ⟨href.insertion_reading _ _ ha, href.insertion_reading _ _ hc,
    href.recording_reading _ _ ha, href.recording_reading _ _ hc⟩

/-- Type A left-cell classification is passed in as a separate, general reference
input. The paper's common-cell conclusion is then a theorem. -/
theorem family_common_left_cell (insertion recording : List Nat → List (List Nat))
    (sameLeftCell : List Nat → List Nat → Prop)
    (href : RowReadingTheorems insertion recording)
    (hcell : ∀ p q n, p.Perm (List.range' 1 n) → q.Perm (List.range' 1 n) →
      recording p = recording q → sameLeftCell p q) (m : Nat) :
    sameLeftCell (xPermutation m) (yPermutation m) := by
  have hr := family_RSK insertion recording href m
  apply hcell _ _ (12+9*m)
  · simpa [length_a] using permutation_perm_range (aWord m)
  · simpa [length_c] using permutation_perm_range (cWord m)
  · exact hr.2.2.1.trans hr.2.2.2.symm

theorem columns_prefix_counts (a b : List Nat) (h : ColumnsLT a b) (k : Nat) :
    natSmaller k b ≤ natSmaller k a := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [ColumnsLT, natSmaller]
  | cons x a ih =>
    cases b with
    | nil => simp [natSmaller]
    | cons y b =>
      have hxy := h.1
      have ht := ih b h.2
      simp only [natSmaller]
      split <;> split <;> omega

theorem safe_of_prefix_chambers (s : Chamber) (w : Word)
    (h : ∀ p q, w=p++q → 0 ≤ (run s p).1 ∧ 0 ≤ (run s p).2) : Safe s w := by
  induction w generalizing s with
  | nil => exact h [] [] rfl
  | cons x w ih =>
    constructor
    · exact h [] (x::w) rfl
    · apply ih (step s x)
      intro p q hpq
      exact h (x::p) q (by simp [hpq])

/-- The elementary dominance/standard-tableau equivalence in both directions. -/
theorem standard_wordTableau_iff (w : Word) (n : Nat) (hn : 0 < n) :
    Standard3 n (wordTableau w) ↔ Dominant w ∧ ∀ x, count x w=n := by
  constructor
  · intro hs
    constructor
    · apply safe_of_prefix_chambers (0,0) w
      intro p q hpq
      have hAB := columns_prefix_counts _ _ hs.first_second (p.length+1)
      have hBC := columns_prefix_counts _ _ hs.second_third (p.length+1)
      simp only [wordTableau, natSmaller_positions, Nat.add_sub_cancel] at hAB hBC
      rw [hpq, List.take_append, List.take_length, Nat.sub_self, List.take_zero,
        List.append_nil] at hAB hBC
      rw [run_counts]
      simp only
      omega
    · intro x
      cases x with
      | A => exact (length_positions 1 A w).symm.trans hs.first_length
      | B => exact (length_positions 1 B w).symm.trans hs.second_length
      | C => exact (length_positions 1 C w).symm.trans hs.third_length
  · intro h
    exact standard_wordTableau w n hn h.1 h.2

#print axioms standard_wordTableau_iff
#print axioms standard_wordTableau
#print axioms family_RSK
#print axioms family_common_left_cell
end WebMu.Revised.Tableaux
