import WebMu.Revised.Tableaux

/-!
The row-bumping proof of Lemma `lem:rectangular-cell`, using the insertion
algorithm itself. `insert` handles an arbitrary number of rows and propagates
every bumped entry to the next row. The computation starts with no rows.
-/
namespace WebMu.Revised.RSKBumping
open Family Tableaux

/-- Insert into an increasing row: replace the first entry strictly greater
than `x`, returning that bumped entry; otherwise append `x`. -/
def rowInsert (x : Nat) : List Nat → List Nat × Option Nat
  | [] => ([x], none)
  | y :: ys =>
    if x < y then (x :: ys, some y)
    else let r := rowInsert x ys; (y :: r.1, r.2)

/-- Row insertion, together with the (zero-based) row of the new box. -/
def insert (x : Nat) : List (List Nat) → List (List Nat) × Nat
  | [] => ([[x]], 0)
  | row :: rows =>
    let r := rowInsert x row
    match r.2 with
    | none => (r.1 :: rows, 0)
    | some y => let s := insert y rows; (r.1 :: s.1, s.2 + 1)

/-- Place the next time-label in the row of the newly created box. -/
def record : Nat → Nat → List (List Nat) → List (List Nat)
  | 0, k, [] => [[k]]
  | j+1, k, [] => [] :: record j k []
  | 0, k, row :: rows => (row ++ [k]) :: rows
  | j+1, k, row :: rows => row :: record j k rows

structure State where
  p : List (List Nat)
  q : List (List Nat)
  deriving DecidableEq, Repr

def step (k x : Nat) (s : State) : State :=
  let r := insert x s.p
  ⟨r.1, record r.2 k s.q⟩

def run (k : Nat) : List Nat → State → State
  | [], s => s
  | x::xs, s => run (k+1) xs (step k x s)

def empty : State := ⟨[], []⟩
def computation (w : List Nat) : State := run 1 w empty

def insertion (w : List Nat) := (computation w).p
def recording (w : List Nat) := (computation w).q

theorem rowInsert_append (x : Nat) (p : List Nat)
    (h : ∀ z ∈ p, z ≤ x) : rowInsert x p = (p ++ [x], none) := by
  induction p with
  | nil => rfl
  | cons y ys ih =>
    have hy : ¬ x < y := by have := h y (by simp); omega
    simp only [rowInsert, if_neg hy, ih (by intro z hz; exact h z (by simp [hz]))]
    rfl

theorem rowInsert_bump (x y : Nat) (p s : List Nat)
    (h : ∀ z ∈ p, z ≤ x) (hxy : x < y) :
    rowInsert x (p ++ y::s) = (p ++ x::s, some y) := by
  induction p with
  | nil => simp [rowInsert, hxy]
  | cons z zs ih =>
    have hz : ¬ x < z := by have := h z (by simp); omega
    simp only [List.cons_append, rowInsert, if_neg hz,
      ih (by intro u hu; exact h u (by simp [hu]))]

theorem sorted_prefix_last (p : List Nat) (x : Nat) (s : List Nat)
    (h : (p ++ x::s).Pairwise (· < ·)) : ∀ z ∈ p, z < x := by
  have hh := List.pairwise_append.mp h
  intro z hz
  exact hh.2.2 z hz x (by simp)

theorem run_append (k : Nat) (xs ys : List Nat) (s : State) :
    run k (xs ++ ys) s = run (k+xs.length) ys (run k xs s) := by
  induction xs generalizing k s with
  | nil => simp [run]
  | cons x xs ih =>
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (k+1) (step k x s)

/-- The first block appends successively in row one. -/
theorem first_block (k : Nat) (p xs q₁ : List Nat) (rows qs : List (List Nat))
    (h : (p ++ xs).Pairwise (· < ·)) :
    run k xs ⟨p::rows, q₁::qs⟩ =
      ⟨(p++xs)::rows, (q₁++List.range' k xs.length)::qs⟩ := by
  induction xs generalizing k p q₁ with
  | nil => simp [run]
  | cons x xs ih =>
    have hp := sorted_prefix_last p x xs h
    have hs : step k x ⟨p::rows, q₁::qs⟩ =
        ⟨(p++[x])::rows, (q₁++[k])::qs⟩ := by
      simp [step, insert, rowInsert_append x p (by intro z hz; exact Nat.le_of_lt (hp z hz)), record]
    rw [run, hs, ih (k+1) (p++[x]) (q₁++[k]) (by simpa [List.append_assoc] using h)]
    simp [List.range', List.append_assoc]

/-- In the second block, `b` bumps the matching `c`; that `c` appends
in row two. The prefixes record exactly the intermediate row printed in
the manuscript. -/
theorem second_block (k : Nat) (bp bs cp cs q₁ q₂ : List Nat)
    (rows qs : List (List Nat))
    (hb : (bp ++ bs).Pairwise (· < ·))
    (hc : (cp ++ cs).Pairwise (· < ·)) (hbc : ColumnsLT bs cs) :
    run k bs ⟨(bp++cs)::cp::rows, q₁::q₂::qs⟩ =
      ⟨(bp++bs)::(cp++cs)::rows, q₁::(q₂++List.range' k bs.length)::qs⟩ := by
  induction bs generalizing k bp cp cs q₂ with
  | nil =>
    cases cs with
    | nil => simp [run]
    | cons c cs => simp [ColumnsLT] at hbc
  | cons b bs ih =>
    cases cs with
    | nil => simp [ColumnsLT] at hbc
    | cons c cs =>
      have hbp := sorted_prefix_last bp b bs hb
      have hcp := sorted_prefix_last cp c cs hc
      have hs : step k b ⟨(bp++(c::cs))::cp::rows, q₁::q₂::qs⟩ =
          ⟨((bp++[b])++cs)::(cp++[c])::rows, q₁::(q₂++[k])::qs⟩ := by
        simp [step, insert, rowInsert_bump b c bp cs
          (by intro z hz; exact Nat.le_of_lt (hbp z hz)) hbc.1,
          rowInsert_append c cp (by intro z hz; exact Nat.le_of_lt (hcp z hz)),
          record, List.append_assoc]
      rw [run, hs, ih (k+1) (bp++[b]) (cp++[c]) cs (q₂++[k])
        (by simpa [List.append_assoc] using hb)
        (by simpa [List.append_assoc] using hc) hbc.2]
      simp [List.range', List.append_assoc]

/-- In the third block, `a` bumps the matching `b`, which bumps the
matching `c`; the latter appends in row three. -/
theorem third_block (k : Nat) (ap as bp bs cp cs q₁ q₂ q₃ : List Nat)
    (ha : (ap ++ as).Pairwise (· < ·))
    (hb : (bp ++ bs).Pairwise (· < ·))
    (hc : (cp ++ cs).Pairwise (· < ·))
    (hab : ColumnsLT as bs) (hbc : ColumnsLT bs cs) :
    run k as ⟨[ap++bs,bp++cs,cp], [q₁,q₂,q₃]⟩ =
      ⟨[ap++as,bp++bs,cp++cs], [q₁,q₂,q₃++List.range' k as.length]⟩ := by
  induction as generalizing k ap bp bs cp cs q₃ with
  | nil =>
    cases bs with
    | nil =>
      cases cs with
      | nil => simp [run]
      | cons c cs => simp [ColumnsLT] at hbc
    | cons b bs => simp [ColumnsLT] at hab
  | cons a as ih =>
    cases bs with
    | nil => simp [ColumnsLT] at hab
    | cons b bs =>
      cases cs with
      | nil => simp [ColumnsLT] at hbc
      | cons c cs =>
        have hap := sorted_prefix_last ap a as ha
        have hbp := sorted_prefix_last bp b bs hb
        have hcp := sorted_prefix_last cp c cs hc
        have hs : step k a ⟨[ap++(b::bs),bp++(c::cs),cp], [q₁,q₂,q₃]⟩ =
            ⟨[(ap++[a])++bs,(bp++[b])++cs,cp++[c]], [q₁,q₂,q₃++[k]]⟩ := by
          simp [step, insert, rowInsert_bump a b ap bs
            (by intro z hz; exact Nat.le_of_lt (hap z hz)) hab.1,
            rowInsert_bump b c bp cs
            (by intro z hz; exact Nat.le_of_lt (hbp z hz)) hbc.1,
            rowInsert_append c cp (by intro z hz; exact Nat.le_of_lt (hcp z hz)),
            record, List.append_assoc]
        rw [run, hs, ih (k+1) (ap++[a]) (bp++[b]) bs (cp++[c]) cs (q₃++[k])
          (by simpa [List.append_assoc] using ha)
          (by simpa [List.append_assoc] using hb)
          (by simpa [List.append_assoc] using hc) hab.2 hbc.2]
        simp [List.range', List.append_assoc]

/-- Inserting the increasing c-block into the empty tableau. -/
theorem initial_block (cs : List Nat) (hc : cs.Pairwise (· < ·)) (hne : cs ≠ []) :
    run 1 cs empty = ⟨[cs], [List.range' 1 cs.length]⟩ := by
  cases cs with
  | nil => contradiction
  | cons c cs =>
    have hs : step 1 c empty = ⟨[[c]], [[1]]⟩ := rfl
    rw [run, hs, first_block 2 [c] cs [1] [] [] (by simpa using hc)]
    simp [List.range']

/-- The second block creates row two, and creates no box in row one. -/
theorem middle_block (k : Nat) (bs cs q : List Nat)
    (hb : bs.Pairwise (· < ·)) (hc : cs.Pairwise (· < ·))
    (hbc : ColumnsLT bs cs) (hne : bs ≠ []) :
    run k bs ⟨[cs], [q]⟩ = ⟨[bs,cs], [q,List.range' k bs.length]⟩ := by
  cases bs with
  | nil => contradiction
  | cons b bs =>
    cases cs with
    | nil => simp [ColumnsLT] at hbc
    | cons c cs =>
      have hs : step k b ⟨[c::cs], [q]⟩ = ⟨[b::cs,[c]], [q,[k]]⟩ := by
        simp [step, insert, rowInsert, hbc.1, record]
      rw [run, hs]
      have hh := second_block (k+1) [b] bs [c] cs q [k] [] []
        (by simpa using hb) (by simpa using hc) hbc.2
      simpa [List.range'] using hh

/-- The third block creates row three, bumping through each of the first two. -/
theorem last_block (k : Nat) (as bs cs q₁ q₂ : List Nat)
    (ha : as.Pairwise (· < ·)) (hb : bs.Pairwise (· < ·))
    (hc : cs.Pairwise (· < ·)) (hab : ColumnsLT as bs) (hbc : ColumnsLT bs cs)
    (hne : as ≠ []) :
    run k as ⟨[bs,cs], [q₁,q₂]⟩ =
      ⟨[as,bs,cs], [q₁,q₂,List.range' k as.length]⟩ := by
  cases as with
  | nil => contradiction
  | cons a as =>
    cases bs with
    | nil => simp [ColumnsLT] at hab
    | cons b bs =>
      cases cs with
      | nil => simp [ColumnsLT] at hbc
      | cons c cs =>
        have hs : step k a ⟨[b::bs,c::cs], [q₁,q₂]⟩ =
            ⟨[a::bs,b::cs,[c]], [q₁,q₂,[k]]⟩ := by
          simp [step, insert, rowInsert, hab.1, hbc.1, record]
        rw [run, hs]
        have hh := third_block (k+1) [a] as [b] bs [c] cs q₁ q₂ [k]
          (by simpa using ha) (by simpa using hb) (by simpa using hc) hab.2 hbc.2
        simpa [List.range'] using hh

/-- The complete written computation, including the actual recording tableau.
The three calls to the block lemmas are the three stages of the printed proof. -/
theorem rectangular_computation (n : Nat) (t : Tableau3) (h : Standard3 n t) :
    computation t.reading = ⟨t.rows, rectangularRecording n⟩ := by
  have h₁ : t.first ≠ [] := by
    intro hn
    have := h.first_length
    rw [hn] at this
    have := h.positive
    simp_all
  have h₂ : t.second ≠ [] := by
    intro hn
    have := h.second_length
    rw [hn] at this
    have := h.positive
    simp_all
  have h₃ : t.third ≠ [] := by
    intro hn
    have := h.third_length
    rw [hn] at this
    have := h.positive
    simp_all
  unfold computation Tableau3.reading
  rw [run_append, run_append, initial_block _ h.third_sorted h₃,
    middle_block _ _ _ _ h.second_sorted h.third_sorted h.second_third h₂,
    last_block _ _ _ _ _ _ h.first_sorted h.second_sorted h.third_sorted
      h.first_second h.second_third h₁]
  simp [Tableau3.rows, rectangularRecording, h.first_length, h.second_length,
    h.third_length, Nat.add_assoc, Nat.add_comm]
  omega

theorem rectangular_insertion (n : Nat) (t : Tableau3) (h : Standard3 n t) :
    insertion t.reading = t.rows := by
  exact congrArg State.p (rectangular_computation n t h)

theorem rectangular_recording (n : Nat) (t : Tableau3) (h : Standard3 n t) :
    recording t.reading = rectangularRecording n := by
  exact congrArg State.q (rectangular_computation n t h)

/-- The old row-reading interface is now discharged by the written bumping
proof; neither field is an external reference input. -/
theorem derived_row_reading : RowReadingTheorems insertion recording :=
  ⟨rectangular_insertion, rectangular_recording⟩

/-- Lemma `lem:rectangular-cell` before the cited type-A cell classification. -/
theorem word_rectangular_RSK (w : Word) (n : Nat) (hn : 0 < n)
    (hdom : Dominant w) (hcontent : ∀ x, count x w = n) :
    insertion (permutation w) = (wordTableau w).rows ∧
    recording (permutation w) = rectangularRecording n := by
  have h := standard_wordTableau w n hn hdom hcontent
  exact ⟨rectangular_insertion n _ h, rectangular_recording n _ h⟩

theorem family_RSK_written (m : Nat) :
    insertion (xPermutation m) = (wordTableau (aWord m)).rows ∧
    insertion (yPermutation m) = (wordTableau (cWord m)).rows ∧
    recording (xPermutation m) = rectangularRecording (N m) ∧
    recording (yPermutation m) = rectangularRecording (N m) :=
  family_RSK insertion recording derived_row_reading m

#print axioms rectangular_computation
#print axioms word_rectangular_RSK
#print axioms family_RSK_written
end WebMu.Revised.RSKBumping
