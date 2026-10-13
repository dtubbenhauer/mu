import WebMu.Revised.Labels
import WebMu.Revised.CircuitSparseSemantics

/-! The complete standard tensor basis, in the manuscript's 6|9|...|9|6 chart.
The inverse and both round trips are proved; no reindexing law is assumed. -/
namespace WebMu.Revised.BoundaryChart
open Bar
set_option maxHeartbeats 0

theorem valid_split (n k : Nat) (w : Word) (h : validWord (n+k) w = true) :
    validWord n (w.take n) = true ∧ validWord k (w.drop n) = true := by
  obtain ⟨hl,ht⟩ := (Revised.validWord_iff _ _).mp h
  constructor
  · apply (Revised.validWord_iff _ _).mpr
    constructor
    · simp [List.length_take,hl]
    · intro a ha
      exact ht a (List.mem_of_mem_take ha)
  · apply (Revised.validWord_iff _ _).mpr
    constructor
    · simp [List.length_drop,hl]
    · intro a ha
      exact ht a (List.mem_of_mem_drop ha)

def chunks : Nat → Word → List Word
  | 0, _ => []
  | m+1,w => w.take 9 :: chunks m (w.drop 9)

theorem chunks_length (m : Nat) (w : Word) : (chunks m w).length = m := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih => simp [chunks,ih]

theorem chunks_reconstruct (m : Nat) (w : Word) :
    (chunks m w).flatten ++ w.drop (9*m) = w := by
  induction m generalizing w with
  | zero => simp [chunks]
  | succ m ih =>
    change (w.take 9 ++ (chunks m (w.drop 9)).flatten) ++ w.drop (9*(m+1)) = w
    rw [List.append_assoc]
    have he : w.drop (9*(m+1)) = (w.drop 9).drop (9*m) := by
      simp only [List.drop_drop]
      congr 1
      omega
    rw [he,ih,List.take_append_drop]

theorem chunks_valid (m : Nat) (w : Word) (hw : validWord (9*m+6) w = true) :
    (∀ u ∈ chunks m w, validWord 9 u = true) ∧
      validWord 6 (w.drop (9*m)) = true := by
  induction m generalizing w with
  | zero => simpa [chunks] using And.intro (by simp : ∀ u ∈ ([] : List Word), validWord 9 u=true) hw
  | succ m ih =>
    have hv : validWord (9+(9*m+6)) w = true := by
      rw [show 9+(9*m+6)=9*(m+1)+6 by omega]
      exact hw
    obtain ⟨hf,ht⟩ := valid_split 9 (9*m+6) w hv
    obtain ⟨hb,he⟩ := ih (w.drop 9) ht
    constructor
    · intro u hu
      simp only [chunks,List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hf
      · exact hb u hu
    · have hd : w.drop (9*(m+1)) = (w.drop 9).drop (9*m) := by
        simp only [List.drop_drop]
        congr 1
        omega
      rw [hd]
      exact he

theorem six_split (m : Nat) (w : Word) (hw : validWord (12+9*m) w = true) :
    validWord 6 (w.take 6) = true ∧ validWord (9*m+6) (w.drop 6) = true := by
  apply valid_split 6 (9*m+6) w
  rw [show 6+(9*m+6)=12+9*m by omega]
  exact hw

def boundaryOfWord (m : Nat) (w : Word) (hw : validWord (12+9*m) w = true) : Boundary m where
  initial := w.take 6
  blocks := chunks m (w.drop 6)
  terminal := (w.drop 6).drop (9*m)
  initial_length := ((Revised.validWord_iff _ _).mp (six_split m w hw).1).1
  blocks_length := chunks_length m (w.drop 6)
  terminal_length := ((Revised.validWord_iff _ _).mp
    (chunks_valid m (w.drop 6) (six_split m w hw).2).2).1
  initial_ternary := ((Revised.validWord_iff _ _).mp (six_split m w hw).1).2
  blocks_valid := by
    intro u hu
    exact (Revised.validWord_iff _ _).mp
      ((chunks_valid m (w.drop 6) (six_split m w hw).2).1 u hu)
  terminal_ternary := ((Revised.validWord_iff _ _).mp
    (chunks_valid m (w.drop 6) (six_split m w hw).2).2).2

@[simp] theorem boundaryOfWord_word (m : Nat) (w : Word)
    (hw : validWord (12+9*m) w = true) : (boundaryOfWord m w hw).word = w := by
  change (w.take 6 ++ (chunks m (w.drop 6)).flatten) ++ (w.drop 6).drop (9*m) = w
  rw [List.append_assoc,chunks_reconstruct,List.take_append_drop]

theorem boundary_word_valid {m : Nat} (b : Boundary m) :
    validWord (12+9*m) b.word = true := by
  apply (Revised.validWord_iff _ _).mpr
  refine ⟨boundary_word_length b,?_⟩
  intro a ha
  simp only [Boundary.word,List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · exact b.initial_ternary a ha
  · obtain ⟨u,hu,ha⟩ := List.mem_flatten.mp ha
    exact (b.blocks_valid u hu).2 a ha
  · exact b.terminal_ternary a ha

@[simp] theorem boundaryOfWord_roundtrip {m : Nat} (b : Boundary m) :
    boundaryOfWord m b.word (boundary_word_valid b) = b := by
  apply boundary_word_injective
  exact boundaryOfWord_word _ _ _

theorem boundary_word_surjective (m : Nat) (w : Word)
    (hw : validWord (12+9*m) w = true) : ∃ b : Boundary m, b.word=w :=
  ⟨boundaryOfWord m w hw,boundaryOfWord_word m w hw⟩

/-- Extend a chart vector by zero outside the prescribed full tensor boundary. -/
def extend (m : Nat) (f : Boundary m → Algebra.Poly) (w : Word) : Algebra.Poly :=
  if h : validWord (12+9*m) w = true then f (boundaryOfWord m w h) else 0

@[simp] theorem extend_boundary {m : Nat} (f : Boundary m → Algebra.Poly) (b : Boundary m) :
    extend m f b.word = f b := by
  simp [extend,boundary_word_valid]

end WebMu.Revised.BoundaryChart
