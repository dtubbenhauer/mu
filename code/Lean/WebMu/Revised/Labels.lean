import WebMu.Revised.Boundary
import WebMu.Revised.Family

namespace WebMu.Revised

def decodeLetter : Nat → Family.Letter
  | 0 => .A
  | 1 => .B
  | _ => .C

theorem decode_letterCode (a : Family.Letter) : decodeLetter (Family.letterCode a) = a := by
  cases a <;> rfl

theorem decode_encodeLetters (w : Family.Word) :
    (Family.encodeLetters w).map decodeLetter = w := by
  simp [Family.encodeLetters,List.map_map,Function.comp_def,decode_letterCode]

def Boundary.familyWord {m : Nat} (b : Boundary m) : Family.Word := b.word.map decodeLetter

theorem leading_word (m : Nat) :
    (leadingBoundary m).word = Family.encodeLetters (Family.cWord m) := by
  simpa [Boundary.word,leadingBoundary,wordY,wordU,wordV] using (Family.encoded_c m).symm

theorem source_word (m : Nat) :
    (sourceBoundary m).word = Family.encodeLetters (Family.aWord m) := by
  simpa [Boundary.word,sourceBoundary,wordEnd,wordBlock] using (Family.encoded_a m).symm

@[simp] theorem leading_familyWord (m : Nat) : (leadingBoundary m).familyWord = Family.cWord m := by
  simp [Boundary.familyWord,leading_word,decode_encodeLetters]

@[simp] theorem source_familyWord (m : Nat) : (sourceBoundary m).familyWord = Family.aWord m := by
  simp [Boundary.familyWord,source_word,decode_encodeLetters]

theorem blocks_flatten_length (ws : List Word) (hn : ∀ w ∈ ws, w.length = 9) :
    ws.flatten.length = 9 * ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hw := hn w (by simp)
    have ht : ∀ v ∈ ws, v.length = 9 := fun v hv => hn v (by simp [hv])
    simp [hw,ih ht,Nat.mul_add,Nat.add_comm]

theorem boundary_word_length {m : Nat} (b : Boundary m) : b.word.length = 12+9*m := by
  simp only [Boundary.word,List.length_append,b.initial_length,b.terminal_length,
    blocks_flatten_length b.blocks (fun w hw => (b.blocks_valid w hw).1), b.blocks_length]
  omega

theorem flatten_fixed_injective (us vs : List Word)
    (hu : ∀ w ∈ us, w.length = 9) (hv : ∀ w ∈ vs, w.length = 9)
    (hlen : us.length = vs.length) (he : us.flatten = vs.flatten) : us = vs := by
  induction us generalizing vs with
  | nil => simpa using hlen.symm
  | cons u us ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have huv := List.append_inj he ((hu u (by simp)).trans (hv v (by simp)).symm)
      have hut : ∀ w ∈ us, w.length = 9 := fun w hw => hu w (by simp [hw])
      have hvt : ∀ w ∈ vs, w.length = 9 := fun w hw => hv w (by simp [hw])
      have ht := ih vs hut hvt (by simpa using hlen) huv.2
      simp [huv.1,ht]

/-- The chosen tensor-factor cuts give a faithful standard-basis indexing. -/
theorem boundary_word_injective {m : Nat} {a b : Boundary m} (h : a.word = b.word) : a = b := by
  have htail := List.append_inj' h (a.terminal_length.trans b.terminal_length.symm)
  have hinit := List.append_inj htail.1 (a.initial_length.trans b.initial_length.symm)
  have hblocks := flatten_fixed_injective a.blocks b.blocks
    (fun w hw => (a.blocks_valid w hw).1) (fun w hw => (b.blocks_valid w hw).1)
    (a.blocks_length.trans b.blocks_length.symm) hinit.2
  exact Boundary.ext hinit.1 hblocks htail.2

end WebMu.Revised
