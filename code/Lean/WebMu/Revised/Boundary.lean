import WebMu.Revised.Applications
import WebMu.Revised.WordEncoding
import WebMu.Revised.CoefficientBridge

namespace WebMu.Revised
open Laurent Algebra

def Ternary (w : Word) : Prop := ∀ a ∈ w, a < 3

/-- A standard tensor basis index, cut at the actual 6|9|...|9|6 outputs. -/
structure Boundary (m : Nat) where
  initial : Word
  blocks : List Word
  terminal : Word
  initial_length : initial.length = 6
  blocks_length : blocks.length = m
  terminal_length : terminal.length = 6
  initial_ternary : Ternary initial
  blocks_valid : ∀ w ∈ blocks, w.length = 9 ∧ Ternary w
  terminal_ternary : Ternary terminal
  deriving DecidableEq

@[ext] theorem Boundary.ext {m : Nat} {a b : Boundary m}
    (hi : a.initial = b.initial) (hb : a.blocks = b.blocks)
    (ht : a.terminal = b.terminal) : a = b := by
  cases a; cases b; simp_all

def Boundary.word {m : Nat} (b : Boundary m) : Word :=
  b.initial ++ b.blocks.flatten ++ b.terminal

def leadingBoundary (m : Nat) : Boundary m where
  initial := wordY
  blocks := List.replicate m wordU
  terminal := wordV
  initial_length := rfl
  blocks_length := List.length_replicate
  terminal_length := rfl
  initial_ternary := by simp [Ternary,wordY]
  blocks_valid := by intro w hw; have h := List.eq_of_mem_replicate hw; subst w; simp [Ternary,wordU]
  terminal_ternary := by simp [Ternary,wordV]

def sourceBoundary (m : Nat) : Boundary m where
  initial := wordEnd
  blocks := List.replicate m wordBlock
  terminal := wordEnd
  initial_length := rfl
  blocks_length := List.length_replicate
  terminal_length := rfl
  initial_ternary := by simp [Ternary,wordEnd]
  blocks_valid := by intro w hw; have h := List.eq_of_mem_replicate hw; subst w; simp [Ternary,wordBlock]
  terminal_ternary := by simp [Ternary,wordEnd]

theorem map_encode_replicate_iff (ws : List Word) (u : Word)
    (hws : ∀ w ∈ ws, w.length = u.length ∧ Ternary w) (hu : Ternary u) :
    ws.map encode = List.replicate ws.length (encode u) ↔ ws = List.replicate ws.length u := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hw := hws w (by simp)
    have ht : ∀ v ∈ ws, v.length = u.length ∧ Ternary v := by
      intro v hv; exact hws v (by simp [hv])
    simp only [List.map_cons,List.length_cons,List.replicate_succ,List.cons.injEq]
    rw [encode_eq_iff_fixed_length w u hw.2 hu hw.1, ih ht]

def tensorHat (m : Nat) (b : Boundary m) : Poly :=
  ofList (gaugedTensor b.initial (b.blocks.map encode) (encode b.terminal))

theorem tensorHat_integral (m : Nat) (b : Boundary m) (d : Int) (hd : 0 < d) :
    coefficient (tensorHat m b) d = 0 := by
  exact coeff_positive _ (gauged_tensor_unique_leading _ _ _).1 d hd

theorem tensorHat_constant (m : Nat) (b : Boundary m) :
    coefficient (tensorHat m b) 0 = if b = leadingBoundary m then 1 else 0 := by
  classical
  change coeff (gaugedTensor b.initial (b.blocks.map encode) (encode b.terminal)) 0 = _
  rw [(gauged_tensor_unique_leading _ _ _).2, List.length_map]
  have hb : b.blocks.map encode = List.replicate b.blocks.length (encode wordU) ↔
      b.blocks = List.replicate b.blocks.length wordU :=
    map_encode_replicate_iff b.blocks wordU b.blocks_valid (by simp [Ternary,wordU])
  have ht : encode b.terminal = encode wordV ↔ b.terminal = wordV :=
    encode_eq_iff_fixed_length b.terminal wordV b.terminal_ternary (by simp [Ternary,wordV]) b.terminal_length
  have hi : b.initial = wordY ∧ b.blocks = List.replicate b.blocks.length wordU ∧
      b.terminal = wordV ↔ b = leadingBoundary m := by
    constructor
    · rintro ⟨h₁,h₂,h₃⟩
      apply Boundary.ext h₁ _ h₃
      simpa [leadingBoundary,b.blocks_length] using h₂
    · intro h; subst b; simp [leadingBoundary]
  simp only [hb,ht,hi]

theorem tensorHat_source_even (r : Nat) :
    coefficient (tensorHat (2*r) (sourceBoundary (2*r))) (-1) = (2:Int)^r := by
  change coeff (gaugedTensor wordEnd ((List.replicate (2*r) wordBlock).map encode)
    (encode wordEnd)) (-1) = _
  rw [List.map_replicate, ← selected_is_gaugedTensor, selected_gauged_even]

end WebMu.Revised
