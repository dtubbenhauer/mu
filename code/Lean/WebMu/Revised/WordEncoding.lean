import WebMu.Spider

namespace WebMu.Revised

/-- A fixed-length base-three decoder; leading A's are retained. -/
def decodeWord : Nat → Nat → Word
  | 0, _ => []
  | n+1, i => decodeWord n (i/3) ++ [i%3]

theorem reverse_induction {α : Type} {P : List α → Prop} (hnil : P [])
    (hsnoc : ∀ l a, P l → P (l ++ [a])) (l : List α) : P l := by
  have h : ∀ l : List α, P l.reverse := by
    intro l
    induction l with
    | nil => exact hnil
    | cons a l ih => simpa using hsnoc l.reverse a ih
  simpa using h l.reverse

theorem encode_snoc (w : Word) (a : Nat) : encode (w ++ [a]) = 3 * encode w + a := by
  simp [encode, List.foldl_append]

theorem decodeWord_encode (w : Word) (hw : ∀ a ∈ w, a < 3) :
    decodeWord w.length (encode w) = w := by
  induction w using reverse_induction with
  | hnil => rfl
  | hsnoc w a ih =>
    have ha : a < 3 := hw a (by simp)
    have hquot : (3 * encode w + a) / 3 = encode w := by omega
    have hrem : (3 * encode w + a) % 3 = a := by omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      decodeWord, encode_snoc, hquot, hrem]
    rw [ih (fun b hb => hw b (by simp [hb]))]

/-- The encoding is injective on ternary words of a fixed length. -/
theorem encode_injective_fixed_length (u v : Word) (hu : ∀ a ∈ u, a < 3)
    (hv : ∀ a ∈ v, a < 3) (hlen : u.length = v.length)
    (he : encode u = encode v) : u = v := by
  rw [← decodeWord_encode u hu, ← decodeWord_encode v hv, hlen, he]

theorem encode_eq_iff_fixed_length (u v : Word) (hu : ∀ a ∈ u, a < 3)
    (hv : ∀ a ∈ v, a < 3) (hlen : u.length = v.length) :
    encode u = encode v ↔ u = v :=
  ⟨encode_injective_fixed_length u v hu hv hlen, congrArg encode⟩

end WebMu.Revised
