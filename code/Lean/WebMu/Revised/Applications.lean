import WebMu.RevisedLocal
import WebMu.Revised.TwoRows

/-! Concrete applications to the corrected shortened tensor.  Exterior blocks
are indexed by their base-three word encodings, with the lengths fixed by the
prefix (6), block (9), and tail (6) construction. -/
namespace WebMu.Revised
open Laurent

def interfaceIndices : List (Fin 28) := List.finRange 28

theorem interfaceIndices_nodup : interfaceIndices.Nodup := by decide
theorem interfaceIndices_mem (i : Fin 28) : i ∈ interfaceIndices := by
  revert i
  decide

def prefixCoordinate (o : Word) (i : Fin 28) : Laurent := (prefixHat i.val).getD o []
def blockCoordinate (e : Nat) (i j : Fin 28) : Laurent :=
  (blockHat j.val).getD (i.val,e) []
def tailCoordinate (r : Nat) (i : Fin 28) : Laurent := tailHat.getD (i.val,r) []

def gaugedTensor (o : Word) (es : List Nat) (r : Nat) : Laurent :=
  tensorCoefficient interfaceIndices (prefixCoordinate o) blockCoordinate (tailCoordinate r) es

theorem bounded_nonpositive (p : Laurent) (h : bounded 0 p = true) : Nonpositive p := by
  have hh : canonical p = true ∧ p.all (fun term => term.1 ≤ 0) = true := by
    simpa [bounded] using h
  exact hh.2

theorem prefixCoordinate_nonpositive (o : Word) (i : Fin 28) :
    Nonpositive (prefixCoordinate o i) := bounded_nonpositive _ (prefix_integral i o)

theorem blockCoordinate_nonpositive (e : Nat) (i j : Fin 28) :
    Nonpositive (blockCoordinate e i j) := bounded_nonpositive _ (block_integral j (i.val,e))

theorem tailCoordinate_nonpositive (r : Nat) (i : Fin 28) :
    Nonpositive (tailCoordinate r i) := bounded_nonpositive _ (tail_integral (i.val,r))

theorem prefixCoordinate_constant (o : Word) :
    coeff (prefixCoordinate o 0) 0 = if o = wordY then 1 else 0 := by
  simpa [prefixCoordinate] using prefix_leading o

theorem blockCoordinate_constant (e : Nat) (i : Fin 28) :
    coeff (blockCoordinate e i 0) 0 =
      if i = 0 then (if e = encode wordU then 1 else 0) else 0 := by
  change coeff ((blockHat 0).getD (i.val,e) []) 0 = _
  rw [block_leading]
  simp only [beq_iff_eq, Prod.mk.injEq]
  have hi : i.val = 0 ↔ i = 0 := ⟨fun h => Fin.ext h, congrArg Fin.val⟩
  split <;> split <;> (try split) <;> grind

theorem tailCoordinate_constant (r : Nat) (i : Fin 28) :
    coeff (tailCoordinate r i) 0 =
      if i = 0 then (if r = encode wordV then 1 else 0) else 0 := by
  change coeff (tailHat.getD (i.val,r) []) 0 = _
  rw [tail_leading]
  simp only [beq_iff_eq, Prod.mk.injEq]
  have hi : i.val = 0 ↔ i = 0 := ⟨fun h => Fin.ext h, congrArg Fin.val⟩
  split <;> split <;> (try split) <;> grind

/-- Proposition 5.12's lattice conclusion, for every parameter and exterior coordinate. -/
theorem gauged_tensor_unique_leading (o : Word) (es : List Nat) (r : Nat) :
    Nonpositive (gaugedTensor o es r) ∧
    coeff (gaugedTensor o es r) 0 =
      if o = wordY ∧ es = List.replicate es.length (encode wordU) ∧ r = encode wordV
      then 1 else 0 := by
  exact tensor_unique_leading_state interfaceIndices interfaceIndices_nodup 0
    (interfaceIndices_mem 0) prefixCoordinate blockCoordinate tailCoordinate
    wordY (encode wordU) (encode wordV) prefixCoordinate_nonpositive
    blockCoordinate_nonpositive tailCoordinate_nonpositive prefixCoordinate_constant
    blockCoordinate_constant tailCoordinate_constant o es r

def selectedGaugedCoefficient (m : Nat) : Laurent :=
  Laurent.sum (interfaceIndices.map (fun i => mul (selectedPrefix i.val)
    (iterate interfaceIndices (fun i j => selectedBlock i.val j.val)
      (fun i => selectedTail i.val) m i)))

/-- All-parameter first-order coefficient for the actual finite local maps. -/
theorem selected_gauged_coefficient (m : Nat) :
    coeff (selectedGaugedCoefficient m) (-1) =
      if m % 2 = 0 then (2:Int)^(m/2) else 0 := by
  apply selected_coefficient interfaceIndices interfaceIndices_nodup
    (fun i => selectedPrefix i.val) (fun i j => selectedBlock i.val j.val)
    (fun i => selectedTail i.val) 5 27 (interfaceIndices_mem 5) (interfaceIndices_mem 27)
  · intro i
    exact bounded_nonpositive _ (prefix_integral i wordEnd)
  · intro i j
    exact bounded_nonpositive _ (block_integral j (i.val,encode wordBlock))
  · intro i
    exact bounded_nonpositive _ (tail_integral (i.val,encode wordEnd))
  · exact selected_tail_constant
  · intro i
    simpa [Fin.ext_iff] using selected_prefix_constant i
  · intro i
    simpa [Fin.ext_iff] using selected_ABC_constant i
  · intro i
    simpa [Fin.ext_iff] using selected_scalar_constant i
  · simpa using selected_tail_first (5 : Fin 28)
  · simpa using selected_tail_first (27 : Fin 28)

theorem selected_gauged_even (r : Nat) :
    coeff (selectedGaugedCoefficient (2*r)) (-1) = (2:Int)^r := by
  rw [selected_gauged_coefficient]
  have hm : (2*r) % 2 = 0 := by omega
  have hd : (2*r) / 2 = r := by omega
  simp [hm, hd]

theorem selected_gauged_odd (r : Nat) :
    coeff (selectedGaugedCoefficient (2*r+1)) (-1) = 0 := by
  rw [selected_gauged_coefficient]
  have hm : (2*r+1) % 2 ≠ 0 := by omega
  simp [hm]

theorem wordIterate_replicate {ι ε : Type} (indices : List ι)
    (a : ε → ι → ι → Laurent) (q : ι → Laurent) (e : ε) (m : Nat) :
    wordIterate indices a q (List.replicate m e) = iterate indices (a e) q m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ, wordIterate, iterate, ih]

/-- The selected readout is a coefficient of the same tensor as the lattice induction. -/
theorem selected_is_gaugedTensor (m : Nat) :
    selectedGaugedCoefficient m =
      gaugedTensor wordEnd (List.replicate m (encode wordBlock)) (encode wordEnd) := by
  simp only [gaugedTensor, tensorCoefficient, wordIterate_replicate,
    selectedGaugedCoefficient, selectedPrefix, selectedBlock, selectedTail,
    prefixCoordinate, blockCoordinate, tailCoordinate]
  rfl

end WebMu.Revised
