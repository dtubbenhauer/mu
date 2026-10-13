import WebMu.Revised.OriginalMaps
import WebMu.Revised.SupportBounds
import WebMu.Revised.WordEncoding
import WebMu.Revised.CoordinateBridge

namespace WebMu.Revised
open Laurent Algebra

set_option maxRecDepth 100000
set_option maxHeartbeats 50000

theorem validWord_iff (n : Nat) (w : Word) :
    validWord n w = true ↔ w.length = n ∧ ∀ a ∈ w, a < 3 := by
  simp [validWord, List.all_eq_true]

theorem tensor_entries_valid (x : Tensor) (n : Nat)
    (h : allEntries x (fun w _ => validWord n w) = true)
    (w : Word) (p : Laurent) (hm : (w,p) ∈ x.toList) :
    w.length = n ∧ ∀ a ∈ w, a < 3 :=
  (validWord_iff n w).mp (List.all_eq_true.mp h (w,p) hm)

theorem split_key_injective (n : Nat) (z s w : Word)
    (hz : z.length = 3+n ∧ ∀ a ∈ z, a < 3)
    (hs : s.length = 3 ∧ ∀ a ∈ s, a < 3)
    (hw : w.length = n ∧ ∀ a ∈ w, a < 3) :
    (encode (z.take 3),encode (z.drop 3)) = (encode s,encode w) ↔ z = s++w := by
  constructor
  · intro he
    have htake : (z.take 3).length = s.length := by simp [List.length_take,hz.1,hs.1]
    have hdrop : (z.drop 3).length = w.length := by simp [List.length_drop,hz.1,hw.1]
    have het : z.take 3 = s := encode_injective_fixed_length _ _
      (fun a ha => hz.2 a (List.mem_of_mem_take ha)) hs.2 htake (congrArg Prod.fst he)
    have hed : z.drop 3 = w := encode_injective_fixed_length _ _
      (fun a ha => hz.2 a (List.mem_of_mem_drop ha)) hw.2 hdrop (congrArg Prod.snd he)
    rw [← List.take_append_drop 3 z, het, hed]
  · intro he
    subst z
    have ht : (s++w).take 3 = s := by rw [← hs.1]; simp
    have hd : (s++w).drop 3 = w := by rw [← hs.1]; simp
    simp [ht,hd]

theorem splitColumn_lookup (x : Tensor) (n : Nat)
    (h : allEntries x (fun w _ => validWord (3+n) w) = true)
    (s w : Word) (hs : s.length = 3 ∧ ∀ a ∈ s, a < 3)
    (hw : w.length = n ∧ ∀ a ∈ w, a < 3) :
    ofList ((splitColumn x).getD (encode s,encode w) []) = ofList (x.getD (s++w) []) := by
  rw [splitColumn_poly]
  calc
    total x.toList (fun (z,p) =>
        if (encode (z.take 3),encode (z.drop 3)) == (encode s,encode w) then ofList p else 0) =
      total x.toList (fun (z,p) => if z == s++w then ofList p else 0) := by
        apply total_congr_mem
        rintro ⟨z,p⟩ hm
        have hi := split_key_injective n z s w (tensor_entries_valid x _ h z p hm) hs hw
        simp only [beq_iff_eq, hi]
    _ = ofList (x.getD (s++w) []) := hashmap_total_lookup x (s++w) ofList rfl

theorem encodeExterior_lookup (x : Tensor) (n : Nat)
    (h : allEntries x (fun w _ => validWord n w) = true)
    (w : Word) (hw : w.length = n ∧ ∀ a ∈ w, a < 3) :
    ofList ((encodeExterior x).getD (encode w) []) = ofList (x.getD w []) := by
  rw [encodeExterior_poly]
  calc
    total x.toList (fun (z,p) => if encode z == encode w then ofList p else 0) =
        total x.toList (fun (z,p) => if z == w then ofList p else 0) := by
      apply total_congr_mem
      rintro ⟨z,p⟩ hm
      have hz := tensor_entries_valid x n h z p hm
      have hi := encode_eq_iff_fixed_length z w hz.2 hw.2 (hz.1.trans hw.1.symm)
      by_cases he : z = w
      · simp [he]
      · have hn : encode z ≠ encode w := fun ht => he (hi.mp ht)
        simp [hn,he]
    _ = ofList (x.getD w []) := hashmap_total_lookup x w ofList rfl

theorem triple_valid (i : Fin 27) : (triple i).length = 3 ∧ ∀ a ∈ triple i, a < 3 := by
  have h : ∀ i : Fin 27, validWord 3 (triple i) = true := by decide
  exact (validWord_iff _ _).mp (h i)

theorem encode_triple (i : Fin 27) : encode (triple i) = i.val := by
  revert i
  decide

theorem splitColumn_interface_lt (x : Tensor) (n : Nat)
    (h : allEntries x (fun w _ => validWord (3+n) w) = true) (w : Nat) :
    ofList ((splitColumn x).getD (27,w) []) = 0 := by
  rw [splitColumn_poly]
  calc
    total x.toList (fun (z,p) =>
        if (encode (z.take 3),encode (z.drop 3)) == (27,w) then ofList p else 0) =
        total x.toList (fun _ => 0) := by
      apply total_congr_mem
      rintro ⟨z,p⟩ hm
      have hz := tensor_entries_valid x _ h z p hm
      have ht : (z.take 3).length = 3 := by simp [List.length_take,hz.1]
      have hp : ∀ a ∈ z.take 3, a < 3 := fun a ha => hz.2 a (List.mem_of_mem_take ha)
      have hbound : encode (z.take 3) < 27 := by
        generalize hxs : z.take 3 = xs at ht hp ⊢
        cases xs with
        | nil => simp [encode] at *
        | cons a xs =>
          cases xs with
          | nil => simp_all
          | cons b xs =>
            cases xs with
            | nil => simp_all
            | cons c xs =>
              have hxnil : xs = [] := by
                apply List.length_eq_zero.mp
                simp only [List.length_cons] at ht
                omega
              subst xs
              have ha := hp a (by simp)
              have hb := hp b (by simp)
              have hc := hp c (by simp)
              simp [encode]
              omega
      have hn : (encode (z.take 3),encode (z.drop 3)) ≠ (27,w) := by
        intro he
        have he' := congrArg Prod.fst he
        simp only at he'
        omega
      simp [hn]
    _ = 0 := total_zero _

def webState (i : Fin 27) : Fin 28 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩

@[simp] theorem scalarState_val : (27 : Fin 28).val = 27 := by decide

theorem originalBlock_B (i j : Fin 27) (w : Word)
    (hw : w.length = 9 ∧ ∀ a ∈ w, a < 3) :
    originalBlock (encode w) (webState i) (webState j) =
      ofList ((rawB j).getD (triple i ++ w) []) := by
  unfold originalBlock
  have hsep := original_block_separation (webState j) (i.val,encode w)
  simp only [webState] at hsep ⊢
  rw [hsep]
  have hi : 27 ≠ i.val := by omega
  simp only [separatedBlock,webState,if_pos j.isLt,addMap_poly,putRow_poly,if_neg hi,
    poly_add_zero]
  simpa only [encode_triple i] using
    splitColumn_lookup _ 9 (raw_boundaries_check j).1 _ _ (triple_valid i) hw

theorem originalBlock_D (j : Fin 27) (w : Word)
    (hw : w.length = 9 ∧ ∀ a ∈ w, a < 3) :
    originalBlock (encode w) 27 (webState j) = ofList ((rawD j).getD w []) := by
  unfold originalBlock
  have hsep := original_block_separation (webState j) (27,encode w)
  simp only [webState,scalarState_val] at hsep ⊢
  rw [hsep]
  simp only [separatedBlock,webState,if_pos j.isLt,addMap_poly,putRow_poly,
    scalarState_val, ↓reduceIte]
  rw [splitColumn_interface_lt _ 9 (raw_boundaries_check j).1, poly_zero_add]
  exact encodeExterior_lookup _ 9 (raw_boundaries_check j).2.1 w hw

theorem ofList_neg_factor (p : Laurent) :
    ofList (neg p) = ofList p * ofList (monomial 0 (-1)) := by
  apply poly_ext
  intro z
  change coeff (neg p) z = coeff (mul p (monomial 0 (-1))) z
  rw [Algebra.mul_comm]
  simp [Algebra.coeff_neg, monomial, mul, coeff_add, coeff_shiftScale, coeff]

theorem originalBlock_C (i : Fin 27) (w : Word)
    (hw : w.length = 9 ∧ ∀ a ∈ w, a < 3) :
    originalBlock (encode w) (webState i) 27 = ofList (neg (rawC.getD (triple i++w) [])) := by
  unfold originalBlock
  have hsep := original_block_separation 27 (i.val,encode w)
  simp only [webState,scalarState_val] at hsep ⊢
  rw [hsep]
  have hi : 27 ≠ i.val := by omega
  simp only [separatedBlock,webState,scalarState_val,show ¬27<27 by omega,
    ↓reduceIte,addMap_poly,putRow_poly,if_neg hi,poly_add_zero,scaleMap_poly]
  have he := splitColumn_lookup _ 9 scalar_boundaries_check.1 _ _ (triple_valid i) hw
  simp only [encode_triple i] at he
  rw [he,ofList_neg_factor]

theorem originalBlock_scalar (w : Word)
    (hw : w.length = 9 ∧ ∀ a ∈ w, a < 3) :
    originalBlock (encode w) 27 27 = ofList (mul (neg d) (tau3.getD w [])) := by
  unfold originalBlock
  have hsep := original_block_separation 27 (27,encode w)
  simp only [scalarState_val] at hsep ⊢
  rw [hsep]
  simp only [separatedBlock,scalarState_val,show ¬27<27 by omega,
    ↓reduceIte,addMap_poly,putRow_poly,scaleMap_poly]
  rw [splitColumn_interface_lt _ 9 scalar_boundaries_check.1,poly_zero_mul,poly_zero_add,
    encodeExterior_lookup _ 9 scalar_boundaries_check.2.2.2 w hw,ofList_mul,poly_mul_comm]

theorem originalTail_upper (i : Fin 27) (w : Word)
    (hw : w.length = 6 ∧ ∀ a ∈ w, a < 3) :
    originalTail (encode w) (webState i) = ofList (rawQ.getD (triple i++w) []) := by
  unfold originalTail
  simp only [webState]
  rw [original_tail_separation (i.val,encode w)]
  have hi : 27 ≠ i.val := by omega
  simp only [separatedTail,webState,addMap_poly,putRow_poly,if_neg hi,poly_add_zero]
  simpa only [encode_triple i] using
    splitColumn_lookup _ 6 scalar_boundaries_check.2.1 _ _ (triple_valid i) hw

theorem originalTail_scalar (w : Word)
    (hw : w.length = 6 ∧ ∀ a ∈ w, a < 3) :
    originalTail (encode w) 27 = ofList (tau2.getD w []) := by
  unfold originalTail
  simp only [scalarState_val]
  rw [original_tail_separation (27,encode w)]
  simp only [separatedTail,scalarState_val,addMap_poly,putRow_poly,↓reduceIte]
  rw [splitColumn_interface_lt _ 6 scalar_boundaries_check.2.1,poly_zero_add]
  exact encodeExterior_lookup _ 6 scalar_boundaries_check.2.2.1 w hw

theorem originalPrefix_scalar (w : Word) : originalPrefix w 27 = 0 := by
  simp [originalPrefix,shortPrefix,scalarState_val]

theorem originalPrefix_upper (i : Fin 27) (w : Word) :
    originalPrefix w (webState i) = ofList ((shortPrefix i).getD w []) := rfl

end WebMu.Revised
