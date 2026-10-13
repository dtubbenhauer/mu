import WebMu.Revised.LocalLatticeBounds
import WebMu.Revised.LocalCoordinateStorage
import WebMu.Revised.LocalRowFormulas

/-! Assembly of the local lattice proof from monomial paths, exact offender
cancellation, and the actual diagrammatic cap reductions. -/
namespace WebMu.Revised.LocalDegreeProof
open Laurent Algebra Bar AtlasRealization CapDiagram
set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable (R : BarReferences) (A : AtomicCoordinates R)
  (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
  (T : BoundaryTripodReferences R F)

theorem prefix_nonpositive_from_paths (w : Word) (j : Fin 28) :
    Nonpositive (prefixCoordinate w j) :=
  nonpositive_of_degree _ (prefix_canonical j w) (prefix_degree j w)

include R A F G

include T in
theorem block_word_degree (w : Word) (hw : validWord 9 w=true) (i j : Fin 28) :
    DegreeLE ((blockHat j).getD (i.val,encode w) []) 0 := by
  by_cases hi : i.val<27
  · by_cases hj : j.val<27
    · exact degree_congr (upper_formula ⟨j.val,hj⟩ ⟨i.val,hi⟩ w hw)
        (upper_expression_integral ⟨i.val,hi⟩ ⟨j.val,hj⟩ w)
    · have hj' : j.val=27 := by omega
      rw [hj']
      exact degree_congr (upper_scalar_raw_formula ⟨i.val,hi⟩ w hw)
        (upper_scalar_expression_integral ⟨i.val,hi⟩ w)
  · have hi' : i.val=27 := by omega
    rw [hi']
    by_cases hj : j.val<27
    · exact degree_congr (lower_formula R A F G T ⟨j.val,hj⟩ w hw)
        (lower_expression_integral ⟨j.val,hj⟩ w)
    · have hj' : j.val=27 := by omega
      rw [hj']
      exact degree_congr (lower_scalar_formula R A F G w hw)
        (degree_mono (lower_scalar_negative w) (by decide))

include T in
theorem block_nonpositive_from_local (e : Nat) (i j : Fin 28) :
    Nonpositive (blockCoordinate e i j) := by
  apply nonpositive_of_degree _ (block_canonical j (i.val,e))
  by_cases he : e<3^9
  · have h := block_word_degree R A F G T (decodeWord 9 e) (decode_valid 9 e) i j
    rw [ShortNorm.encode_decode 9 e he] at h
    exact h
  · change DegreeLE ((blockHat j).getD (i.val,e) []) 0
    rw [block_outside j i.val e (by omega)]
    intro d hd; rfl

theorem tail_word_degree (w : Word) (hw : validWord 6 w=true) (i : Fin 28) :
    DegreeLE (tailHat.getD (i.val,encode w) []) 0 := by
  by_cases hi : i.val<27
  · have h := LocalPaths.tail_degree (triple i.val++w)
    rw [height_interface ⟨i.val,hi⟩ w] at h
    have hs := degree_shift h (height i) 1
    have hz : -height i+height i=0 := by omega
    rw [hz] at hs
    exact degree_congr (tail_upper_formula ⟨i.val,hi⟩ w hw) hs
  · have hi' : i.val=27 := by omega
    rw [hi']
    exact degree_congr (tail_scalar_formula R A F G w hw)
      (degree_mono (tail_scalar_negative w) (by decide))

theorem tail_nonpositive_from_local (e : Nat) (i : Fin 28) :
    Nonpositive (tailCoordinate e i) := by
  apply nonpositive_of_degree _ (tail_canonical (i.val,e))
  by_cases he : e<3^6
  · have h := tail_word_degree R A F G (decodeWord 6 e) (decode_valid 6 e) i
    rw [ShortNorm.encode_decode 6 e he] at h
    exact h
  · change DegreeLE (tailHat.getD (i.val,e) []) 0
    rw [tail_outside i.val e (by omega)]
    intro d hd; rfl

omit R A F G

theorem coeff_mul_nil (p : Laurent) (e : Int) : coeff (mul p []) e=0 := by
  rw [Algebra.mul_comm]; rfl

theorem triple_prefix_eq (i : Fin 27) (w u : Word) :
    triple i++w=triple 0++u ↔ i.val=0 ∧ w=u := by
  constructor
  · intro h
    have ht := List.append_inj_left h (by simp [triple])
    have hw := List.append_inj_right h (by simp [triple])
    have hi := congrArg encode ht
    rw [encode_triple] at hi
    exact ⟨hi,hw⟩
  · rintro ⟨hi,hw⟩
    simp [hi,hw]

include R A F G

include T in
theorem block_word_constant (w : Word) (hw : validWord 9 w=true) (i : Fin 28) :
    coeff ((blockHat 0).getD (i.val,encode w) []) 0=
      if i.val=0 ∧ w=wordU then 1 else 0 := by
  by_cases hi : i.val<27
  · have h := congrArg (fun p => coefficient p 0) (upper_formula 0 ⟨i.val,hi⟩ w hw)
    simp only [coefficient_ofList,coeff_shiftScale,coeff_add,Algebra.coeff_neg,Fin.val_zero] at h
    have he : shiftScale (eta 0) (-1) 1=[] := by decide
    have hz : height 0=0 := by decide
    rw [he,hz,coeff_mul_nil] at h
    simp only [Int.sub_zero,Int.zero_sub,Int.neg_zero,Int.add_zero,Int.mul_one] at h
    have hp := LocalPaths.aaa_block_shifted_constant (triple i.val++w)
    rw [height_interface ⟨i.val,hi⟩ w] at hp
    have ht : LocalPaths.word "AAABBBAACACC"=triple 0++wordU := by decide
    simp only [ht,triple_prefix_eq ⟨i.val,hi⟩ w wordU] at hp
    exact h.trans hp
  · have hi' : i.val=27 := by omega
    rw [hi']
    have h := congrArg (fun p => coefficient p 0) (lower_formula R A F G T 0 w hw)
    have hz := lower_zero_input_negative w 0 (by decide)
    change coeff ((blockHat 0).getD (27,encode w) []) 0=coeff (lowerDegreeExpr 0 w) 0 at h
    rw [hz] at h
    simpa using h

theorem tail_word_constant (w : Word) (hw : validWord 6 w=true) (i : Fin 28) :
    coeff (tailHat.getD (i.val,encode w) []) 0=
      if i.val=0 ∧ w=wordV then 1 else 0 := by
  by_cases hi : i.val<27
  · have h := congrArg (fun p => coefficient p 0) (tail_upper_formula ⟨i.val,hi⟩ w hw)
    simp only [coefficient_ofList,coeff_shiftScale,Int.zero_sub,Int.mul_one] at h
    have hp := LocalPaths.tail_shifted_constant (triple i.val++w)
    rw [height_interface ⟨i.val,hi⟩ w] at hp
    have ht : LocalPaths.word "AAABBCBCC"=triple 0++wordV := by decide
    simp only [ht,triple_prefix_eq ⟨i.val,hi⟩ w wordV] at hp
    exact h.trans hp
  · have hi' : i.val=27 := by omega
    rw [hi']
    have h := congrArg (fun p => coefficient p 0) (tail_scalar_formula R A F G w hw)
    have hz := tail_scalar_negative w 0 (by decide)
    change coeff (tailHat.getD (27,encode w) []) 0=coeff _ 0 at h
    rw [hz] at h
    simpa using h

omit R A F G

theorem decode_eq_word (n e : Nat) (he : e<3^n) (u : Word) (hu : validWord n u=true) :
    decodeWord n e=u ↔ e=encode u := by
  have hv := (validWord_iff _ _).mp (decode_valid n e)
  have hut := (validWord_iff _ _).mp hu
  have h := encode_eq_iff_fixed_length (decodeWord n e) u hv.2 hut.2 (hv.1.trans hut.1.symm)
  rw [ShortNorm.encode_decode n e he] at h
  exact h.symm

include R A F G

include T in
theorem block_constant_from_local (e : Nat) (i : Fin 28) :
    coeff (blockCoordinate e i 0) 0=
      if i=0 then (if e=encode wordU then 1 else 0) else 0 := by
  by_cases he : e<3^9
  · have h := block_word_constant R A F G T (decodeWord 9 e) (decode_valid 9 e) i
    simp only [ShortNorm.encode_decode 9 e he,decode_eq_word 9 e he wordU (by decide)] at h
    have hi : i.val=0 ↔ i=0 := ⟨fun h => Fin.ext h,congrArg Fin.val⟩
    simp only [hi] at h
    by_cases hz : i=0 <;> simpa [hz,blockCoordinate] using h
  · change coeff ((blockHat 0).getD (i.val,e) []) 0=_
    have hz := block_outside 0 i.val e (by omega)
    simp only [Fin.val_zero] at hz
    rw [hz]
    have hu : encode wordU<3^9 := by decide
    have hn : e≠encode wordU := by omega
    simp [coeff,hn]

theorem tail_constant_from_local (e : Nat) (i : Fin 28) :
    coeff (tailCoordinate e i) 0=
      if i=0 then (if e=encode wordV then 1 else 0) else 0 := by
  by_cases he : e<3^6
  · have h := tail_word_constant R A F G (decodeWord 6 e) (decode_valid 6 e) i
    simp only [ShortNorm.encode_decode 6 e he,decode_eq_word 6 e he wordV (by decide)] at h
    have hi : i.val=0 ↔ i=0 := ⟨fun h => Fin.ext h,congrArg Fin.val⟩
    simp only [hi] at h
    by_cases hz : i=0 <;> simpa [hz,tailCoordinate] using h
  · change coeff (tailHat.getD (i.val,e) []) 0=_
    rw [tail_outside i.val e (by omega)]
    have hu : encode wordV<3^6 := by decide
    have hn : e≠encode wordV := by omega
    simp [coeff,hn]

#print axioms block_nonpositive_from_local
#print axioms block_constant_from_local
#print axioms tail_constant_from_local
end WebMu.Revised.LocalDegreeProof
