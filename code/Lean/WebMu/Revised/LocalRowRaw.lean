import WebMu.Revised.SelectedRowDerivation
import WebMu.Revised.CapDiagram
import WebMu.Revised.Reindex

/-! Literal gauge multiplication followed by the diagrammatic cap identities.
The finite raw certificate below checks only the unsimplified multiplication;
its simplification uses the actual square/digon proofs. -/
namespace WebMu.Revised.LocalDegreeProof
open Laurent Algebra Bar AtlasRealization CapDiagram SelectedRowDerivation
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def shiftMap {α : Type} [BEq α] [Hashable α] (x : Std.HashMap α Laurent)
    (h : α → Int) : Std.HashMap α Laurent :=
  x.fold (fun out k p => accumulate out k (shiftScale p (h k) 1)) ∅

theorem shiftMap_lookup {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (h : α → Int) (k : α) :
    ofList ((shiftMap x h).getD k [])=ofList (shiftScale (x.getD k []) (h k) 1) := by
  rw [shiftMap,hashmap_fold_poly]
  have he : total x.toList (fun (j,p) => if j==k then ofList (shiftScale p (h j) 1) else 0)=
      total x.toList (fun (j,p) => if j==k then ofList (shiftScale p (h k) 1) else 0) := by
    apply total_congr_mem
    rintro ⟨j,p⟩ _
    by_cases hj : j=k <;> simp [hj]
  rw [he,hashmap_total_lookup x k (fun p => ofList (shiftScale p (h k) 1)) rfl]

def upperRaw (j : Nat) : Tensor :=
  sumTensor [rawB j,scaleTensor rawC (neg (shiftScale (eta j) (-1) 1))]

def lowerRaw (j : Nat) : Tensor := sumTensor [
  scaleTensor (cap (rawB j)) (monomial (-1)),
  scaleTensor (rawD j) (monomial 0 (-1)),
  scaleTensor (cap rawC) (neg (shiftScale (eta j) (-2) 1)),
  scaleTensor tau3 (mul d (shiftScale (eta j) (-1) 1))]

def lowerScalarRaw : Tensor := sumTensor [
  scaleTensor (cap rawC) (monomial (-1)),scaleTensor tau3 (neg d)]

def tailScalarRaw : Tensor := sumTensor [
  scaleTensor (cap rawQ) (monomial (-1)),scaleTensor tau2 (monomial 0 (-1))]

def rawHat (j : Nat) : Column :=
  addColumn (shiftMap (splitColumn (upperRaw j)) (fun k => height k.1-height j))
    (putRow (shiftMap (encodeExterior (lowerRaw j)) (fun _ => -height j)) 27)

def rawScalar : Column := addColumn
  (shiftMap (splitColumn rawC) (fun k => height k.1))
  (putRow (encodeExterior lowerScalarRaw) 27)

def rawTail : Column := addColumn
  (shiftMap (splitColumn rawQ) (fun k => height k.1))
  (putRow (encodeExterior tailScalarRaw) 27)

set_option maxHeartbeats 0 in
/-- The four terms in lowerRaw are the literal lower-left gauge product,
with the cap of B and cap of C left unreduced. -/
theorem raw_multiplication_check :
    (∀ j : Fin 27, sameEntries (blockHat j) (rawHat j)=true) ∧
    sameEntries (blockHat 27) rawScalar=true ∧ sameEntries tailHat rawTail=true := by
  native_decide

set_option maxHeartbeats 0 in
theorem raw_support_check :
    (∀ j : Fin 27,
      allEntries (upperRaw j) (fun w _ => validWord 12 w)=true ∧
      allEntries (lowerRaw j) (fun w _ => validWord 9 w)=true) ∧
    allEntries lowerScalarRaw (fun w _ => validWord 9 w)=true ∧
    allEntries tailScalarRaw (fun w _ => validWord 6 w)=true := by native_decide

theorem upper_raw_formula (j i : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    ofList ((blockHat j).getD (i.val,encode w) [])=
      ofList (shiftScale ((upperRaw j).getD (triple i++w) []) (height i-height j) 1) := by
  rw [sameEntries_getD _ _ (raw_multiplication_check.1 j)]
  change ofList ((addMap _ _).getD (i.val,encode w) [])=_
  rw [addMap_poly,shiftMap_lookup,putRow_poly,if_neg (show 27≠i.val by omega),poly_add_zero]
  apply shift_congr
  have h := splitColumn_lookup _ 9 ((raw_support_check.1 j).1)
    (triple i) w (Revised.triple_valid i) ((validWord_iff _ _).mp hw)
  simpa only [encode_triple] using h

theorem lower_raw_formula (j : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    ofList ((blockHat j).getD (27,encode w) [])=
      ofList (shiftScale ((lowerRaw j).getD w []) (-height j) 1) := by
  rw [sameEntries_getD _ _ (raw_multiplication_check.1 j)]
  change ofList ((addMap _ _).getD (27,encode w) [])=_
  rw [addMap_poly,shiftMap_lookup,putRow_poly,if_pos rfl,shiftMap_lookup]
  have hz := splitColumn_interface_lt _ 9 ((raw_support_check.1 j).1) (encode w)
  have hz' := shift_congr hz (height 27-height j) 1
  change ofList (shiftScale _ _ 1)=0 at hz'
  rw [hz',poly_zero_add]
  apply shift_congr
  exact encodeExterior_lookup _ 9 ((raw_support_check.1 j).2) w ((validWord_iff _ _).mp hw)

theorem upper_scalar_raw_formula (i : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    ofList ((blockHat 27).getD (i.val,encode w) [])=
      ofList (shiftScale (rawC.getD (triple i++w) []) (height i) 1) := by
  rw [sameEntries_getD _ _ raw_multiplication_check.2.1]
  change ofList ((addMap _ _).getD (i.val,encode w) [])=_
  rw [addMap_poly,shiftMap_lookup,putRow_poly,if_neg (show 27≠i.val by omega),poly_add_zero]
  apply shift_congr
  have h := splitColumn_lookup _ 9 scalar_boundaries_check.1
    (triple i) w (Revised.triple_valid i) ((validWord_iff _ _).mp hw)
  simpa only [encode_triple] using h

theorem lower_scalar_raw_formula (w : Word) (hw : validWord 9 w=true) :
    ofList ((blockHat 27).getD (27,encode w) [])=ofList (lowerScalarRaw.getD w []) := by
  rw [sameEntries_getD _ _ raw_multiplication_check.2.1]
  change ofList ((addMap _ _).getD (27,encode w) [])=_
  rw [addMap_poly,shiftMap_lookup,putRow_poly,if_pos rfl]
  have hz := shift_congr (splitColumn_interface_lt _ 9 scalar_boundaries_check.1 (encode w)) (height 27) 1
  change ofList (shiftScale _ _ 1)=0 at hz
  rw [hz,poly_zero_add]
  exact encodeExterior_lookup _ 9 raw_support_check.2.1 w ((validWord_iff _ _).mp hw)

theorem tail_upper_formula (i : Fin 27) (w : Word) (hw : validWord 6 w=true) :
    ofList (tailHat.getD (i.val,encode w) [])=
      ofList (shiftScale (rawQ.getD (triple i++w) []) (height i) 1) := by
  rw [sameEntries_getD _ _ raw_multiplication_check.2.2]
  change ofList ((addMap _ _).getD (i.val,encode w) [])=_
  rw [addMap_poly,shiftMap_lookup,putRow_poly,if_neg (show 27≠i.val by omega),poly_add_zero]
  apply shift_congr
  have h := splitColumn_lookup _ 6 scalar_boundaries_check.2.1
    (triple i) w (Revised.triple_valid i) ((validWord_iff _ _).mp hw)
  simpa only [encode_triple] using h

theorem tail_scalar_raw_formula (w : Word) (hw : validWord 6 w=true) :
    ofList (tailHat.getD (27,encode w) [])=ofList (tailScalarRaw.getD w []) := by
  rw [sameEntries_getD _ _ raw_multiplication_check.2.2]
  change ofList ((addMap _ _).getD (27,encode w) [])=_
  rw [addMap_poly,shiftMap_lookup,putRow_poly,if_pos rfl]
  have hz := shift_congr (splitColumn_interface_lt _ 6 scalar_boundaries_check.2.1 (encode w)) (height 27) 1
  change ofList (shiftScale _ _ 1)=0 at hz
  rw [hz,poly_zero_add]
  exact encodeExterior_lookup _ 6 raw_support_check.2.2 w ((validWord_iff _ _).mp hw)

theorem ofList_shift (p : Laurent) (e c : Int) :
    ofList (shiftScale p e c)=ofList p * ofList (monomial e c) := by
  apply poly_ext
  intro n
  change coeff (shiftScale p e c) n=coeff (mul p (monomial e c)) n
  rw [Algebra.mul_comm]
  by_cases hc : c=0
  · simp [hc,monomial,mul,shiftScale,coeff]
  · simp [monomial,hc,mul,coeff_add,coeff_shiftScale,coeff]

theorem scaleTensor_coordinate (x : Tensor) (p : Laurent) (w : Word) :
    ofList ((scaleTensor x p).getD w [])=ofList (x.getD w [])*ofList p :=
  scaleMap_poly x p w

theorem poly_mul_left_comm (a b c : Poly) : a*(b*c)=b*(a*c) := by
  rw [← poly_mul_assoc,poly_mul_comm a b,poly_mul_assoc]

theorem upper_formula (j i : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    ofList ((blockHat j).getD (i.val,encode w) [])=
      ofList (shiftScale (add ((rawB j).getD (triple i++w) [])
        (neg (mul (rawC.getD (triple i++w) []) (shiftScale (eta j) (-1) 1))))
        (height i-height j) 1) := by
  rw [upper_raw_formula j i w hw]
  apply shift_congr
  rw [upperRaw,sumTensor_coordinates]
  simp only [total_cons,total_nil,poly_add_zero,scaleTensor_coordinate,ofList_add,ofList_neg_factor,ofList_mul,poly_mul_assoc]

end WebMu.Revised.LocalDegreeProof
