import WebMu.Revised.BarLocal
import WebMu.Revised.OriginalTensor
import WebMu.Revised.SupportBounds

namespace WebMu.Revised.Bar
open Algebra

/-- Coordinate-realization interface. The whole-circuit `closed_coordinates`
and `tensor_identity_coordinates` fields include correctness of the custom
`evalSparse` evaluator. They have not been derived from elementary coordinate
and functor laws; uniform quantification does not discharge that obligation.
Consequently endpoints taking this record are conditional on more than the
published representation-theoretic results. See SEMANTIC_REAUDIT.txt. -/
structure CoordinateReferences (R : BarReferences) where
  coord : (s : Signs) → R.Space s → Word → Poly
  coord_add : ∀ s x y w, coord s (R.add s x y) w = coord s x w + coord s y w
  closed_coordinates : ∀ {s} (f : Circuit [] s) w,
    validWord s.length w = true →
    coord s (R.interpret f R.vacuum) w = ofList ((evalSparse f []).getD w [])
  tensor_identity_coordinates : ∀ {s t} (f : Circuit s t) (r : Signs)
      (x : R.Space (s++r)) (o w : Word),
    validWord t.length o = true → validWord r.length w = true →
    coord (t++r) (R.interpret (.tensor f (.identity r)) x) (o++w) =
      total (List.finRange (3^s.length)) (fun i =>
        ofList ((evalSparse f (decodeWord s.length i.val)).getD o []) *
          coord (s++r) x (decodeWord s.length i.val ++ w))
  /-- The standard tensor bar written in the complete 6|9|...|9|6 basis. -/
  tensorBar : (m : Nat) → (Boundary m → Poly) → Boundary m → Poly
  boundary_coordinates : ∀ m (x : R.Space (positive 6 ++ exterior m)),
    tensorBar m (fun b => coord _ x b.word) =
      fun b => coord _ (R.bar _ x) b.word

theorem coord_cast (R : BarReferences) (C : CoordinateReferences R)
    {s t u : Signs} (f : Circuit s t) (h : t = u) (x : R.Space s) (w : Word) :
    C.coord u (R.interpret (f.cast rfl h) x) w = C.coord t (R.interpret f x) w := by
  cases h
  rfl

def circuitTensor (R : BarReferences) (C : CoordinateReferences R)
    (m : Nat) (b : Boundary m) : Poly :=
  C.coord _ (R.interpret (originalCircuit m) R.vacuum) b.word

theorem circuitTensor_fixed (R : BarReferences) (C : CoordinateReferences R) (m : Nat) :
    C.tensorBar m (circuitTensor R C m) = circuitTensor R C m := by
  unfold circuitTensor
  rw [C.boundary_coordinates, original_circuit_fixed]

theorem validWord_iff (n : Nat) (w : Word) :
    validWord n w = true ↔ w.length = n ∧ Ternary w := by
  simp [validWord, Ternary, List.all_eq_true]

theorem validWord_append {n k : Nat} {u v : Word}
    (hu : validWord n u = true) (hv : validWord k v = true) :
    validWord (n+k) (u++v) = true := by
  rw [validWord_iff] at hu hv ⊢
  constructor
  · simp [hu.1, hv.1]
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hu.2 a ha
    · exact hv.2 a ha

theorem triple_valid (i : Fin 27) : validWord 3 (triple i) = true := by
  revert i
  decide

theorem decode_three (i : Fin 27) : decodeWord 3 i.val = triple i.val := by
  revert i
  decide

theorem exterior_word_valid (es : List Word) (v : Word)
    (he : ∀ w ∈ es, validWord 9 w = true) (hv : validWord 6 v = true) :
    validWord (exterior es.length).length (es.flatten ++ v) = true := by
  induction es with
  | nil => simpa [exterior, positive] using hv
  | cons e es ih =>
    have het : ∀ w ∈ es, validWord 9 w = true := by
      intro w hw
      exact he w (by simp [hw])
    have h := validWord_append (he e (by simp)) (ih het)
    simp only [List.length_cons, exterior, List.length_append, List.flatten_cons]
    change validWord (9 + (exterior es.length).length) ((e ++ es.flatten) ++ v) = true
    simpa only [List.append_assoc] using h

theorem total_append {ι : Type} (xs ys : List ι) (f : ι → Poly) :
    total (xs++ys) f = total xs f + total ys f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, poly_add_assoc]

theorem total_fin28 (f : Fin 28 → Poly) :
    total (List.finRange 28) f =
      total (List.finRange 27) (fun i => f i.castSucc) + f 27 := by
  rw [List.finRange_succ_last, total_append, total_map]
  simp

theorem action_fin28 (a : Fin 28 → Fin 28 → Poly) (x : Fin 28 → Poly) (i : Fin 28) :
    action interfaceIndices a x i =
      total (List.finRange 27) (fun j => a i j.castSucc * x j.castSucc) + a i 27 * x 27 :=
  total_fin28 _

theorem prefix_scalar_zero (w : Word) : originalPrefix w 27 = 0 := by
  change ofList ((shortPrefix 27).getD w []) = 0
  simp [originalPrefix, shortPrefix]

theorem pairing_fin28 (p x : Fin 28 → Poly) (hp : p 27 = 0) :
    pairing interfaceIndices p x =
      total (List.finRange 27) (fun i => p i.castSucc * x i.castSucc) := by
  rw [pairing, show interfaceIndices = List.finRange 28 from rfl, total_fin28]
  simp [hp]

theorem coord_tensor_scalar (R : BarReferences) (C : CoordinateReferences R)
    {t : Signs} (f : Circuit [] t) (r : Signs) (x : R.Space r) (o w : Word)
    (ho : validWord t.length o = true) (hw : validWord r.length w = true) :
    C.coord (t++r) (R.interpret (.tensor f (.identity r)) x) (o++w) =
      ofList ((evalSparse f []).getD o []) * C.coord r x w := by
  rw [C.tensor_identity_coordinates f r x o w ho hw]
  change _ + 0 = _
  exact poly_add_zero _

theorem coord_tensor_triple (R : BarReferences) (C : CoordinateReferences R)
    {t : Signs} (f : Circuit (positive 3) t) (r : Signs)
    (x : R.Space (positive 3 ++ r)) (o w : Word)
    (ho : validWord t.length o = true) (hw : validWord r.length w = true) :
    C.coord (t++r) (R.interpret (.tensor f (.identity r)) x) (o++w) =
      total (List.finRange 27) (fun i =>
        ofList ((evalSparse f (triple i)).getD o []) *
          C.coord (positive 3++r) x (triple i++w)) := by
  rw [C.tensor_identity_coordinates f r x o w ho hw]
  change total (List.finRange 27) _ = _
  apply total_congr_mem
  intro i _
  simp only [show (positive 3).length = 3 from rfl, decode_three]

def upperCoordinate (R : BarReferences) (C : CoordinateReferences R)
    (es : List Word) (v : Word) (i : Fin 27) : Poly :=
  C.coord _ (R.interpret (interfaceCircuit es.length).1 R.vacuum)
    (triple i ++ es.flatten ++ v)

def lowerCoordinate (R : BarReferences) (C : CoordinateReferences R)
    (es : List Word) (v : Word) : Poly :=
  C.coord _ (R.interpret (interfaceCircuit es.length).2 R.vacuum) (es.flatten ++ v)

theorem upperCoordinate_nil (R : BarReferences) (C : CoordinateReferences R)
    (v : Word) (i : Fin 27) (hv : validWord 6 v = true) :
    upperCoordinate R C [] v i = ofList (rawQ.getD (triple i++v) []) := by
  change C.coord _ (R.interpret qCircuit R.vacuum) (triple i ++ [] ++ v) = _
  rw [List.append_nil, C.closed_coordinates qCircuit _
    (validWord_append (n:=3) (k:=6) (triple_valid i) hv), q_circuit]

theorem lowerCoordinate_nil (R : BarReferences) (C : CoordinateReferences R)
    (v : Word) (hv : validWord 6 v = true) :
    lowerCoordinate R C [] v = ofList (tau2.getD v []) := by
  change C.coord _ (R.interpret tauTwoCircuit R.vacuum) ([]++v) = _
  rw [List.nil_append, C.closed_coordinates tauTwoCircuit v hv, tau_two_circuit]

theorem upperCoordinate_cons (R : BarReferences) (C : CoordinateReferences R)
    (e : Word) (es : List Word) (v : Word) (i : Fin 27)
    (he : validWord 9 e = true) (hes : ∀ w ∈ es, validWord 9 w = true)
    (hv : validWord 6 v = true) :
    upperCoordinate R C (e::es) v i =
      total (List.finRange 27) (fun j =>
        ofList ((rawB j).getD (triple i++e) []) * upperCoordinate R C es v j) +
      ofList ((evalSparse (.neg cCircuit) []).getD (triple i++e) []) * lowerCoordinate R C es v := by
  unfold upperCoordinate
  simp only [List.length_cons, interfaceCircuit, upNext, Prod.fst,
    BarReferences.interpret, List.flatten_cons]
  rw [C.coord_add, coord_cast, coord_cast]
  have hb := coord_tensor_triple R C bCircuit (exterior es.length)
    (R.interpret (interfaceCircuit es.length).1 R.vacuum) (triple i++e) (es.flatten++v)
    (validWord_append (n:=3) (k:=9) (triple_valid i) he) (exterior_word_valid es v hes hv)
  have hc := coord_tensor_scalar R C (.neg cCircuit) (exterior es.length)
    (R.interpret (interfaceCircuit es.length).2 R.vacuum) (triple i++e) (es.flatten++v)
    (validWord_append (n:=3) (k:=9) (triple_valid i) he) (exterior_word_valid es v hes hv)
  simp only [List.append_assoc] at hb hc ⊢
  rw [hb, hc]
  simp only [b_circuit, lowerCoordinate, List.append_assoc]

theorem lowerCoordinate_cons (R : BarReferences) (C : CoordinateReferences R)
    (e : Word) (es : List Word) (v : Word)
    (he : validWord 9 e = true) (hes : ∀ w ∈ es, validWord 9 w = true)
    (hv : validWord 6 v = true) :
    lowerCoordinate R C (e::es) v =
      total (List.finRange 27) (fun j =>
        ofList ((rawD j).getD e []) * upperCoordinate R C es v j) +
      ofList ((evalSparse (.neg (.scaleD tauThreeCircuit)) []).getD e []) * lowerCoordinate R C es v := by
  unfold lowerCoordinate
  simp only [List.length_cons, interfaceCircuit, lowNext, Prod.snd,
    BarReferences.interpret, List.flatten_cons]
  rw [C.coord_add]
  have hd := coord_tensor_triple R C dCircuit (exterior es.length)
    (R.interpret (interfaceCircuit es.length).1 R.vacuum) e (es.flatten++v)
    he (exterior_word_valid es v hes hv)
  have ht := coord_tensor_scalar R C (.neg (.scaleD tauThreeCircuit)) (exterior es.length)
    (R.interpret (interfaceCircuit es.length).2 R.vacuum) e (es.flatten++v)
    he (exterior_word_valid es v hes hv)
  simp only [List.append_assoc] at hd ht ⊢
  simp only [BarReferences.interpret] at hd ht
  simp only [exterior]
  rw [hd, ht]
  simp only [d_circuit, upperCoordinate, List.append_assoc]

theorem evalSparse_neg_coefficient {s t : Signs} (f : Circuit s t) (u w : Word) :
    ofList ((evalSparse (.neg f) u).getD w []) =
      ofList ((evalSparse f u).getD w []) * ofList (Laurent.monomial 0 (-1)) := by
  exact scaleMap_poly (evalSparse f u) (Laurent.monomial 0 (-1)) w

theorem evalSparse_scaleD_coefficient {s t : Signs} (f : Circuit s t) (u w : Word) :
    ofList ((evalSparse (.scaleD f) u).getD w []) =
      ofList ((evalSparse f u).getD w []) * ofList d := by
  exact scaleMap_poly (evalSparse f u) d w

theorem ofList_neg (p : Laurent) :
    ofList (Laurent.neg p) = ofList p * ofList (Laurent.monomial 0 (-1)) := by
  apply poly_ext
  intro e
  change Laurent.coeff (Laurent.neg p) e =
    Laurent.coeff (Laurent.mul p (Laurent.monomial 0 (-1))) e
  rw [Algebra.coeff_neg, Algebra.mul_comm]
  simp [Laurent.monomial, Laurent.mul, Laurent.coeff_add, Laurent.coeff_shiftScale,
    Laurent.coeff]

theorem circuitTensor_prefix (R : BarReferences) (C : CoordinateReferences R)
    (m : Nat) (b : Boundary m) :
    circuitTensor R C m b = total (List.finRange 27) (fun i =>
      originalPrefix b.initial i.castSucc * upperCoordinate R C b.blocks b.terminal i) := by
  rcases b with ⟨o,es,v,ho,hes,hv,hot,hest,hvt⟩
  subst m
  have hvo : validWord 6 o = true := (validWord_iff 6 o).mpr ⟨ho,hot⟩
  have hvv : validWord 6 v = true := (validWord_iff 6 v).mpr ⟨hv,hvt⟩
  have hve : ∀ e ∈ es, validWord 9 e = true := by
    intro e he
    exact (validWord_iff 9 e).mpr (hest e he)
  change C.coord _ (R.interpret (originalCircuit es.length) R.vacuum)
    (o ++ es.flatten ++ v) = _
  change C.coord _ (R.interpret (.tensor prefixCircuit (.identity (exterior es.length)))
    (R.interpret (interfaceCircuit es.length).1 R.vacuum)) (o ++ es.flatten ++ v) = _
  rw [List.append_assoc, coord_tensor_triple R C prefixCircuit (exterior es.length) _
    o (es.flatten++v) hvo (exterior_word_valid es v hve hvv)]
  apply total_congr_mem
  intro i _
  rw [prefix_circuit]
  rfl

end WebMu.Revised.Bar
