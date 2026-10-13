import WebMu.Revised.AtomicBoundaryBar
import WebMu.Revised.CircuitSparseSemantics
import WebMu.Revised.CircuitSupport

/-! Correctness of the executable spider evaluator from atomic coordinate laws.
The proofs in this module, rather than fields of a reference record, establish
the interpretation of arbitrary typed circuits. -/
namespace WebMu.Revised.Bar
open Algebra GrowthBridge

set_option maxHeartbeats 0

theorem decoded_word_valid (n i : Nat) : validWord n (decodeWord n i) = true := by
  apply (validWord_iff n _).mpr
  induction n generalizing i with
  | zero => simp [decodeWord,Ternary]
  | succ n ih =>
    have h := ih (i/3)
    constructor
    · simp [decodeWord,h.1]
    · intro a ha
      have hm : a ∈ decodeWord n (i/3) ∨ a=i%3 := by simpa [decodeWord] using ha
      rcases hm with hm | rfl
      · exact h.2 a hm
      · exact Nat.mod_lt _ (by decide)

/-- The generic matrix law specialized only to a single downward generator. -/
theorem AtomicCoordinates.down_single_dense (A : AtomicCoordinates R)
    (s t : Signs) (step : Step)
    (h : [step].foldlM descendSigns t = some s) (x : R.Space s) (o : Word)
    (ho : validWord t.length o = true) :
    A.coord t (R.downMap s t [step] h x) o =
      total (List.finRange (3^s.length)) (fun i =>
        transitionCoefficient (transitions step) (decodeWord s.length i.val) o *
          A.coord s x (decodeWord s.length i.val)) := by
  rw [A.linear_coordinates (R.downMap s t [step] h)
    (R.down_intertwiner s t [step] h) x o ho]
  apply total_congr_mem
  intro i _
  rw [A.down_single_coordinates s t step h _ o (decoded_word_valid _ _) ho]

/-- The generic matrix law specialized only to a single upward generator. -/
theorem AtomicCoordinates.up_single_dense (A : AtomicCoordinates R)
    (s t : Signs) (step : Step)
    (h : [step].foldlM ascendSigns s = some t) (x : R.Space s) (o : Word)
    (ho : validWord t.length o = true) :
    A.coord t (R.upMap s t [step] h x) o =
      total (List.finRange (3^s.length)) (fun i =>
        transitionCoefficient (transitions step) (decodeWord s.length i.val) o *
          A.coord s x (decodeWord s.length i.val)) := by
  rw [A.linear_coordinates (R.upMap s t [step] h)
    (R.up_intertwiner s t [step] h) x o ho]
  apply total_congr_mem
  intro i _
  rw [A.up_single_coordinates s t step h _ o (decoded_word_valid _ _) ho]

theorem foldlM_cons_some {α β : Type} (f : α → β → Option α)
    (step : β) (steps : List β) (s t : α)
    (h : (step::steps).foldlM f s = some t) :
    ∃ mid, f s step = some mid ∧ steps.foldlM f mid = some t := by
  simp only [List.foldlM_cons] at h
  cases he : f s step with
  | none => simp [he] at h
  | some mid => exact ⟨mid,rfl,by simpa [he] using h⟩

theorem singleton_foldlM {α β : Type} (f : α → β → Option α)
    (step : β) (s t : α) (h : f s step = some t) :
    [step].foldlM f s = some t := by simp [List.foldlM_cons,h]

theorem expand_cons (step : Step) (steps : List Step) (x : Tensor) :
    expand (step::steps) x = applyStep (expand steps x) step := by
  simp [expand,WebMu.compose,List.reverse_cons,List.foldl_append]

theorem compose_cons (step : Step) (steps : List Step) (x : Tensor) :
    WebMu.compose (step::steps) x = WebMu.compose steps (applyStep x step) := rfl

/-- A sparse representation of a vector, on every valid standard coordinate. -/
def Represents (A : AtomicCoordinates R) (s : Signs) (x : R.Space s)
    (values : Tensor) : Prop :=
  ∀ w, validWord s.length w = true → A.coord s x w = ofList (values.getD w [])

theorem AtomicCoordinates.basis_represents (A : AtomicCoordinates R) (s : Signs)
    (u : Word) (hu : validWord s.length u = true) :
    Represents A s (A.basis s u) (singleton u) := by
  intro w hw
  rw [A.coord_basis s u w hu hw,singleton_poly]
  rfl

theorem AtomicCoordinates.down_single_represents (A : AtomicCoordinates R)
    (s t : Signs) (step : Step) (h : [step].foldlM descendSigns t = some s)
    (x : R.Space s) (values : Tensor) (hs : Supported s.length values)
    (hx : Represents A s x values) :
    Represents A t (R.downMap s t [step] h x) (applyStep values step) := by
  intro o ho
  rw [A.down_single_dense s t step h x o ho,applyStep_dense s.length values step o hs]
  apply total_congr_mem
  intro i _
  rw [hx _ (decoded_word_valid _ _)]

theorem AtomicCoordinates.up_single_represents (A : AtomicCoordinates R)
    (s t : Signs) (step : Step) (h : [step].foldlM ascendSigns s = some t)
    (x : R.Space s) (values : Tensor) (hs : Supported s.length values)
    (hx : Represents A s x values) :
    Represents A t (R.upMap s t [step] h x) (applyStep values step) := by
  intro o ho
  rw [A.up_single_dense s t step h x o ho,applyStep_dense s.length values step o hs]
  apply total_congr_mem
  intro i _
  rw [hx _ (decoded_word_valid _ _)]

/-- Arbitrary downward growth strings, with support and coordinate realization
proved together. The induction uses the atomic generator table at each step. -/
theorem AtomicCoordinates.down_represents (A : AtomicCoordinates R)
    (steps : List Step) (s t : Signs)
    (h : steps.foldlM descendSigns t = some s)
    (x : R.Space s) (values : Tensor) (hs : Supported s.length values)
    (hx : Represents A s x values) :
    Supported t.length (expand steps values) ∧
      Represents A t (R.downMap s t steps h x) (expand steps values) := by
  induction steps generalizing s t with
  | nil =>
    have he : t = s := by simpa using h
    subst t
    constructor
    · exact hs
    · simpa [A.down_nil] using hx
  | cons step steps ih =>
    obtain ⟨mid,hfirst,hrest⟩ := foldlM_cons_some descendSigns step steps t s h
    have hf := singleton_foldlM descendSigns step t mid hfirst
    obtain ⟨hst,hxt⟩ := ih s mid hrest x hs hx
    rw [expand_cons]
    constructor
    · exact descend_step_supported mid t step hfirst _ hst
    · rw [A.down_cons s t mid step steps h hf hrest]
      exact A.down_single_represents mid t step hf _ _ hst hxt

/-- Arbitrary upward growth strings, again including complete support. -/
theorem AtomicCoordinates.up_represents (A : AtomicCoordinates R)
    (steps : List Step) (s t : Signs)
    (h : steps.foldlM ascendSigns s = some t)
    (x : R.Space s) (values : Tensor) (hs : Supported s.length values)
    (hx : Represents A s x values) :
    Supported t.length (WebMu.compose steps values) ∧
      Represents A t (R.upMap s t steps h x) (WebMu.compose steps values) := by
  induction steps generalizing s t values with
  | nil =>
    have he : s = t := by simpa using h
    subst t
    constructor
    · exact hs
    · simpa [A.up_nil] using hx
  | cons step steps ih =>
    obtain ⟨mid,hfirst,hrest⟩ := foldlM_cons_some ascendSigns step steps s t h
    have hf := singleton_foldlM ascendSigns step s mid hfirst
    have hsfirst := ascend_step_supported s mid step hfirst values hs
    have hxfirst := A.up_single_represents s mid step hf x values hs hx
    rw [compose_cons,A.up_cons s t mid step steps h hf hrest]
    exact ih mid t hrest _ _ hsfirst hxfirst

theorem validWord_split (n k : Nat) (w : Word) (h : validWord (n+k) w = true) :
    validWord n (w.take n) = true ∧ validWord k (w.drop n) = true := by
  obtain ⟨hl,ht⟩ := (validWord_iff _ _).mp h
  constructor
  · apply (validWord_iff _ _).mpr
    constructor
    · simp [List.length_take,hl]
    · intro a ha
      exact ht a (List.mem_of_mem_take ha)
  · apply (validWord_iff _ _).mpr
    constructor
    · simp [List.length_drop,hl]
    · intro a ha
      exact ht a (List.mem_of_mem_drop ha)

theorem realization_eval_identity (s : Signs) (u w : Word) :
    ofList ((evalSparse (.identity s) u).getD w []) = if u=w then 1 else 0 := by
  exact singleton_poly u w Laurent.one

theorem realization_eval_add {s t : Signs} (f g : Circuit s t) (u w : Word) :
    ofList ((evalSparse (.add f g) u).getD w []) =
      ofList ((evalSparse f u).getD w []) + ofList ((evalSparse g u).getD w []) := by
  change ofList ((sumMap [evalSparse f u,evalSparse g u]).getD w []) = _
  simp [sumMap_poly]

theorem realization_eval_neg {s t : Signs} (f : Circuit s t) (u w : Word) :
    ofList ((evalSparse (.neg f) u).getD w []) =
      ofList ((evalSparse f u).getD w []) * ofList (Laurent.monomial 0 (-1)) :=
  evalSparse_neg_coefficient f u w

theorem realization_eval_scaleD {s t : Signs} (f : Circuit s t) (u w : Word) :
    ofList ((evalSparse (.scaleD f) u).getD w []) =
      ofList ((evalSparse f u).getD w []) * ofList d :=
  evalSparse_scaleD_coefficient f u w

theorem realization_eval_zero (s t : Signs) (u w : Word) :
    ofList ((evalSparse (.zero s t) u).getD w []) = 0 := by
  simp [evalSparse]

theorem supported_zero_of_invalid (hx : Supported n x) (w : Word)
    (hw : validWord n w ≠ true) : ofList (x.getD w []) = 0 := by
  by_cases h : ofList (x.getD w []) = 0
  · exact h
  · exact False.elim (hw (hx w h))

/-- Every typed circuit's executable matrix is its actual standard-basis matrix.
The statement also proves complete output support, so each finite contraction
in the induction genuinely sums over every possible intermediate state. -/
theorem AtomicCoordinates.circuit_matrix (A : AtomicCoordinates R)
    {s t : Signs} (f : Circuit s t) (a : Word) (ha : validWord s.length a = true) :
    Supported t.length (evalSparse f a) ∧
      ∀ o, validWord t.length o = true →
        A.coord t (R.interpret f (A.basis s a)) o =
          ofList ((evalSparse f a).getD o []) := by
  induction f generalizing a with
  | identity s =>
    refine ⟨singleton_supported s.length a Laurent.one ha,?_⟩
    intro o ho
    exact (A.coord_basis s a o ha ho).trans (realization_eval_identity s a o).symm
  | down s t steps valid =>
    exact A.down_represents steps s t valid (A.basis s a) (singleton a)
      (singleton_supported s.length a Laurent.one ha) (A.basis_represents s a ha)
  | up s t steps valid =>
    exact A.up_represents steps s t valid (A.basis s a) (singleton a)
      (singleton_supported s.length a Laurent.one ha) (A.basis_represents s a ha)
  | @compose r s t f g ihf ihg =>
    obtain ⟨hsf,hcf⟩ := ihf a ha
    constructor
    · exact bindSparse_supported_input s.length t.length (evalSparse f a) (evalSparse g)
        hsf (fun u hu => (ihg u hu).1)
    · intro o ho
      change A.coord t (R.interpret g (R.interpret f (A.basis r a))) o = _
      rw [A.linear_coordinates (R.interpret g) (circuit_intertwiner R g) _ o ho]
      change _ = ofList ((bindSparse (evalSparse f a) (evalSparse g)).getD o [])
      rw [bindSparse_dense s.length _ _ o hsf]
      apply total_congr_mem
      intro i _
      rw [(ihg _ (decoded_word_valid _ _)).2 o ho,hcf _ (decoded_word_valid _ _)]
  | @tensor r s t u f g ihf ihg =>
    have hai : validWord (r.length+t.length) a = true := by simpa using ha
    obtain ⟨hal,har⟩ := validWord_split r.length t.length a hai
    obtain ⟨hsf,hcf⟩ := ihf (a.take r.length) hal
    obtain ⟨hsg,hcg⟩ := ihg (a.drop r.length) har
    constructor
    · simpa only [List.length_append] using tensorProduct_supported s.length u.length
        (evalSparse f (a.take r.length)) (evalSparse g (a.drop r.length)) hsf hsg
    · intro o ho
      have hoi : validWord (s.length+u.length) o = true := by simpa using ho
      obtain ⟨hol,hor⟩ := validWord_split s.length u.length o hoi
      have hc := A.tensor_basis (R.interpret f) (R.interpret g)
        (circuit_intertwiner R f) (circuit_intertwiner R g)
        (a.take r.length) (a.drop r.length) (o.take s.length) (o.drop s.length)
        hal har hol hor
      simp only [List.take_append_drop] at hc
      change A.coord (s++u) (R.tensorMap (R.interpret f) (R.interpret g)
        (A.basis (r++t) a)) o = _
      rw [hc,hcf _ hol,hcg _ hor]
      change _ = ofList ((tensorProduct (evalSparse f (a.take r.length))
        (evalSparse g (a.drop r.length))).getD o [])
      have he := tensorProduct_split s.length
        (evalSparse f (a.take r.length)) (evalSparse g (a.drop r.length))
        (o.take s.length) (o.drop s.length) hsf ((validWord_iff _ _).mp hol).1
      simpa only [List.take_append_drop] using he.symm
  | @add s t f g ihf ihg =>
    obtain ⟨hsf,hcf⟩ := ihf a ha
    obtain ⟨hsg,hcg⟩ := ihg a ha
    constructor
    · intro o hn
      by_cases ho : validWord t.length o = true
      · exact ho
      · apply False.elim
        apply hn
        rw [realization_eval_add,supported_zero_of_invalid hsf o ho,
          supported_zero_of_invalid hsg o ho]
        exact poly_add_zero 0
    · intro o ho
      change A.coord t (R.add t (R.interpret f (A.basis s a))
        (R.interpret g (A.basis s a))) o = _
      rw [A.coord_add,hcf o ho,hcg o ho,realization_eval_add]
  | @neg s t f ih =>
    obtain ⟨hs,hc⟩ := ih a ha
    constructor
    · intro o hn
      by_cases ho : validWord t.length o = true
      · exact ho
      · apply False.elim
        apply hn
        rw [realization_eval_neg,supported_zero_of_invalid hs o ho,poly_zero_mul]
    · intro o ho
      change A.coord t (R.neg t (R.interpret f (A.basis s a))) o = _
      rw [A.coord_neg,hc o ho,realization_eval_neg]
  | @scaleD s t f ih =>
    obtain ⟨hs,hc⟩ := ih a ha
    constructor
    · intro o hn
      by_cases ho : validWord t.length o = true
      · exact ho
      · apply False.elim
        apply hn
        rw [realization_eval_scaleD,supported_zero_of_invalid hs o ho,poly_zero_mul]
    · intro o ho
      change A.coord t (R.scaleD t (R.interpret f (A.basis s a))) o = _
      rw [A.coord_scaleD,hc o ho,realization_eval_scaleD]
  | zero s t =>
    constructor
    · intro o hn
      exact False.elim (hn (realization_eval_zero s t a o))
    · intro o _
      exact (A.coord_zero t o).trans (realization_eval_zero s t a o).symm

/-- Action on an arbitrary tensor, derived from the proved basis matrix. -/
theorem AtomicCoordinates.circuit_action (A : AtomicCoordinates R)
    {s t : Signs} (f : Circuit s t) (x : R.Space s) (o : Word)
    (ho : validWord t.length o = true) :
    A.coord t (R.interpret f x) o =
      total (List.finRange (3^s.length)) (fun i =>
        ofList ((evalSparse f (decodeWord s.length i.val)).getD o []) *
          A.coord s x (decodeWord s.length i.val)) := by
  rw [A.linear_coordinates (R.interpret f) (circuit_intertwiner R f) x o ho]
  apply total_congr_mem
  intro i _
  rw [(A.circuit_matrix f _ (decoded_word_valid _ _)).2 o ho]

/-- In particular, the closed-circuit evaluator realizes the actual invariant. -/
theorem AtomicCoordinates.closed_circuit (A : AtomicCoordinates R)
    {s : Signs} (f : Circuit [] s) (w : Word)
    (hw : validWord s.length w = true) :
    A.coord s (R.interpret f R.vacuum) w = ofList ((evalSparse f []).getD w []) := by
  have h := (A.circuit_matrix f [] (by decide)).2 w hw
  simpa only [A.basis_vacuum] using h

/-- The former whole-program correctness interface is now constructed by proof.
Its equations are conclusions of `circuit_matrix`, not new reference inputs. -/
def AtomicCoordinates.toCoordinateReferences (A : AtomicCoordinates R) : CoordinateReferences R where
  coord := A.coord
  coord_add := A.coord_add
  closed_coordinates := A.closed_circuit
  tensor_identity_coordinates := by
    intro s t f r x o w ho hw
    change A.coord (t++r) (R.tensorMap (R.interpret f) (id : R.Space r → R.Space r) x) (o++w) = _
    rw [A.tensor_identity_coordinates (R.interpret f) (circuit_intertwiner R f) r x o w ho hw]
    apply total_congr_mem
    intro i _
    rw [(A.circuit_matrix f _ (decoded_word_valid _ _)).2 o ho]
  tensorBar := A.tensorBar
  boundary_coordinates := A.boundary_coordinates

#print axioms AtomicCoordinates.circuit_matrix
#print axioms AtomicCoordinates.toCoordinateReferences

end WebMu.Revised.Bar
