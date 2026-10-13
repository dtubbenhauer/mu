import WebMu.Revised.BarCoordinates
import WebMu.Revised.GrowthBridge
import WebMu.Revised.CircuitSparseSemantics
import WebMu.Revised.GrowthPairing
import WebMu.Revised.HPrimitiveCoordinates

/-!
Atomic coordinate inputs for the ordinary signed tensor representations.

No field states correctness of `evalSparse`, a whole `Circuit`, or a multi-step
growth evaluator. The coordinate fields are the ordinary rules for a finite
standard basis, arbitrary linear intertwiners, and tensor products. The only
web-coordinate inputs concern a SINGLE primitive vertex or evaluation/coevaluation
edge, with its literal local table and identity strands. H is defined by its
two vertices; its nine-entry table is proved, not a reference input. The down/up list rules express composition
in the spider functor; they make no claim about the executable evaluator.

The tables are those of Khovanov--Kuperberg, Sections 2 and 4. The independent
`CircuitRealization` proof derives the formerly assumed whole-circuit rules.
`R.Space s` is instantiated by the integral Laurent tensor lattice, whose
coordinates lie in Z[v,v^-1], not by its unrestricted rational-function
scalar extension. All elementary maps and the tensor bar preserve this lattice.
-/
namespace WebMu.Revised.Bar
open Algebra GrowthBridge GrowthPairing GrowthAdjoint M2Flow GrowthPrimitiveRealization

structure AtomicCoordinates (R : BarReferences) where
  coord : (s : Signs) → R.Space s → Word → Poly
  basis : (s : Signs) → Word → R.Space s
  realize : (s : Signs) → (Word → Poly) → R.Space s
  coord_basis : ∀ s u w,
    validWord s.length u = true → validWord s.length w = true →
    coord s (basis s u) w = if u = w then 1 else 0
  coord_realize : ∀ s f w, validWord s.length w = true →
    coord s (realize s f) w = f w
  coord_ext : ∀ s (x y : R.Space s),
    (∀ w, validWord s.length w = true → coord s x w = coord s y w) → x = y
  basis_vacuum : basis [] [] = R.vacuum
  coord_add : ∀ s x y w, coord s (R.add s x y) w = coord s x w + coord s y w
  coord_neg : ∀ s x w, coord s (R.neg s x) w =
    coord s x w * ofList (Laurent.monomial 0 (-1))
  coord_scaleD : ∀ s x w, coord s (R.scaleD s x) w = coord s x w * ofList d
  coord_zero : ∀ s w, coord s (R.zero s) w = 0
  /-- Ordinary matrix multiplication for an arbitrary linear intertwiner. -/
  linear_basis_coordinates : ∀ {s t} (f : R.Space s → R.Space t),
    R.IsIntertwiner f → ∀ (ws : List Word), ws.Nodup →
    (∀ w, w ∈ ws ↔ validWord s.length w = true) →
    ∀ x o, validWord t.length o = true →
    coord t (f x) o = total ws (fun w =>
      coord t (f (basis s w)) o * coord s x w)
  /-- The ordinary tensor product of arbitrary linear maps on basis tensors. -/
  tensor_basis : ∀ {r s t u} (f : R.Space r → R.Space s) (g : R.Space t → R.Space u),
    R.IsIntertwiner f → R.IsIntertwiner g → ∀ a b c e,
    validWord r.length a = true → validWord t.length b = true →
    validWord s.length c = true → validWord u.length e = true →
    coord (s++u) (R.tensorMap f g (basis (r++t) (a++b))) (c++e) =
      coord s (f (basis r a)) c * coord u (g (basis t b)) e
  /-- Partial matrix multiplication, with arbitrary identity spectators.
  This is a generic linear-algebra law; f need not be a project circuit. -/
  tensor_identity_basis_coordinates : ∀ {s t} (f : R.Space s → R.Space t),
    R.IsIntertwiner f → ∀ (ws : List Word), ws.Nodup →
    (∀ w, w ∈ ws ↔ validWord s.length w = true) →
    ∀ (r : Signs) (x : R.Space (s++r)) o w,
    validWord t.length o = true → validWord r.length w = true →
    coord (t++r) (R.tensorMap f (id : R.Space r → R.Space r) x) (o++w) =
      total ws (fun a => coord t (f (basis s a)) o * coord (s++r) x (a++w))
  down_nil : ∀ s (h : ([] : List Step).foldlM descendSigns s = some s) x,
    R.downMap s s [] h x = x
  up_nil : ∀ s (h : ([] : List Step).foldlM ascendSigns s = some s) x,
    R.upMap s s [] h x = x
  /-- A downward string is interpreted in reversed composition order. -/
  down_cons : ∀ s t mid step steps
    (h : (step::steps).foldlM descendSigns t = some s)
    (hfirst : [step].foldlM descendSigns t = some mid)
    (hrest : steps.foldlM descendSigns mid = some s) x,
    R.downMap s t (step::steps) h x =
      R.downMap mid t [step] hfirst (R.downMap s mid steps hrest x)
  /-- Upward strings are interpreted in their listed composition order. -/
  up_cons : ∀ s t mid step steps
    (h : (step::steps).foldlM ascendSigns s = some t)
    (hfirst : [step].foldlM ascendSigns s = some mid)
    (hrest : steps.foldlM ascendSigns mid = some t) x,
    R.upMap s t (step::steps) h x =
      R.upMap mid t steps hrest (R.upMap s mid [step] hfirst x)
  /-- Primitive tables exclude the two-vertex H macro. -/
  down_single_table : ∀ s t step (primitive : step.1 ≠ Op.h)
    (h : [step].foldlM descendSigns t = some s) a o,
    validWord s.length a = true → validWord t.length o = true →
    coord t (R.downMap s t [step] h (basis s a)) o =
      if contextCondition step.2 (arity step.1) (upperArity step.1) a o then
        transitionCoefficient (localTerms step.1)
          ((a.drop step.2).take (arity step.1))
          ((o.drop step.2).take (upperArity step.1)) else 0
  up_single_table : ∀ s t step (primitive : step.1 ≠ Op.h)
    (h : [step].foldlM ascendSigns s = some t) a o,
    validWord s.length a = true → validWord t.length o = true →
    coord t (R.upMap s t [step] h (basis s a)) o =
      if contextCondition step.2 (arity step.1) (upperArity step.1) a o then
        transitionCoefficient (localTerms step.1)
          ((a.drop step.2).take (arity step.1))
          ((o.drop step.2).take (upperArity step.1)) else 0

  /-- The defining two vertices of the local H web: first Y at i, then
  lambda at i+1. This is literal single-web composition, with arbitrary
  identity spectators; no coordinate table or growth program is assumed. -/
  down_h_definition : ∀ s mid t i
    (hh : [(.h,i)].foldlM descendSigns t=some s)
    (hy : [(.y,i)].foldlM ascendSigns s=some mid)
    (hl : [(.lam,i+1)].foldlM ascendSigns mid=some t) x,
    R.downMap s t [(.h,i)] hh x =
      R.upMap mid t [(.lam,i+1)] hl (R.upMap s mid [(.y,i)] hy x)
  up_h_definition : ∀ s mid t i
    (hh : [(.h,i)].foldlM ascendSigns s=some t)
    (hy : [(.y,i)].foldlM ascendSigns s=some mid)
    (hl : [(.lam,i+1)].foldlM ascendSigns mid=some t) x,
    R.upMap s t [(.h,i)] hh x =
      R.upMap mid t [(.lam,i+1)] hl (R.upMap s mid [(.y,i)] hy x)

/-- The executable placement of one generator agrees with its tensor-coordinate
formula: the local table, and Kronecker deltas on all unchanged strands. -/
theorem single_step_coordinate_table (step : Step) (a o : Word) :
    transitionCoefficient (transitions step) a o =
      if contextCondition step.2 (arity step.1) (upperArity step.1) a o then
        transitionCoefficient (localTerms step.1)
          ((a.drop step.2).take (arity step.1))
          ((o.drop step.2).take (upperArity step.1)) else 0 := by
  rcases step with ⟨op,i⟩
  exact contextCoefficient i (arity op) (upperArity op) (localTerms op)
    (fun w term h => (localTerms_lengths op w term h).2) a o

theorem AtomicCoordinates.down_primitive_coordinates (A : AtomicCoordinates R)
    (s t : Signs) (step : Step) (hp : step.1 ≠ Op.h)
    (h : [step].foldlM descendSigns t = some s)
    (a o : Word) (ha : validWord s.length a = true) (ho : validWord t.length o = true) :
    A.coord t (R.downMap s t [step] h (A.basis s a)) o =
      transitionCoefficient (transitions step) a o := by
  rw [A.down_single_table s t step hp h a o ha ho,single_step_coordinate_table]

theorem AtomicCoordinates.up_primitive_coordinates (A : AtomicCoordinates R)
    (s t : Signs) (step : Step) (hp : step.1 ≠ Op.h)
    (h : [step].foldlM ascendSigns s = some t)
    (a o : Word) (ha : validWord s.length a = true) (ho : validWord t.length o = true) :
    A.coord t (R.upMap s t [step] h (A.basis s a)) o =
      transitionCoefficient (transitions step) a o := by
  rw [A.up_single_table s t step hp h a o ha ho,single_step_coordinate_table]

/-- The H table is derived from its two primitive vertex tables. The finite
nine local cases are expanded to arbitrary ordered identity spectators. -/
theorem AtomicCoordinates.h_composite_coordinates (A : AtomicCoordinates R)
    (s mid t : Signs) (i : Nat)
    (hy : [(.y,i)].foldlM ascendSigns s=some mid)
    (hl : [(.lam,i+1)].foldlM ascendSigns mid=some t)
    (hb : i+2≤s.length) (u o : Word)
    (hu : validWord s.length u=true) (ho : validWord t.length o=true) :
    A.coord t (R.upMap mid t [(.lam,i+1)] hl
      (R.upMap s mid [(.y,i)] hy (A.basis s u))) o =
      transitionCoefficient (transitions (.h,i)) u o := by
  rw [A.linear_basis_coordinates _ (R.up_intertwiner mid t [(.lam,i+1)] hl)
    (completeWords mid.length) (completeWords_nodup _) (completeWords_mem _) _ o ho]
  have hs : ∀ term, term ∈ transitions (.y,i) u → validWord mid.length term.1=true := by
    intro term ht
    have hv := transitions_valid s.length u (.y,i) term hu ht
    have hn := ascendSigns_length s mid (.y,i) ((singleton_foldlM_iff _ _ _ _).mp hy)
    rw [hn] at hv
    exact hv
  have hm : total (completeWords mid.length) (fun w =>
      A.coord t (R.upMap mid t [(.lam,i+1)] hl (A.basis mid w)) o *
      A.coord mid (R.upMap s mid [(.y,i)] hy (A.basis s u)) w) =
    total (completeWords mid.length) (fun w =>
      transitionCoefficient (transitions (.lam,i+1)) w o *
      transitionCoefficient (transitions (.y,i)) u w) := by
    apply total_congr_mem
    intro w hw
    have hw' := (completeWords_mem _ _).mp hw
    rw [A.up_primitive_coordinates mid t (.lam,i+1) (by simp) hl w o hw' ho,
      A.up_primitive_coordinates s mid (.y,i) (by simp) hy u w hu hw']
  rw [hm,total_transition mid.length (transitions (.y,i)) u hs,← twiceTerms_coefficient]
  unfold transitionCoefficient
  rw [h_paths i u ((Revised.validWord_iff _ _).mp hu).2 (by
    have hh := ((Revised.validWord_iff _ _).mp hu).1
    omega)]

theorem AtomicCoordinates.down_single_coordinates (A : AtomicCoordinates R)
    (s t : Signs) (step : Step) (h : [step].foldlM descendSigns t = some s)
    (a o : Word) (ha : validWord s.length a = true) (ho : validWord t.length o = true) :
    A.coord t (R.downMap s t [step] h (A.basis s a)) o =
      transitionCoefficient (transitions step) a o := by
  by_cases hp : step.1=Op.h
  · rcases step with ⟨op,i⟩
    dsimp only at hp
    subst op
    obtain ⟨mid,hy,hl,hb⟩ := down_h_typing s t i h
    rw [A.down_h_definition s mid t i h hy hl]
    exact A.h_composite_coordinates s mid t i hy hl hb a o ha ho
  · exact A.down_primitive_coordinates s t step hp h a o ha ho

theorem AtomicCoordinates.up_single_coordinates (A : AtomicCoordinates R)
    (s t : Signs) (step : Step) (h : [step].foldlM ascendSigns s = some t)
    (a o : Word) (ha : validWord s.length a = true) (ho : validWord t.length o = true) :
    A.coord t (R.upMap s t [step] h (A.basis s a)) o =
      transitionCoefficient (transitions step) a o := by
  by_cases hp : step.1=Op.h
  · rcases step with ⟨op,i⟩
    dsimp only at hp
    subst op
    obtain ⟨mid,hy,hl,hb⟩ := up_h_typing s t i h
    rw [A.up_h_definition s mid t i h hy hl]
    exact A.h_composite_coordinates s mid t i hy hl hb a o ha ho
  · exact A.up_primitive_coordinates s t step hp h a o ha ho

/-- The executable base-three enumeration is used only AFTER its completeness
and lack of repetitions have been proved, not in a reference assumption. -/
theorem AtomicCoordinates.linear_coordinates (A : AtomicCoordinates R)
    {s t : Signs} (f : R.Space s → R.Space t) (hf : R.IsIntertwiner f)
    (x : R.Space s) (o : Word) (ho : validWord t.length o = true) :
    A.coord t (f x) o = total (List.finRange (3^s.length)) (fun i =>
      A.coord t (f (A.basis s (decodeWord s.length i.val))) o *
      A.coord s x (decodeWord s.length i.val)) := by
  rw [A.linear_basis_coordinates f hf (completeWords s.length)
    (completeWords_nodup _) (completeWords_mem _) x o ho]
  exact total_map _ _ _

theorem AtomicCoordinates.tensor_identity_coordinates (A : AtomicCoordinates R)
    {s t : Signs} (f : R.Space s → R.Space t) (hf : R.IsIntertwiner f)
    (r : Signs) (x : R.Space (s++r)) (o w : Word)
    (ho : validWord t.length o = true) (hw : validWord r.length w = true) :
    A.coord (t++r) (R.tensorMap f (id : R.Space r → R.Space r) x) (o++w) =
      total (List.finRange (3^s.length)) (fun i =>
        A.coord t (f (A.basis s (decodeWord s.length i.val))) o *
          A.coord (s++r) x (decodeWord s.length i.val ++ w)) := by
  rw [A.tensor_identity_basis_coordinates f hf (completeWords s.length)
    (completeWords_nodup _) (completeWords_mem _) r x o w ho hw]
  exact total_map _ _ _

end WebMu.Revised.Bar
