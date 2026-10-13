import WebMu.Revised.CircuitRealization

/-! Signed tensor weights and their conservation by the elementary spider
maps. The proof is uniform in spectators, words and circuit length. -/
namespace WebMu.Revised.WeightConservation
open Laurent Algebra Bar GrowthBridge GrowthPrimitiveRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev Weight := Int × Int

def plus (a b : Weight) : Weight := (a.1+b.1,a.2+b.2)
def letterWeight (s : Bool) (a : Nat) : Weight :=
  if s then match a with | 0 => (1,0) | 1 => (-1,1) | _ => (0,-1)
  else match a with | 0 => (0,1) | 1 => (1,-1) | _ => (-1,0)
def weight : Signs → Word → Weight
  | s::ss,a::as => plus (letterWeight s a) (weight ss as)
  | _,_ => (0,0)

theorem plus_assoc (a b c : Weight) : plus (plus a b) c=plus a (plus b c) := by
  apply Prod.ext <;> simp only [plus] <;> omega

theorem weight_append (s t : Signs) (u v : Word) (h : s.length=u.length) :
    weight (s++t) (u++v)=plus (weight s u) (weight t v) := by
  induction s generalizing u with
  | nil => cases u <;> simp_all [weight,plus]
  | cons a s ih =>
    cases u with
    | nil => simp at h
    | cons b u =>
      simp only [List.cons_append,weight]
      rw [ih u (by simpa using h),plus_assoc]

inductive LocalType : Op → Signs → Signs → Prop where
  | y (s : Bool) : LocalType .y [s] [!s,!s]
  | cup (s : Bool) : LocalType .cup [] [s,!s]
  | lam (s : Bool) : LocalType .lam [s,s] [!s]
  | sigma (s : Bool) : LocalType .sigma [s,!s] []
  | h (s : Bool) : LocalType .h [s,!s] [!s,s]

/-- Only the primitive tables are enumerated; arbitrary contexts are handled
by the following structural theorems. -/
theorem local_weight {op : Op} {s t : Signs} (ht : LocalType op s t)
    (u : Word) (hu : validWord s.length u=true) (z : Word × Laurent)
    (hz : z ∈ localTerms op u) : weight s u=weight t z.1 := by
  cases ht with
  | y s =>
    obtain ⟨hl,ha⟩ := (validWord_iff _ _).mp hu
    obtain ⟨a,rfl⟩ : ∃ a, u=[a] := by cases u with | nil => simp at hl | cons a u => cases u <;> simp_all
    have h : a=0 ∨ a=1 ∨ a=2 := by have := ha a (by simp); omega
    rcases h with rfl|rfl|rfl <;> cases s <;>
      simp [localTerms] at hz <;> rcases hz with rfl|rfl <;> rfl
  | cup s =>
    have hl := ((validWord_iff _ _).mp hu).1
    have he : u=[] := List.eq_nil_of_length_eq_zero hl
    subst u
    cases s <;> simp [localTerms] at hz <;> rcases hz with rfl|rfl|rfl <;> rfl
  | lam s | sigma s | h s =>
    obtain ⟨hl,ha⟩ := (validWord_iff _ _).mp hu
    obtain ⟨a,b,rfl⟩ : ∃ a b, u=[a,b] := by
      cases u with
      | nil => simp at hl
      | cons a u => cases u with
        | nil => simp at hl
        | cons b u => cases u <;> simp_all
    have h₁ : a=0 ∨ a=1 ∨ a=2 := by have := ha a (by simp); omega
    have h₂ : b=0 ∨ b=1 ∨ b=2 := by have := ha b (by simp); omega
    rcases h₁ with rfl|rfl|rfl <;> rcases h₂ with rfl|rfl|rfl <;> cases s <;>
      simp [localTerms] at hz <;> (first | (rcases hz with rfl | rfl <;> decide) | (subst z; decide))

/-- An elementary map with arbitrary unchanged prefix and suffix strands. -/
inductive StepType : Signs → Step → Signs → Prop where
  | base {op s t} (ht : LocalType op s t) (r : Signs) : StepType (s++r) (op,0) (t++r)
  | spectator {s t op i} (a : Bool) : StepType s (op,i) t → StepType (a::s) (op,i+1) (a::t)

theorem local_arity {op s t} (h : LocalType op s t) : s.length=arity op := by cases h <;> rfl

theorem transitions_cons (op : Op) (i a : Nat) (u : Word) :
    transitions (op,i+1) (a::u)=(transitions (op,i) u).map (fun z => (a::z.1,z.2)) := by
  simp only [transitions,List.length_cons]
  have hi : i+1+arity op=(i+arity op)+1 := by omega
  rw [hi]
  by_cases hb : i+arity op≤u.length
  · simp [hb,List.map_map,Function.comp_def]
  · simp [hb]

theorem step_weight {s t step} (ht : StepType s step t) (u : Word)
    (hu : validWord s.length u=true) (z : Word × Laurent)
    (hz : z ∈ transitions step u) : weight s u=weight t z.1 := by
  induction ht generalizing u z with
  | @base op s t ht r =>
    have hs := local_arity ht
    have hu' := validWord_split s.length r.length u (by simpa using hu)
    have he : u=u.take s.length++u.drop s.length := (List.take_append_drop _ _).symm
    have hh := transitions_framed op [] (u.take s.length) (u.drop s.length)
      (((validWord_iff _ _).mp hu'.1).1.trans hs)
    simp only [List.length_nil,List.nil_append] at hh
    rw [← he] at hh
    rw [hh] at hz
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp hz
    cases heq
    have hvl := ((validWord_iff _ _).mp (localTerms_valid op _ v hv)).1
    have htlen : t.length=v.1.length := by
      have hh : t.length=M2Flow.upperArity op := by cases ht <;> rfl
      omega
    calc
      weight (s++r) u=weight (s++r) (u.take s.length++u.drop s.length) := congrArg (weight (s++r)) he
      _ = plus (weight s (u.take s.length)) (weight r (u.drop s.length)) :=
        weight_append s r _ _ ((validWord_iff _ _).mp hu'.1).1.symm
      _ = plus (weight t v.1) (weight r (u.drop s.length)) := by rw [local_weight ht _ hu'.1 v hv]
      _ = weight (t++r) (v.1++u.drop s.length) := (weight_append t r _ _ htlen).symm
  | @spectator s t op i a ht ih =>
    cases u with
    | nil => simp [validWord] at hu
    | cons b u =>
      rw [transitions_cons] at hz
      obtain ⟨v,hv,he⟩ := List.mem_map.mp hz
      cases he
      have hu' : validWord s.length u=true := by
        obtain ⟨hl,ha⟩ := (validWord_iff _ _).mp hu
        exact (validWord_iff _ _).mpr ⟨by simpa using hl,fun a h => ha a (by simp [h])⟩
      simp only [weight,ih u hu' v hv]

/-- The executable signed typing predicates produce these local rules. -/
theorem ascend_typed (s t : Signs) (op : Op) (i : Nat)
    (h : ascendSigns s (op,i)=some t) : StepType s (op,i) t := by
  induction i generalizing s t with
  | zero =>
    cases op with
    | cup => simp [ascendSigns] at h
    | y =>
      cases s with
      | nil => simp [ascendSigns] at h
      | cons a s =>
        have he : t=[!a,!a]++s := by simpa [ascendSigns] using h.symm
        subst t
        exact .base (.y a) s
    | lam | sigma | h =>
      cases s with
      | nil => simp [ascendSigns] at h
      | cons a s => cases s with
        | nil => simp [ascendSigns] at h
        | cons b s =>
          cases a <;> cases b <;> simp [ascendSigns] at h
          all_goals subst t
          all_goals first | exact .base (.lam _) s | exact .base (.sigma _) s | exact .base (.h _) s
  | succ i ih =>
    cases s with
    | nil => cases op <;> simp [ascendSigns] at h
    | cons a s =>
      rw [ascend_cons] at h
      cases hs : ascendSigns s (op,i) with
      | none => simp [hs] at h
      | some t' =>
        have he : t=a::t' := by simpa [hs] using h.symm
        subst t
        exact .spectator a (ih s t' hs)

theorem descend_typed (s t : Signs) (op : Op) (i : Nat)
    (h : descendSigns t (op,i)=some s) : StepType s (op,i) t := by
  induction i generalizing s t with
  | zero =>
    cases t with
    | nil => simp [descendSigns] at h
    | cons a t => cases t with
      | nil => simp [descendSigns] at h
      | cons b t =>
        cases op <;> cases a <;> cases b <;> simp [descendSigns] at h
        all_goals subst s
        all_goals first | exact .base (.y _) t | exact .base (.cup _) t | exact .base (.h _) t
  | succ i ih =>
    cases t with
    | nil => simp [descendSigns] at h
    | cons a t =>
      rw [descend_cons] at h
      cases ht : descendSigns t (op,i) with
      | none => simp [ht] at h
      | some s' =>
        have he : s=a::s' := by simpa [ht] using h.symm
        subst s
        exact .spectator a (ih s' t ht)

/-- A Laurent tensor supported in one signed weight space. -/
def PureWeight (s : Signs) (q : Weight) (x : Tensor) : Prop :=
  Supported s.length x ∧ ∀ w, weight s w≠q → ofList (x.getD w [])=0

theorem singleton_weight (s : Signs) (u : Word) (hu : validWord s.length u=true) :
    PureWeight s (weight s u) (singleton u) := by
  refine ⟨singleton_supported _ _ one hu,?_⟩
  intro w hw
  rw [singleton_poly]
  exact if_neg (by intro he; subst w; exact hw rfl)

theorem transition_weight_zero {s t step} (ht : StepType s step t) (u w : Word)
    (hu : validWord s.length u=true) (hw : weight t w≠weight s u) :
    transitionCoefficient (transitions step) u w=0 := by
  apply total_eq_zero_of_each
  intro z hz
  have he : z.1≠w := by
    intro he
    exact hw (he ▸ (step_weight ht u hu z hz).symm)
  simp [he]

theorem step_pure {s t step} (ht : StepType s step t)
    (hsp : ∀ x, Supported s.length x → Supported t.length (applyStep x step))
    (q : Weight) (x : Tensor) (hx : PureWeight s q x) : PureWeight t q (applyStep x step) := by
  refine ⟨hsp x hx.1,?_⟩
  intro w hw
  rw [applyStep_dense s.length x step w hx.1]
  apply total_eq_zero_of_each
  intro i _
  by_cases hi : weight s (decodeWord s.length i.val)=q
  · rw [transition_weight_zero ht _ w (decode_valid _ _) (by simpa only [hi] using hw),poly_zero_mul]
  · rw [hx.2 _ hi,poly_mul_zero]

theorem up_pure (ss : List Step) (s t : Signs) (ht : ss.foldlM ascendSigns s=some t)
    (q : Weight) (x : Tensor) (hx : PureWeight s q x) : PureWeight t q (compose ss x) := by
  induction ss generalizing s t x with
  | nil =>
    have he : s=t := by simpa using ht
    subst t
    exact hx
  | cons st ss ih =>
    obtain ⟨mid,hfirst,hrest⟩ := foldlM_cons_some ascendSigns st ss s t ht
    rw [compose_cons]
    exact ih mid t hrest _ (step_pure (ascend_typed s mid st.1 st.2 hfirst)
      (fun x h => ascend_step_supported s mid st hfirst x h) q x hx)

theorem down_pure (ss : List Step) (s t : Signs) (ht : ss.foldlM descendSigns t=some s)
    (q : Weight) (x : Tensor) (hx : PureWeight s q x) : PureWeight t q (expand ss x) := by
  induction ss generalizing s t with
  | nil =>
    have he : t=s := by simpa using ht
    subst t
    exact hx
  | cons st ss ih =>
    obtain ⟨mid,hfirst,hrest⟩ := foldlM_cons_some descendSigns st ss t s ht
    rw [expand_cons]
    exact step_pure (descend_typed mid t st.1 st.2 hfirst)
      (fun x h => descend_step_supported mid t st hfirst x h) q _ (ih s mid hrest hx)

/-- Every typed circuit preserves the weight of each basis input.  The
induction uses primitive weight conservation, finite linearity and tensor
products. AtomicCoordinates is used for the already proved support theorem;
no weight assertion is an input field. -/
theorem circuit_weight_zero (R : BarReferences) (A : AtomicCoordinates R)
    {s t : Signs} (f : Circuit s t) (u : Word) (hu : validWord s.length u=true)
    (w : Word) (hw : weight t w≠weight s u) : ofList ((evalSparse f u).getD w [])=0 := by
  induction f generalizing u w with
  | identity s => exact (singleton_weight s u hu).2 w hw
  | down s t ss ht => exact (down_pure ss s t ht _ _ (singleton_weight s u hu)).2 w hw
  | up s t ss ht => exact (up_pure ss s t ht _ _ (singleton_weight s u hu)).2 w hw
  | @compose r s t f g ihf ihg =>
    change ofList ((bindSparse (evalSparse f u) (evalSparse g)).getD w [])=0
    rw [bindSparse_poly]
    apply total_eq_zero_of_each
    rintro ⟨v,p⟩ hp
    dsimp only
    by_cases hz : ofList p=0
    · rw [hz,poly_mul_zero]
    · have hv : validWord s.length v=true := (A.circuit_matrix f u hu).1 v
        (by rw [entry_lookup _ _ _ hp]; exact hz)
      have hwt : weight s v=weight r u := by
        by_cases he : weight s v=weight r u
        · exact he
        · have h := ihf u hu v he
          rw [entry_lookup _ _ _ hp] at h
          contradiction
      rw [ihg v hv w (by simpa only [hwt] using hw),poly_zero_mul]
  | @tensor r s t v f g ihf ihg =>
    have hu' := validWord_split r.length t.length u (by simpa using hu)
    change ofList ((tensorProduct (evalSparse f (u.take r.length))
      (evalSparse g (u.drop r.length))).getD w [])=0
    rw [tensorProduct_poly]
    apply total_eq_zero_of_each
    rintro ⟨a,p⟩ hp
    apply total_eq_zero_of_each
    rintro ⟨b,q⟩ hq
    dsimp only
    by_cases he : a++b=w
    · simp only [he,beq_self_eq_true,↓reduceIte]
      by_cases hpz : ofList p=0
      · rw [hpz,poly_zero_mul]
      by_cases hqz : ofList q=0
      · rw [hqz,poly_mul_zero]
      have hva := (A.circuit_matrix f _ hu'.1).1 a (by rw [entry_lookup _ _ _ hp]; exact hpz)
      have hwa : weight s a=weight r (u.take r.length) := by
        by_cases h : weight s a=weight r (u.take r.length)
        · exact h
        · have hz := ihf _ hu'.1 a h
          rw [entry_lookup _ _ _ hp] at hz
          contradiction
      have hwb : weight v b=weight t (u.drop r.length) := by
        by_cases h : weight v b=weight t (u.drop r.length)
        · exact h
        · have hz := ihg _ hu'.2 b h
          rw [entry_lookup _ _ _ hq] at hz
          contradiction
      apply False.elim
      apply hw
      rw [← he,weight_append s v a b ((validWord_iff _ _).mp hva).1.symm,hwa,hwb]
      rw [← weight_append r t _ _ ((validWord_iff _ _).mp hu'.1).1.symm,List.take_append_drop]
    · simp [he]
  | add f g ihf ihg => rw [realization_eval_add,ihf u hu w hw,ihg u hu w hw,poly_zero_add]
  | neg f ih => rw [realization_eval_neg,ih u hu w hw,poly_zero_mul]
  | scaleD f ih => rw [realization_eval_scaleD,ih u hu w hw,poly_zero_mul]
  | zero s t => exact realization_eval_zero s t u w

#print axioms circuit_weight_zero
end WebMu.Revised.WeightConservation
