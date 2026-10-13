import WebMu.Revised.GrowthAdjoint

/-! The downward evaluator is exactly the transpose of the upward growth tensor,
including all untouched boundary factors. -/
namespace WebMu.Revised.GrowthPairing
open Laurent Algebra TruncatedGrowth GrowthBridge GrowthAdjoint M2Flow
set_option maxHeartbeats 0

 theorem splice_eq_iff (u v r : Word) (i k l : Nat)
    (hi : i+k ≤ u.length) (hr : r.length=l) :
    u.take i ++ r ++ u.drop (i+k)=v ↔
      i+l ≤ v.length ∧ u.take i=v.take i ∧ r=(v.drop i).take l ∧
        u.drop (i+k)=v.drop (i+l) := by
  have hp : (u.take i).length=i := List.length_take_of_le (by omega)
  constructor
  · intro h
    subst v
    have hl : (u.take i ++ r).length=i+l := by simp [hp,hr]
    constructor
    · simp only [List.length_append, hp, hr]; omega
    constructor
    · rw [List.append_assoc, List.take_left' hp]
    constructor
    · rw [List.append_assoc, List.drop_left' hp, List.take_left' hr]
    · rw [← hl, List.drop_left]
  · rintro ⟨_,hp',hr',hs'⟩
    rw [hp',hr',hs',List.append_assoc,← List.drop_drop]
    rw [List.take_append_drop,List.take_append_drop]

def contextCondition (i k l : Nat) (u v : Word) : Prop :=
  i+k ≤ u.length ∧ i+l ≤ v.length ∧ u.take i=v.take i ∧ u.drop (i+k)=v.drop (i+l)
instance (i k l : Nat) (u v : Word) : Decidable (contextCondition i k l u v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem contextCondition_swap (i k l : Nat) (u v : Word) :
    contextCondition i k l u v ↔ contextCondition i l k v u := by
  simp only [contextCondition]
  exact ⟨fun ⟨a,b,c,d⟩ => ⟨b,a,c.symm,d.symm⟩,
    fun ⟨a,b,c,d⟩ => ⟨b,a,c.symm,d.symm⟩⟩

def contextTerms (i k : Nat) (f : Word → List (Word × Laurent)) (u : Word) :=
  if i+k ≤ u.length then
    (f ((u.drop i).take k)).map (fun (r,q) => (u.take i ++ r ++ u.drop (i+k),q))
  else []

theorem contextCoefficient (i k l : Nat) (f : Word → List (Word × Laurent))
    (hf : ∀ w term, term ∈ f w → term.1.length=l) (u v : Word) :
    transitionCoefficient (contextTerms i k f) u v =
      if contextCondition i k l u v then
        transitionCoefficient f ((u.drop i).take k) ((v.drop i).take l) else 0 := by
  unfold transitionCoefficient contextTerms
  by_cases hi : i+k ≤ u.length
  · simp only [if_pos hi, total_map]
    by_cases hc : contextCondition i k l u v
    · rw [if_pos hc]
      apply total_congr_mem
      rintro ⟨r,q⟩ ht
      have hh := splice_eq_iff u v r i k l hi (hf _ _ ht)
      have he : (u.take i ++ r ++ u.drop (i+k)=v) ↔ r=(v.drop i).take l := by
        exact ⟨fun h => (hh.mp h).2.2.1,
          fun h => hh.mpr ⟨hc.2.1,hc.2.2.1,h,hc.2.2.2⟩⟩
      simp only [beq_iff_eq,he]
    · rw [if_neg hc]
      apply (total_congr_mem _ _ (fun _ => 0) ?_).trans (total_zero _)
      rintro ⟨r,q⟩ ht
      have hn : u.take i ++ r ++ u.drop (i+k) ≠ v := by
        intro h
        obtain ⟨a,b,_,d⟩ := (splice_eq_iff u v r i k l hi (hf _ _ ht)).mp h
        exact hc ⟨hi,a,b,d⟩
      simp only [beq_iff_eq, if_neg hn]
  · have hc : ¬contextCondition i k l u v := fun h => hi h.1
    simp [hi,hc]

theorem downwardTerms_lengths (op : Op) (w : Word) (term : Word × Laurent)
    (h : term ∈ downwardTerms op w) : term.1.length=arity op := by
  simp only [downwardTerms, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨u,_,⟨v,q⟩,ht,he⟩ := h
  split at he
  · cases he
    exact (localTerms_lengths op u (v,q) ht).1
  · simp at he

theorem contextual_transpose (step : Step) (u v : Word) :
    transitionCoefficient (downwardTransitions step) v u =
      transitionCoefficient (transitions step) u v := by
  rcases step with ⟨op,i⟩
  change transitionCoefficient (contextTerms i (upperArity op) (downwardTerms op)) v u =
    transitionCoefficient (contextTerms i (arity op) (localTerms op)) u v
  rw [contextCoefficient i (upperArity op) (arity op) _ (downwardTerms_lengths op),
    contextCoefficient i (arity op) (upperArity op) _ (fun w t h => (localTerms_lengths op w t h).2)]
  by_cases h : contextCondition i (arity op) (upperArity op) u v
  · have hh := (contextCondition_swap i (arity op) (upperArity op) u v).mp h
    simp only [if_pos h, if_pos hh]
    exact local_terms_transpose op _ _
  · have hh : ¬contextCondition i (upperArity op) (arity op) v u :=
      fun hh => h ((contextCondition_swap i (arity op) (upperArity op) u v).mpr hh)
    simp only [if_neg h, if_neg hh]

def sparsePair (x y : Tensor) : Poly :=
  total x.toList (fun (w,p) => ofList p * ofList (y.getD w []))

theorem sparsePair_double (x y : Tensor) :
    sparsePair x y = total x.toList (fun (u,p) => total y.toList (fun (v,q) =>
      if v=u then ofList p * ofList q else 0)) := by
  unfold sparsePair
  apply total_congr_mem
  rintro ⟨u,p⟩ _
  dsimp only
  rw [← hashmap_total_lookup y u ofList rfl, ← mul_total]
  apply total_congr_mem
  rintro ⟨v,q⟩ _
  by_cases h : v=u <;> simp [h]

theorem sparsePair_comm (x y : Tensor) : sparsePair x y=sparsePair y x := by
  rw [sparsePair_double,sparsePair_double,total_swap]
  apply total_congr_mem
  rintro ⟨u,p⟩ _
  apply total_congr_mem
  rintro ⟨v,q⟩ _
  by_cases h : u=v
  · simp [h,poly_mul_comm]
  · simp [h,Ne.symm h]

theorem sparsePair_linearMap_right (f : Transition) (x y : Tensor) :
    sparsePair x (linearMap f y) =
      total x.toList (fun (u,p) => total y.toList (fun (v,q) =>
        (ofList p * ofList q) * transitionCoefficient f v u)) := by
  unfold sparsePair
  apply total_congr_mem
  rintro ⟨u,p⟩ _
  dsimp only
  rw [linearMap_factored_poly, ← mul_total]
  apply total_congr_mem
  rintro ⟨v,q⟩ _
  exact (poly_mul_assoc _ _ _).symm

theorem step_transpose (step : Step) (x y : Tensor) :
    sparsePair (applyStep x step) y=sparsePair x (downwardStep y step) := by
  rw [sparsePair_comm,applyStep_eq_linearMap,downwardStep_eq_linearMap,
    sparsePair_linearMap_right,sparsePair_linearMap_right,total_swap]
  apply total_congr_mem
  rintro ⟨u,p⟩ _
  apply total_congr_mem
  rintro ⟨v,q⟩ _
  dsimp only
  rw [contextual_transpose,poly_mul_comm (ofList q) (ofList p)]

theorem singleton_pair (u : Word) (x : Tensor) :
    sparsePair (singleton u) x=ofList (x.getD u []) := by
  rw [sparsePair_comm]
  unfold sparsePair
  have he : total x.toList (fun (w,p) => ofList p * ofList ((singleton u).getD w [])) =
      total x.toList (fun (w,p) => if w == u then ofList p else 0) := by
    apply total_congr_mem
    rintro ⟨w,p⟩ _
    by_cases h : w=u <;> simp [singleton,Std.HashMap.getD_insert,h,Ne.symm,show ofList one=(1:Poly) from rfl]
  rw [he,hashmap_total_lookup x u ofList rfl]

theorem pair_singleton (x : Tensor) (u : Word) :
    sparsePair x (singleton u)=ofList (x.getD u []) := by
  rw [sparsePair_comm,singleton_pair]

theorem expand_transpose (steps : List Step) (x y : Tensor) :
    sparsePair (expand steps x) y=sparsePair x (steps.foldl downwardStep y) := by
  induction steps generalizing y with
  | nil => rfl
  | cons step steps ih =>
    simp only [expand,compose,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [step_transpose]
    exact ih _

/-- Full source coordinates of growth tensors agree with the independent downward
contraction evaluator. The proof includes the order reversal and the contexts. -/
theorem contract_is_expansion (steps : List Step) (boundary : Word) :
    ofList (contract steps boundary) =
      ofList ((expand steps (singleton [])).getD boundary []) := by
  have h := expand_transpose steps (singleton []) (singleton boundary)
  rw [pair_singleton,singleton_pair] at h
  exact h.symm

#print axioms contract_is_expansion
end WebMu.Revised.GrowthPairing
