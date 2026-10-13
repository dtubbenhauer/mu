import WebMu.Revised.CircuitSupport
import WebMu.Revised.GrowthPairing

/-! Exact coordinates of the literal two-vertex H diagram, before any
representation reference interface is introduced. All statements in this
module are derived from the primitive Y/lambda tables and finite Laurent
arithmetic; no H-map coordinate law is assumed. -/
namespace WebMu.Revised.GrowthPrimitiveRealization
open Laurent Algebra GrowthBridge GrowthPairing GrowthAdjoint M2Flow Bar
set_option maxHeartbeats 0
set_option maxRecDepth 1000

def twiceTerms (i : Nat) (u : Word) : List (Word × Laurent) :=
  (transitions (.y,i) u).flatMap fun (r,p) =>
    (transitions (.lam,i+1) r).map fun (s,q) => (s,Laurent.mul p q)

theorem transitions_framed (op : Op) (p w q : Word) (hw : w.length=arity op) :
    transitions (op,p.length) (p++w++q) =
      (localTerms op w).map (fun (r,a) => (p++r++q,a)) := by
  simp only [transitions]
  have hb : p.length + arity op ≤ (p++w++q).length := by simp [hw]
  rw [if_pos hb]
  have htake : ((p++w++q).drop p.length).take (arity op)=w := by
    simp only [List.append_assoc,List.drop_left]
    rw [← hw,List.take_left]
  have hp : (p++w++q).take p.length=p := by simp [List.append_assoc]
  have hq : (p++w++q).drop (p.length+arity op)=q := by
    rw [← hw,← List.length_append,List.drop_left]
  rw [htake,hp,hq]

theorem h_local_paths (a b : Fin 3) :
    twiceTerms 0 [a.val,b.val] = localTerms .h [a.val,b.val] := by
  obtain ⟨a,ha⟩ := a
  obtain ⟨b,hb⟩ := b
  have ha' : a=0 ∨ a=1 ∨ a=2 := by omega
  have hb' : b=0 ∨ b=1 ∨ b=2 := by omega
  rcases ha' with rfl|rfl|rfl <;> rcases hb' with rfl|rfl|rfl <;>
    simp [twiceTerms,transitions,arity,localTerms,Laurent.one,Laurent.monomial,
      Laurent.mul,Laurent.shiftScale,Laurent.add]

theorem flatMap_congr_mem {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x, x∈xs → f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,h x (by simp),ih (fun y hy => h y (by simp [hy]))]

theorem lam_framed (p q : Word) (a b c : Nat) :
    transitions (.lam,p.length+1) (p++[a,b]++c::q) =
      (localTerms .lam [b,c]).map (fun (r,d) => (p++[a]++r++q,d)) := by
  have he : p++[a,b]++c::q=(p++[a])++[b,c]++q := by simp [List.append_assoc]
  have hl : p.length+1=(p++[a]).length := by simp
  rw [he,hl,transitions_framed .lam (p++[a]) [b,c] q rfl]

theorem h_framed_paths (p q : Word) (a b : Fin 3) :
    twiceTerms p.length (p++[a.val,b.val]++q) =
      (localTerms .h [a.val,b.val]).map (fun (r,c) => (p++r++q,c)) := by
  unfold twiceTerms
  have hi : p++[a.val,b.val]++q = p++[a.val]++(b.val::q) := by simp [List.append_assoc]
  rw [hi,transitions_framed .y p [a.val] (b.val::q) rfl]
  simp only [List.flatMap_map]
  have he : ∀ r c, (r,c) ∈ localTerms .y [a.val] →
    (transitions (.lam,p.length+1) (p++r++b.val::q)).map
        (fun (s,d) => (s,Laurent.mul c d)) =
      ((transitions (.lam,1) (r++[b.val])).map
        (fun (s,d) => (s,Laurent.mul c d))).map
        (fun (r,d) => (p++r++q,d)) := by
    intro r c hr
    have ha : a.val=0 ∨ a.val=1 ∨ a.val=2 := by omega
    rcases ha with ha|ha|ha <;>
      simp [localTerms,ha] at hr <;>
      rcases hr with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      rw [lam_framed] <;>
      simp [transitions,arity,List.map_map,List.append_assoc]
  rw [flatMap_congr_mem _ _ _ (fun x hx => he x.1 x.2 hx)]
  rw [← List.map_flatMap]
  have hy : transitions (.y,0) [a.val,b.val] =
      (localTerms .y [a.val]).map (fun (r,c) => (r++[b.val],c)) := by
    simp [transitions,arity]
  have hl := h_local_paths a b
  unfold twiceTerms at hl
  rw [hy,List.flatMap_map] at hl
  rw [hl]


theorem h_paths (i : Nat) (u : Word) (hu : Ternary u) (hi : i+2≤u.length) :
    twiceTerms i u = transitions (.h,i) u := by
  have hp : (u.take i).length=i := List.length_take_of_le (by omega)
  have hd : 2≤(u.drop i).length := by simp only [List.length_drop]; omega
  obtain ⟨a,b,q,hq⟩ : ∃ a b q, u.drop i=a::b::q := by
    cases he : u.drop i with
    | nil => simp [he] at hd
    | cons a rest =>
      cases rest with
      | nil => simp [he] at hd
      | cons b q => exact ⟨a,b,q,rfl⟩
  have he : u=u.take i++[a,b]++q := by
    calc
      u = u.take i++u.drop i := (List.take_append_drop i u).symm
      _ = u.take i++[a,b]++q := by rw [hq]; simp [List.append_assoc]
  have ha : a<3 := hu a (by rw [he]; simp)
  have hb : b<3 := hu b (by rw [he]; simp)
  have h := h_framed_paths (u.take i) q ⟨a,ha⟩ ⟨b,hb⟩
  rw [← transitions_framed .h (u.take i) [a,b] q rfl] at h
  simpa only [hp,← he] using h

theorem total_transition (n : Nat) (f : Word → List (Word × Laurent)) (u : Word)
    (hf : ∀ term, term∈f u → validWord n term.1=true) (F : Word → Poly) :
    total (completeWords n) (fun w => F w * transitionCoefficient f u w) =
      total (f u) (fun (w,p) => F w * ofList p) := by
  unfold transitionCoefficient
  simp only [← mul_total]
  rw [total_swap]
  apply total_congr_mem
  rintro ⟨w,p⟩ hp
  have hmem := (completeWords_mem n w).mpr (hf (w,p) hp)
  have he : (fun x => F x * (if w==x then ofList p else 0)) =
      (fun x => if x=w then F w * ofList p else 0) := by
    funext x
    by_cases h : x=w
    · subst x; simp
    · simp [h,Ne.symm h]
  rw [he,total_delta _ (completeWords_nodup n)]
  simp [hmem]

theorem twiceTerms_coefficient (i : Nat) (u o : Word) :
    transitionCoefficient (twiceTerms i) u o =
      total (transitions (.y,i) u) (fun (r,p) =>
        transitionCoefficient (transitions (.lam,i+1)) r o * ofList p) := by
  unfold transitionCoefficient twiceTerms
  rw [total_flatMap]
  apply total_congr_mem
  rintro ⟨r,p⟩ _
  rw [total_map]
  dsimp only
  rw [← total_mul]
  apply total_congr_mem
  rintro ⟨s,q⟩ _
  by_cases h : s==o <;> simp [h,poly_mul_comm]


theorem singleton_foldlM_iff {α β : Type} (f : α → β → Option α)
    (step : β) (s t : α) : [step].foldlM f s=some t ↔ f s step=some t := by
  cases h : f s step <;> simp [List.foldlM_cons,h]



theorem ascend_cons (a : Bool) (s : Signs) (op : Op) (i : Nat) :
    ascendSigns (a::s) (op,i+1)=(ascendSigns s (op,i)).map (List.cons a) := by
  cases op <;> cases h₁ : s[i]? <;> cases h₂ : s[i+1]? <;>
    simp [ascendSigns,h₁,h₂,Nat.add_assoc,Bind.bind,Pure.pure,Option.bind]
  all_goals split <;> simp_all

theorem descend_cons (a : Bool) (s : Signs) (op : Op) (i : Nat) :
    descendSigns (a::s) (op,i+1)=(descendSigns s (op,i)).map (List.cons a) := by
  cases op <;> cases h₁ : s[i]? <;> cases h₂ : s[i+1]? <;>
    simp [descendSigns,h₁,h₂,Nat.add_assoc,Bind.bind,Pure.pure,Option.bind]
  all_goals split <;> simp_all

theorem up_h_typing_option (s t : Signs) (i : Nat)
    (h : ascendSigns s (.h,i)=some t) :
    ∃ mid, ascendSigns s (.y,i)=some mid ∧
      ascendSigns mid (.lam,i+1)=some t ∧ i+2≤s.length := by
  induction i generalizing s t with
  | zero =>
    cases s with
    | nil => simp [ascendSigns] at h
    | cons a rest =>
      cases rest with
      | nil => simp [ascendSigns] at h
      | cons b rest =>
        cases a <;> cases b <;> simp [ascendSigns] at h
        all_goals subst t
        · exact ⟨[true,true,true]++rest,by simp [ascendSigns]⟩
        · exact ⟨[false,false,false]++rest,by simp [ascendSigns]⟩
  | succ i ih =>
    cases s with
    | nil => simp [ascendSigns] at h
    | cons a s =>
      rw [ascend_cons] at h
      cases he : ascendSigns s (.h,i) with
      | none => simp [he] at h
      | some t' =>
        have ht : a::t'=t := by simpa [he] using h
        subst t
        obtain ⟨mid,hy,hl,hb⟩ := ih s t' he
        refine ⟨a::mid,?_,?_,by simp; omega⟩
        · rw [ascend_cons,hy]; rfl
        · rw [show i+1+1=(i+1)+1 by omega,ascend_cons,hl]; rfl

theorem down_h_typing_option (s t : Signs) (i : Nat)
    (h : descendSigns t (.h,i)=some s) :
    ∃ mid, ascendSigns s (.y,i)=some mid ∧
      ascendSigns mid (.lam,i+1)=some t ∧ i+2≤s.length := by
  induction i generalizing s t with
  | zero =>
    cases t with
    | nil => simp [descendSigns] at h
    | cons a rest =>
      cases rest with
      | nil => simp [descendSigns] at h
      | cons b rest =>
        cases a <;> cases b <;> simp [descendSigns] at h
        all_goals subst s
        · exact ⟨[false,false,false]++rest,by simp [ascendSigns]⟩
        · exact ⟨[true,true,true]++rest,by simp [ascendSigns]⟩
  | succ i ih =>
    cases t with
    | nil => simp [descendSigns] at h
    | cons a t =>
      rw [descend_cons] at h
      cases he : descendSigns t (.h,i) with
      | none => simp [he] at h
      | some s' =>
        have hs : a::s'=s := by simpa [he] using h
        subst s
        obtain ⟨mid,hy,hl,hb⟩ := ih s' t he
        refine ⟨a::mid,?_,?_,by simp; omega⟩
        · rw [ascend_cons,hy]; rfl
        · rw [show i+1+1=(i+1)+1 by omega,ascend_cons,hl]; rfl

theorem up_h_typing (s t : Signs) (i : Nat)
    (h : [(.h,i)].foldlM ascendSigns s=some t) :
    ∃ mid, [(.y,i)].foldlM ascendSigns s=some mid ∧
      [(.lam,i+1)].foldlM ascendSigns mid=some t ∧ i+2≤s.length := by
  obtain ⟨mid,hy,hl,hb⟩ := up_h_typing_option s t i ((singleton_foldlM_iff _ _ _ _).mp h)
  exact ⟨mid,(singleton_foldlM_iff _ _ _ _).mpr hy,
    (singleton_foldlM_iff _ _ _ _).mpr hl,hb⟩

theorem down_h_typing (s t : Signs) (i : Nat)
    (h : [(.h,i)].foldlM descendSigns t=some s) :
    ∃ mid, [(.y,i)].foldlM ascendSigns s=some mid ∧
      [(.lam,i+1)].foldlM ascendSigns mid=some t ∧ i+2≤s.length := by
  obtain ⟨mid,hy,hl,hb⟩ := down_h_typing_option s t i ((singleton_foldlM_iff _ _ _ _).mp h)
  exact ⟨mid,(singleton_foldlM_iff _ _ _ _).mpr hy,
    (singleton_foldlM_iff _ _ _ _).mpr hl,hb⟩

end WebMu.Revised.GrowthPrimitiveRealization
