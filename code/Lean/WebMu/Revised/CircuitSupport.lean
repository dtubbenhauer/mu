import WebMu.Revised.CircuitSparseSemantics
import WebMu.Revised.M2Flow

/-! Support and typed-step semantics for the custom circuit evaluator. -/
namespace WebMu.Revised.Bar
open Laurent Algebra GrowthBridge M2Flow
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem localTerms_valid (op : Op) (u : Word) (term : Word × Laurent)
    (h : term ∈ localTerms op u) : validWord (upperArity op) term.1 = true := by
  unfold localTerms at h
  split at h <;> simp_all [validWord, upperArity] <;> grind

theorem transitions_valid (n : Nat) (u : Word) (step : Step) (term : Word × Laurent)
    (hu : validWord n u = true) (h : term ∈ transitions step u) :
    validWord (n - arity step.1 + upperArity step.1) term.1 = true := by
  rcases step with ⟨op,i⟩
  obtain ⟨hul,hut⟩ := (Revised.validWord_iff n u).mp hu
  simp only [transitions] at h
  split at h
  next hi =>
    obtain ⟨⟨v,q⟩,hv,he⟩ := List.mem_map.mp h
    cases he
    obtain ⟨hvl,hvt⟩ := (Revised.validWord_iff _ _).mp (localTerms_valid op _ (v,q) hv)
    apply (Revised.validWord_iff _ _).mpr
    constructor
    · simp only [List.length_append,List.length_take,List.length_drop,hvl,hul]
      omega
    · intro a ha
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · exact hut a (List.mem_of_mem_take ha)
      · exact hvt a ha
      · exact hut a (List.mem_of_mem_drop ha)
  · simp at h

theorem descendSigns_length (s t : Signs) (step : Step)
    (h : descendSigns t step = some s) :
    s.length - arity step.1 + upperArity step.1 = t.length := by
  rcases step with ⟨op,i⟩
  unfold descendSigns at h
  cases ha : t[i]? with
  | none => simp [ha] at h
  | some a =>
    cases hb : t[i+1]? with
    | none => simp [ha,hb] at h
    | some b =>
      have hi : i < t.length := (List.getElem?_eq_some_iff.mp ha).1
      have hj : i+1 < t.length := (List.getElem?_eq_some_iff.mp hb).1
      have hl := congrArg (Option.map List.length) h
      cases op <;> cases a <;> cases b <;>
        simp [ha,hb,Bind.bind,Pure.pure,Option.bind,List.length_append,List.length_take,List.length_drop] at hl <;>
        simp only [arity,upperArity] <;> omega

theorem ascendSigns_length (s t : Signs) (step : Step)
    (h : ascendSigns s step = some t) :
    s.length - arity step.1 + upperArity step.1 = t.length := by
  rcases step with ⟨op,i⟩
  cases op with
  | cup => simp [ascendSigns] at h
  | y =>
    cases ha : s[i]? with
    | none => simp [ascendSigns,ha] at h
    | some a =>
      have hi : i < s.length := (List.getElem?_eq_some_iff.mp ha).1
      have hl := congrArg (Option.map List.length) h
      cases a <;>
        simp [ascendSigns,ha,Bind.bind,Pure.pure,Option.bind,List.length_append,List.length_take,List.length_drop] at hl <;>
        simp only [arity,upperArity] <;> omega
  | h | lam | sigma =>
    cases ha : s[i]? with
    | none => simp [ascendSigns,ha] at h
    | some a =>
      cases hb : s[i+1]? with
      | none => simp [ascendSigns,ha,hb] at h
      | some b =>
        have hi : i < s.length := (List.getElem?_eq_some_iff.mp ha).1
        have hj : i+1 < s.length := (List.getElem?_eq_some_iff.mp hb).1
        have hl := congrArg (Option.map List.length) h
        cases a <;> cases b <;>
          simp [ascendSigns,ha,hb,Bind.bind,Pure.pure,Option.bind,List.length_append,List.length_take,List.length_drop] at hl <;>
          simp only [arity,upperArity] <;> omega


theorem singleton_supported (n : Nat) (u : Word) (p : Laurent)
    (hu : validWord n u = true) : Supported n (singleton u p) := by
  intro w hw
  by_cases he : u=w
  · simpa [← he] using hu
  · have hz : ofList ((singleton u p).getD w []) = 0 := by rw [singleton_poly,if_neg he]
    exact False.elim (hw hz)

theorem transitionCoefficient_invalid (n : Nat) (u w : Word) (step : Step)
    (hu : validWord n u = true)
    (hw : validWord (n - arity step.1 + upperArity step.1) w ≠ true) :
    transitionCoefficient (transitions step) u w = 0 := by
  apply total_eq_zero_of_each
  rintro ⟨v,q⟩ hv
  dsimp only
  by_cases he : v=w
  · subst v
    exact False.elim (hw (transitions_valid n u step (w,q) hu hv))
  · simp [he]

theorem applyStep_supported (n : Nat) (x : Tensor) (step : Step)
    (hx : Supported n x) :
    Supported (n - arity step.1 + upperArity step.1) (applyStep x step) := by
  intro w hw
  by_cases hv : validWord (n - arity step.1 + upperArity step.1) w = true
  · exact hv
  · apply False.elim
    apply hw
    rw [applyStep_dense n x step w hx]
    apply total_eq_zero_of_each
    intro i _
    rw [transitionCoefficient_invalid n (decodeWord n i.val) w step (decode_valid _ _) hv,
      poly_zero_mul]

theorem ascend_step_supported (s t : Signs) (step : Step)
    (h : ascendSigns s step = some t) (x : Tensor) (hx : Supported s.length x) :
    Supported t.length (applyStep x step) := by
  rw [← ascendSigns_length s t step h]
  exact applyStep_supported s.length x step hx

theorem descend_step_supported (s t : Signs) (step : Step)
    (h : descendSigns t step = some s) (x : Tensor) (hx : Supported s.length x) :
    Supported t.length (applyStep x step) := by
  rw [← descendSigns_length s t step h]
  exact applyStep_supported s.length x step hx

end WebMu.Revised.Bar
