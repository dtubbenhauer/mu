import WebMu.Revised.TruncatedGrowth

namespace WebMu.Revised.GrowthBridge
open Laurent Algebra TruncatedGrowth

def transitions (step : Step) (word : Word) : List (Word × Laurent) :=
  let (op,i) := step
  if i + arity op ≤ word.length then
    (localTerms op ((word.drop i).take (arity op))).map fun (r,q) =>
      (word.take i ++ r ++ word.drop (i+arity op),q)
  else []

theorem id_forIn_yield {α β : Type} (xs : List α) (f : β → α → β) (a : β) :
    (ForIn.forIn (m:=Id) xs a
      (fun x b => (ForInStep.yield (f b x) : Id (ForInStep β)))) =
      xs.foldl f a := List.forIn_pure_yield_eq_foldl (m:=Id) (fun x b => f b x) a

theorem ite_yield {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then ForInStep.yield a else ForInStep.yield b) =
      ForInStep.yield (if c then a else b) := by split <;> rfl

theorem applyStep_eq_linearMap (values : Tensor) (step : Step) :
    applyStep values step = linearMap (transitions step) values := by
  rcases step with ⟨op,i⟩
  unfold applyStep linearMap
  simp only [Std.HashMap.forIn_eq_forIn_toList, pure_bind]
  dsimp only [Id.run, Bind.bind, Pure.pure]
  simp only [id_forIn_yield]
  have hf : (fun (x : Word × Laurent) (r : Tensor) =>
      if i + arity op ≤ x.1.length then
        ForInStep.yield ((localTerms op ((x.1.drop i).take (arity op))).foldl
          (fun out term => accumulate out (x.1.take i ++ term.1 ++ x.1.drop (i+arity op))
            (mul x.2 term.2)) r)
      else ForInStep.yield r) =
      (fun x r => ForInStep.yield ((transitions (op,i) x.1).foldl
        (fun out term => accumulate out term.1 (mul x.2 term.2)) r)) := by
    funext x r
    by_cases h : i + arity op ≤ x.1.length <;>
      simp only [h, ↓reduceIte, transitions, List.foldl_map, List.foldl_nil]
  rw [hf]
  exact id_forIn_yield _ _ _

def transitionCoefficient (f : Word → List (Word × Laurent)) (input output : Word) : Poly :=
  total (f input) (fun (w,q) => if w == output then ofList q else 0)

theorem transition_fold_poly (ts : List (Word × Laurent)) (p : Laurent)
    (out : Tensor) (w : Word) :
    ofList ((ts.foldl (fun out (u,q) => accumulate out u (mul p q)) out).getD w []) =
      ofList (out.getD w []) + ofList p *
        total ts (fun (u,q) => if u == w then ofList q else 0) := by
  rw [fold_accumulate_poly]
  congr 1
  rw [← mul_total]
  apply total_congr_mem
  rintro ⟨u,q⟩ _
  by_cases h : u == w <;> simp [h]

theorem linearMap_factored_poly (f : Transition) (values : Tensor) (w : Word) :
    ofList ((linearMap f values).getD w []) =
      total values.toList (fun (u,p) => ofList p * transitionCoefficient f u w) := by
  rw [linearMap_poly]
  apply total_congr_mem
  rintro ⟨u,p⟩ _
  simp only [transitionCoefficient]
  rw [← mul_total]
  apply total_congr_mem
  rintro ⟨v,q⟩ _
  by_cases h : v == w <;> simp [h]

theorem applyStep_poly (values : Tensor) (step : Step) (w : Word) :
    ofList ((applyStep values step).getD w []) =
      total values.toList (fun (u,p) => ofList p * transitionCoefficient (transitions step) u w) := by
  rw [applyStep_eq_linearMap, linearMap_factored_poly]

def opBound : Op → Int
  | .h | .lam => 1
  | .sigma => 2
  | .y | .cup => 0

theorem localTerms_bounded (op : Op) (w : Word) (term : Word × Laurent)
    (h : term ∈ localTerms op w) : BoundedAbove (opBound op) term.2 := by
  unfold localTerms at h
  split at h <;> simp_all [BoundedAbove, opBound, one, monomial] <;> grind

theorem transitions_bounded (step : Step) (w : Word) (term : Word × Laurent)
    (h : term ∈ transitions step w) : BoundedAbove (opBound step.1) term.2 := by
  rcases step with ⟨op,i⟩
  simp only [transitions] at h
  split at h
  · obtain ⟨⟨u,q⟩,hu,he⟩ := List.mem_map.mp h
    cases he
    exact localTerms_bounded op _ (u,q) hu
  · simp at h

end WebMu.Revised.GrowthBridge
