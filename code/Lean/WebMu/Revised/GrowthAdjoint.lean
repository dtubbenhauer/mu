import WebMu.Revised.GrowthBridge
import WebMu.Revised.M2Flow

namespace WebMu.Revised.GrowthAdjoint
open Laurent Algebra TruncatedGrowth GrowthBridge M2Flow

def downwardTransitions (step : Step) (word : Word) : List (Word × Laurent) :=
  let (op,i) := step
  if i + upperArity op ≤ word.length then
    (downwardTerms op ((word.drop i).take (upperArity op))).map fun (r,q) =>
      (word.take i ++ r ++ word.drop (i+upperArity op),q)
  else []

theorem downwardStep_eq_linearMap (values : Tensor) (step : Step) :
    downwardStep values step = linearMap (downwardTransitions step) values := by
  rcases step with ⟨op,i⟩
  unfold downwardStep linearMap
  simp only [Std.HashMap.forIn_eq_forIn_toList, pure_bind]
  dsimp only [Id.run, Bind.bind, Pure.pure]
  simp only [id_forIn_yield]
  have hf : (fun (x : Word × Laurent) (r : Tensor) =>
      if i + upperArity op ≤ x.1.length then
        ForInStep.yield ((downwardTerms op ((x.1.drop i).take (upperArity op))).foldl
          (fun out term => accumulate out (x.1.take i ++ term.1 ++ x.1.drop (i+upperArity op))
            (mul x.2 term.2)) r)
      else ForInStep.yield r) =
      (fun x r => ForInStep.yield ((downwardTransitions (op,i) x.1).foldl
        (fun out term => accumulate out term.1 (mul x.2 term.2)) r)) := by
    funext x r
    by_cases h : i + upperArity op ≤ x.1.length <;>
      simp only [h, ↓reduceIte, downwardTransitions, List.foldl_map, List.foldl_nil]
  rw [hf]
  exact id_forIn_yield _ _ _

theorem total_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → Poly) :
    total (xs.flatMap f) g = total xs (fun x => total (f x) g) := by
  have append (xs ys : List β) : total (xs++ys) g = total xs g + total ys g := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih,poly_add_assoc]
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, append, total_cons, ih]

theorem total_filterMap {α β : Type} (xs : List α) (f : α → Option β) (g : β → Poly) :
    total (xs.filterMap f) g = total xs (fun x => (f x).map g |>.getD 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h,ih]

theorem localTerms_input_mem (op : Op) (w : Word) (term : Word × Laurent)
    (h : term ∈ localTerms op w) : w ∈ words (arity op) := by
  unfold localTerms at h
  split at h <;> simp_all [words, arity, List.range_succ] <;> grind

theorem localTerms_lengths (op : Op) (w : Word) (term : Word × Laurent)
    (h : term ∈ localTerms op w) : w.length = arity op ∧ term.1.length = upperArity op := by
  unfold localTerms at h
  split at h <;> simp_all [arity,upperArity] <;> grind

theorem local_terms_transpose (op : Op) (lower upper : Word) :
    total (downwardTerms op upper) (fun (w,p) => if w == lower then ofList p else 0) =
      total (localTerms op lower) (fun (w,p) => if w == upper then ofList p else 0) := by
  rw [downwardTerms,total_flatMap]
  have hterm (a : Word) :
      total ((localTerms op a).filterMap (fun (u,p) => if u=upper then some (a,p) else none))
          (fun (w,p) => if w == lower then ofList p else 0) =
      if a=lower then total (localTerms op lower) (fun (w,p) => if w == upper then ofList p else 0)
        else 0 := by
    rw [total_filterMap]
    by_cases ha : a=lower
    · subst a
      simp only [↓reduceIte]
      apply total_congr_mem
      rintro ⟨w,p⟩ _
      by_cases hw : w=upper <;> simp [hw]
    · simp only [ha, ↓reduceIte]
      apply (total_congr_mem _ _ (fun _ => 0) ?_).trans (total_zero _)
      rintro ⟨w,p⟩ _
      by_cases hw : w=upper <;> simp [ha,hw]
  simp only [hterm]
  have hn : (words (arity op)).Nodup := by cases op <;> decide
  rw [total_delta _ hn]
  split
  · rfl
  next h =>
    have he : localTerms op lower = [] := by
      cases ht : localTerms op lower with
      | nil => rfl
      | cons t ts =>
        exact False.elim (h (localTerms_input_mem op lower t (by simp [ht])))
    simp [he]

end WebMu.Revised.GrowthAdjoint
