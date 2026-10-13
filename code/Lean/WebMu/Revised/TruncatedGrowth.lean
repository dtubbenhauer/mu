import WebMu.Revised.Sparse

/-! Exact upper-degree truncation of finite local tensor contractions. All bounds
are on powers of v. Retaining a term only when it can still reach the requested
cutoff preserves every coefficient at or above that cutoff. -/
namespace WebMu.Revised.TruncatedGrowth
open Laurent Algebra
set_option maxHeartbeats 0

/-- Agreement of all Laurent coefficients at or above an integer cutoff. -/
def AgreeFrom (cutoff : Int) (p q : Laurent) : Prop :=
  ∀ d, cutoff ≤ d → coeff p d = coeff q d

def BoundedAbove (bound : Int) (p : Laurent) : Prop :=
  ∀ term ∈ p, term.1 ≤ bound

def keepAbove (cutoff : Int) (p : Laurent) : Laurent :=
  p.filter (fun term => cutoff ≤ term.1)

theorem coeff_keepAbove (c : Int) (p : Laurent) (d : Int) :
    coeff (keepAbove c p) d = if c ≤ d then coeff p d else 0 := by
  induction p with
  | nil => simp [keepAbove, coeff]
  | cons term p ih =>
    rcases term with ⟨e,a⟩
    simp only [keepAbove, List.filter_cons, decide_eq_true_eq]
    change coeff (if c ≤ e then (e,a)::keepAbove c p else keepAbove c p) d = _
    by_cases he : c ≤ e <;> by_cases hd : c ≤ d <;> by_cases hed : e=d <;>
      simp only [he, hd, hed, decide_true, decide_false, Bool.false_eq_true,
        if_true, if_false, coeff, ih] <;> omega

theorem keepAbove_agrees (c : Int) (p : Laurent) : AgreeFrom c (keepAbove c p) p := by
  intro d hd
  simp [coeff_keepAbove, hd]

theorem mul_agrees (c b : Int) (p q r : Laurent) (h : AgreeFrom (c-b) p q)
    (hr : BoundedAbove b r) : AgreeFrom c (mul p r) (mul q r) := by
  intro d hd
  induction r with
  | nil => rw [mul_comm p [], mul_comm q []]; rfl
  | cons term r ih =>
    rcases term with ⟨e,a⟩
    rw [coeff_mul_cons, coeff_mul_cons]
    have he : e ≤ b := hr (e,a) (by simp)
    rw [h (d-e) (by omega), ih (by intro term ht; exact hr term (by simp [ht]))]

def MapAgreeFrom (c : Int) (x y : Tensor) : Prop :=
  ∀ w, AgreeFrom c (x.getD w []) (y.getD w [])

def pruneMap (c : Int) (x : Tensor) : Tensor :=
  x.fold (fun out w p => accumulate out w (keepAbove c p)) ∅

theorem pruneMap_poly (c : Int) (x : Tensor) (w : Word) :
    ofList ((pruneMap c x).getD w []) = ofList (keepAbove c (x.getD w [])) := by
  rw [pruneMap, hashmap_fold_poly]
  exact hashmap_total_lookup x w (fun p => ofList (keepAbove c p)) rfl

theorem pruneMap_agrees (c : Int) (x : Tensor) : MapAgreeFrom c (pruneMap c x) x := by
  intro w d hd
  have he := congrArg (fun p => coefficient p d) (pruneMap_poly c x w)
  simpa only [coefficient_ofList, coeff_keepAbove, if_pos hd] using he

/-- The finite outgoing transition list of an arbitrary local tensor map. -/
abbrev Transition := Word → List (Word × Laurent)

def linearMap (t : Transition) (x : Tensor) : Tensor :=
  x.toList.foldl (fun out term =>
    (t term.1).foldl (fun out edge => accumulate out edge.1 (mul term.2 edge.2)) out) ∅

theorem linearMap_poly (t : Transition) (x : Tensor) (w : Word) :
    ofList ((linearMap t x).getD w []) =
    total x.toList (fun term => total (t term.1) (fun edge =>
      if edge.1 == w then ofList (mul term.2 edge.2) else 0)) := by
  have hall (xs : List (Word × Laurent)) (acc : Tensor) :
      ofList ((xs.foldl (fun out term =>
        (t term.1).foldl (fun out edge => accumulate out edge.1 (mul term.2 edge.2)) out) acc).getD w []) =
      ofList (acc.getD w []) + total xs (fun term => total (t term.1) (fun edge =>
        if edge.1 == w then ofList (mul term.2 edge.2) else 0)) := by
    induction xs generalizing acc with
    | nil => simp
    | cons term xs ih =>
      rw [List.foldl_cons, ih, fold_accumulate_poly, total_cons, poly_add_assoc]
  simpa [linearMap] using hall x.toList ∅

def dedup : List Word → List Word
  | [] => []
  | w::ws => if w ∈ ws then dedup ws else w::dedup ws

@[simp] theorem mem_dedup (w : Word) (ws : List Word) : w ∈ dedup ws ↔ w ∈ ws := by
  induction ws with
  | nil => simp [dedup]
  | cons a ws ih =>
    by_cases h : a ∈ ws <;> simp [dedup,h,ih] <;> grind

theorem dedup_nodup (ws : List Word) : (dedup ws).Nodup := by
  induction ws with
  | nil => simp [dedup]
  | cons a ws ih => by_cases h : a ∈ ws <;> simp [dedup,h,ih]

/-- Reindexing a sparse sum by any duplicate-free set containing its keys. -/
theorem hashmap_total_keys (x : Tensor) (ws : List Word) (hnd : ws.Nodup)
    (hx : ∀ term ∈ x.toList, term.1 ∈ ws)
    (f : Word → Laurent → Poly) (hz : ∀ w, f w []=0) :
    total x.toList (fun term => f term.1 term.2) = total ws (fun w => f w (x.getD w [])) := by
  symm
  calc
    total ws (fun w => f w (x.getD w [])) =
        total ws (fun w => total x.toList (fun term => if term.1 == w then f w term.2 else 0)) := by
      apply total_congr_mem
      intro w _
      exact (hashmap_total_lookup x w (f w) (hz w)).symm
    _ = total x.toList (fun term => total ws (fun w => if term.1 == w then f w term.2 else 0)) :=
      total_swap _ _ _
    _ = total x.toList (fun term => f term.1 term.2) := by
      apply total_congr_mem
      intro term ht
      have he (w : Word) : (if term.1 == w then f w term.2 else 0) =
          if w=term.1 then f term.1 term.2 else 0 := by
        by_cases hw : w=term.1 <;> simp [hw,Ne.symm]
      simp only [he]
      rw [total_delta ws hnd, if_pos (hx term ht)]

theorem total_coefficient_congr {ι : Type} (is : List ι) (f g : ι → Poly) (d : Int)
    (h : ∀ i ∈ is, coefficient (f i) d = coefficient (g i) d) :
    coefficient (total is f) d = coefficient (total is g) d := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [total_cons, coefficient_add]
    rw [h i (by simp), ih (by intro j hj; exact h j (by simp [hj]))]

/-- A bound on every local transition propagates upper-degree agreement. -/
theorem linearMap_agrees (t : Transition) (c b : Int) (x y : Tensor)
    (ht : ∀ w edge, edge ∈ t w → BoundedAbove b edge.2)
    (hxy : MapAgreeFrom (c-b) x y) :
    MapAgreeFrom c (linearMap t x) (linearMap t y) := by
  let ws := dedup (x.toList.map Prod.fst ++ y.toList.map Prod.fst)
  have hx : ∀ term ∈ x.toList, term.1 ∈ ws := by
    intro term ht
    simp only [ws, mem_dedup, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨term,ht,rfl⟩)
  have hy : ∀ term ∈ y.toList, term.1 ∈ ws := by
    intro term ht
    simp only [ws, mem_dedup, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨term,ht,rfl⟩)
  have hn : ws.Nodup := dedup_nodup _
  intro w d hd
  change coefficient (ofList ((linearMap t x).getD w [])) d =
    coefficient (ofList ((linearMap t y).getD w [])) d
  rw [linearMap_poly, linearMap_poly]
  let f := fun a p => total (t a) (fun edge => if edge.1 == w then ofList (mul p edge.2) else 0)
  have hz : ∀ a, f a []=0 := by
    intro a
    apply (total_congr_mem (t a) _ (fun _ => 0) ?_).trans (total_zero _)
    intro edge _
    simp [mul]
  rw [hashmap_total_keys x ws hn hx f hz, hashmap_total_keys y ws hn hy f hz]
  apply total_coefficient_congr
  intro a _
  apply total_coefficient_congr
  intro edge he
  by_cases hw : edge.1 == w
  · simp only [if_pos hw, coefficient_ofList]
    exact mul_agrees c b _ _ _ (hxy a) (ht a edge he) d hd
  · simp [hw]

theorem addMap_agrees (c : Int) (x y u v : Tensor)
    (hx : MapAgreeFrom c x y) (hu : MapAgreeFrom c u v) :
    MapAgreeFrom c (addMap x u) (addMap y v) := by
  intro w d hd
  change coefficient (ofList ((addMap x u).getD w [])) d =
    coefficient (ofList ((addMap y v).getD w [])) d
  simp only [addMap_poly, coefficient_add, coefficient_ofList]
  rw [hx w d hd, hu w d hd]

theorem scaleMap_agrees (c b : Int) (x y : Tensor) (p : Laurent)
    (hx : MapAgreeFrom (c-b) x y) (hp : BoundedAbove b p) :
    MapAgreeFrom c (scaleMap x p) (scaleMap y p) := by
  intro w d hd
  change coefficient (ofList ((scaleMap x p).getD w [])) d =
    coefficient (ofList ((scaleMap y p).getD w [])) d
  simp only [scaleMap_poly]
  exact mul_agrees c b _ _ p (hx w) hp d hd

theorem sumMap_agrees {ι : Type} (c : Int) (is : List ι) (x y : ι → Tensor)
    (h : ∀ i ∈ is, MapAgreeFrom c (x i) (y i)) :
    MapAgreeFrom c (sumMap (is.map x)) (sumMap (is.map y)) := by
  intro w d hd
  change coefficient (ofList ((sumMap (is.map x)).getD w [])) d =
    coefficient (ofList ((sumMap (is.map y)).getD w [])) d
  simp only [sumMap_poly, total_map]
  apply total_coefficient_congr
  intro i hi
  exact h i hi w d hd

/-- Each step uses the least partial degree able to reach the final cutoff. -/
def prunedIterate (steps : List (Transition × Int)) (cutoff : Int) (x : Tensor) : Tensor :=
  match steps with
  | [] => pruneMap cutoff x
  | (t,_)::rest =>
    prunedIterate rest cutoff (pruneMap (cutoff-(rest.map Prod.snd).sum) (linearMap t x))

def fullIterate (steps : List (Transition × Int)) (x : Tensor) : Tensor :=
  steps.foldl (fun x step => linearMap step.1 x) x

theorem prunedIterate_correct (steps : List (Transition × Int)) (cutoff : Int) (x y : Tensor)
    (ht : ∀ step ∈ steps, ∀ w edge, edge ∈ step.1 w → BoundedAbove step.2 edge.2)
    (hxy : MapAgreeFrom (cutoff-(steps.map Prod.snd).sum) x y) :
    MapAgreeFrom cutoff (prunedIterate steps cutoff x) (fullIterate steps y) := by
  induction steps generalizing x y with
  | nil =>
    intro w d hd
    exact (pruneMap_agrees cutoff x w d hd).trans (hxy w d (by simpa using hd))
  | cons step steps ih =>
    rcases step with ⟨t,b⟩
    apply ih
    · intro step hs; exact ht step (by simp [hs])
    · let c := cutoff-(steps.map Prod.snd).sum
      have hstep : MapAgreeFrom c (linearMap t x) (linearMap t y) := by
        apply linearMap_agrees t c b x y (ht (t,b) (by simp))
        intro w d hd
        apply hxy w d
        simp only [List.map_cons, List.sum_cons]
        dsimp [c] at hd
        omega
      intro w d hd
      exact (pruneMap_agrees c (linearMap t x) w d hd).trans (hstep w d hd)

end WebMu.Revised.TruncatedGrowth
