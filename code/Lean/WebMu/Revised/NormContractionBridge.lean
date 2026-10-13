import WebMu.Local
import WebMu.Revised.Sparse
import WebMu.Revised.NormSemantics

namespace WebMu.Revised.NormContraction
open Laurent Algebra

def rowSupport (matrix : SmallMatrix) (i : Nat) : List (Nat × Laurent) :=
  (List.range 28).filterMap fun k =>
    let p := entry matrix i k
    if p.isEmpty then none else some (k,p)

def supportTable (matrix : SmallMatrix) : Array (List (Nat × Laurent)) :=
  (List.range 28).toArray.map (rowSupport matrix)

def columnFold (right : Column) (matrix : SmallMatrix) (acc : Laurent)
    (term : (Nat × Nat) × Laurent) : Laurent :=
  (supportTable matrix)[term.1.1]!.foldl (fun sum ks =>
    match right.get? (ks.1,term.1.2) with
    | none => sum
    | some q => add sum (mul (mul term.2 ks.2) q)) acc

theorem option_yield (value : Option Laurent) (acc p s : Laurent) :
    (match value with
    | some q => ForInStep.yield (add acc (mul (mul p s) q))
    | _ => ForInStep.yield acc) =
    ForInStep.yield (match value with
      | none => acc | some q => add acc (mul (mul p s) q)) := by
  cases value <;> rfl

theorem id_forIn_yield {α β : Type} (xs : List α) (f : β → α → β) (a : β) :
    (ForIn.forIn (m:=Id) xs a (fun x b => (ForInStep.yield (f b x) : Id (ForInStep β)))) =
      xs.foldl f a := List.forIn_pure_yield_eq_foldl (m:=Id) (fun x b => f b x) a

theorem pairColumns_fold (left right : Column) (matrix : SmallMatrix) :
    pairColumns left right matrix = left.toList.foldl (columnFold right matrix) [] := by
  unfold pairColumns
  simp only [Std.HashMap.forIn_eq_forIn_toList]
  simp only [pure_bind]
  dsimp only [Id.run, Bind.bind, Pure.pure]
  simp only [id_forIn_yield]
  apply congrArg (fun f => left.toList.foldl f [])
  funext acc term
  change (ForIn.forIn (m:=Id) (supportTable matrix)[term.1.1]! acc
    (fun ks a => match right.get? (ks.1,term.1.2) with
      | some q => ForInStep.yield (add a (mul (mul term.2 ks.2) q))
      | _ => ForInStep.yield a)) = _
  have hf : (fun (ks : Nat × Laurent) (a : Laurent) =>
      match right.get? (ks.1,term.1.2) with
      | some q => (ForInStep.yield (add a (mul (mul term.2 ks.2) q)) : Id (ForInStep Laurent))
      | _ => ForInStep.yield a) =
      fun ks a => (ForInStep.yield (match right.get? (ks.1,term.1.2) with
      | none => a | some q => add a (mul (mul term.2 ks.2) q)) : Id (ForInStep Laurent)) := by
    funext ks a
    cases right.get? (ks.1,term.1.2) <;> rfl
  exact (congrArg (fun fn => ForIn.forIn (m:=Id) (supportTable matrix)[term.1.1]! acc fn) hf).trans
    (id_forIn_yield _ _ _)

theorem supportTable_get (matrix : SmallMatrix) (i : Nat) (hi : i < 28) :
    (supportTable matrix)[i]! = rowSupport matrix i := by
  simp [supportTable, getElem!_pos, hi]

theorem rowFold_poly (right : Column) (w : Nat) (p acc : Laurent)
    (ks : List (Nat × Laurent)) :
    ofList (ks.foldl (fun sum k => match right.get? (k.1,w) with
      | none => sum | some q => add sum (mul (mul p k.2) q)) acc) =
    ofList acc + total ks (fun k => ofList p * ofList k.2 * ofList (right.getD (k.1,w) [])) := by
  induction ks generalizing acc with
  | nil => simp
  | cons k ks ih =>
    simp only [List.foldl_cons, total_cons]
    cases he : right.get? (k.1,w) with
    | none =>
      have hz : right.getD (k.1,w) [] = [] := by
        simp [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, he]
      rw [ih, hz]
      simp
    | some q =>
      have hq : right.getD (k.1,w) [] = q := by
        simp [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, he]
      rw [ih, ofList_add, ofList_mul, ofList_mul, hq, poly_add_assoc]

theorem rowSupport_total (matrix : SmallMatrix) (right : Column) (i w : Nat) (p : Laurent) :
    total (rowSupport matrix i) (fun k => ofList p * ofList k.2 * ofList (right.getD (k.1,w) [])) =
    total (List.range 28) (fun k =>
      ofList p * ofList (entry matrix i k) * ofList (right.getD (k,w) [])) := by
  have hall (ks : List Nat) :
      total (ks.filterMap (fun k => if (entry matrix i k).isEmpty then none
        else some (k,entry matrix i k)))
          (fun k => ofList p * ofList k.2 * ofList (right.getD (k.1,w) [])) =
      total ks (fun k => ofList p * ofList (entry matrix i k) * ofList (right.getD (k,w) [])) := by
    induction ks with
    | nil => rfl
    | cons k ks ih =>
      by_cases h : (entry matrix i k).isEmpty = true
      · have he : entry matrix i k = [] := List.isEmpty_iff.mp h
        simp only [List.filterMap_cons, h, ↓reduceIte, total_cons, he,
          ofList_empty, poly_mul_zero, poly_zero_mul, poly_zero_add]
        exact ih
      · simp only [List.filterMap_cons, h, Bool.false_eq_true, ↓reduceIte, total_cons, ih]
  exact hall _

theorem columnFold_poly (right : Column) (matrix : SmallMatrix) (acc p : Laurent)
    (i w : Nat) (hi : i < 28) :
    ofList (columnFold right matrix acc ((i,w),p)) =
      ofList acc + total (List.range 28) (fun k =>
        ofList p * ofList (entry matrix i k) * ofList (right.getD (k,w) [])) := by
  unfold columnFold
  rw [supportTable_get matrix i hi, rowFold_poly, rowSupport_total]

/-- The executable nested sparse contraction has the full coefficient semantics. -/
theorem pairColumns_sparse (left right : Column) (matrix : SmallMatrix)
    (hleft : ∀ term ∈ left.toList, term.1.1 < 28) :
    ofList (pairColumns left right matrix) =
      total left.toList (fun term => total (List.range 28) (fun k =>
        ofList term.2 * ofList (entry matrix term.1.1 k) * ofList (right.getD (k,term.1.2) []))) := by
  rw [pairColumns_fold]
  have hall (ls : List ((Nat × Nat) × Laurent)) (acc : Laurent)
      (hl : ∀ term ∈ ls, term.1.1 < 28) :
      ofList (ls.foldl (columnFold right matrix) acc) = ofList acc +
        total ls (fun term => total (List.range 28) (fun k =>
          ofList term.2 * ofList (entry matrix term.1.1 k) * ofList (right.getD (k,term.1.2) []))) := by
    induction ls generalizing acc with
    | nil => simp
    | cons term ls ih =>
      rcases term with ⟨⟨i,w⟩,p⟩
      rw [List.foldl_cons, ih _ (fun term ht => hl term (by simp [ht])),
        columnFold_poly right matrix acc p i w (hl ((i,w),p) (by simp)), total_cons, poly_add_assoc]
  simpa using hall left.toList [] hleft

/-- Enumerating a complete finite boundary agrees with sparse dictionary iteration. -/
theorem column_total_coordinates (x : Column) (es : List Nat) (hnd : es.Nodup)
    (hx : ∀ term ∈ x.toList, term.1.1 < 28 ∧ term.1.2 ∈ es)
    (f : Nat → Nat → Laurent → Poly) (hz : ∀ i w, f i w [] = 0) :
    total x.toList (fun term => f term.1.1 term.1.2 term.2) =
      total es (fun w => total (List.finRange 28) (fun i => f i.val w (x.getD (i.val,w) []))) := by
  symm
  calc
    total es (fun w => total (List.finRange 28) (fun i => f i.val w (x.getD (i.val,w) []))) =
        total es (fun w => total (List.finRange 28) (fun i =>
          total x.toList (fun term => if term.1 == (i.val,w) then f i.val w term.2 else 0))) := by
      apply total_congr_mem
      intro w _
      apply total_congr_mem
      intro i _
      exact (hashmap_total_lookup x (i.val,w) (f i.val w) (hz i.val w)).symm
    _ = total x.toList (fun term => total es (fun w => total (List.finRange 28) (fun i =>
          if term.1 == (i.val,w) then f i.val w term.2 else 0))) := by
      simp only [total_swap (List.finRange 28) x.toList]
      exact total_swap es x.toList _
    _ = total x.toList (fun term => f term.1.1 term.1.2 term.2) := by
      apply total_congr_mem
      rintro ⟨⟨a,w0⟩,p⟩ hm
      have ha := hx ((a,w0),p) hm
      let a' : Fin 28 := ⟨a,ha.1⟩
      have heq (w : Nat) (i : Fin 28) :
          (if (a,w0) == (i.val,w) then f i.val w p else 0) =
          if w = w0 then (if i = a' then f a w0 p else 0) else 0 := by
        have hi : i.val = a ↔ i = a' := ⟨fun h => Fin.ext h, congrArg Fin.val⟩
        simp only [beq_iff_eq, Prod.mk.injEq]
        split <;> split <;> (try split) <;> grind
      simp only [heq]
      have hin (w : Nat) : total (List.finRange 28)
          (fun i => if w = w0 then (if i = a' then f a w0 p else 0) else 0) =
          if w = w0 then f a w0 p else 0 := by
        by_cases hw : w = w0
        · simp only [if_pos hw]
          have hamem : a' ∈ List.finRange 28 := List.mem_ofFn.mpr ⟨a',rfl⟩
          rw [total_delta _ (by decide) a', if_pos hamem]
        · simp only [if_neg hw, total_zero]
      simp only [hin]
      rw [total_delta es hnd w0, if_pos ha.2]

theorem total_range28 (f : Nat → Poly) :
    total (List.range 28) f = total (List.finRange 28) (fun i => f i.val) := by
  have h : List.range 28 = (List.finRange 28).map Fin.val := by decide
  rw [h, total_map]

/-- Full three-index formula for the executable contraction. -/
theorem pairColumns_full (left right : Column) (matrix : SmallMatrix)
    (es : List Nat) (hnd : es.Nodup)
    (hleft : ∀ term ∈ left.toList, term.1.1 < 28 ∧ term.1.2 ∈ es) :
    ofList (pairColumns left right matrix) =
      total es (fun w => total (List.finRange 28) (fun i => total (List.finRange 28) (fun k =>
        ofList (left.getD (i.val,w) []) * ofList (entry matrix i.val k.val) *
          ofList (right.getD (k.val,w) [])))) := by
  rw [pairColumns_sparse left right matrix (fun term ht => (hleft term ht).1)]
  rw [column_total_coordinates left es hnd hleft
    (fun i w p => total (List.range 28) (fun k =>
      ofList p * ofList (entry matrix i k) * ofList (right.getD (k,w) [])))
    (by intro i w; simp)]
  simp only [total_range28]

end WebMu.Revised.NormContraction
