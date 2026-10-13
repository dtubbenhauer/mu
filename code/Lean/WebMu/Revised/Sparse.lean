import WebMu.RevisedLocal
import WebMu.Revised.Gauge

namespace WebMu.Revised
open Laurent Algebra

set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[simp] theorem ofList_empty : ofList [] = (0 : Poly) := rfl

theorem total_congr_mem {ι : Type} (is : List ι) (f g : ι → Poly)
    (h : ∀ i ∈ is, f i = g i) : total is f = total is g := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [total_cons, h i (by simp), ih (by intro j hj; exact h j (by simp [hj]))]

theorem accumulate_poly {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (k q : α) (v : Laurent) :
    ofList ((accumulate x k v).getD q []) =
      ofList (x.getD q []) + if k == q then ofList v else 0 := by
  by_cases h : (add (x.getD k []) v).isEmpty = true
  · simp only [accumulate, h, Bool.false_eq_true, ↓reduceIte]

    have he : add (x.getD k []) v = [] := List.isEmpty_iff.mp h
    rw [Std.HashMap.getD_erase]
    by_cases hk : k = q
    · subst q
      simp only [beq_self_eq_true, ↓reduceIte]
      exact (ofList_add _ _).symm.trans (congrArg ofList he) |>.symm
    · simp [hk]
  · simp only [accumulate, h, Bool.false_eq_true, ↓reduceIte]
    rw [Std.HashMap.getD_insert]
    by_cases hk : k = q
    · subst q; simp
    · simp [hk]

theorem fold_accumulate_poly {α ι : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (is : List ι) (key : ι → α) (value : ι → Laurent)
    (x : Std.HashMap α Laurent) (q : α) :
    ofList ((is.foldl (fun out i => accumulate out (key i) (value i)) x).getD q []) =
      ofList (x.getD q []) + total is (fun i => if key i == q then ofList (value i) else 0) := by
  induction is generalizing x with
  | nil => simp [List.foldl_nil]
  | cons i is ih =>
    simp only [List.foldl_cons, ih, accumulate_poly, total_cons, poly_add_assoc]

theorem hashmap_fold_poly {α κ : Type} [BEq α] [Hashable α] [LawfulBEq α]
    [BEq κ] [Hashable κ] (x : Std.HashMap κ Laurent)
    (key : κ → α) (value : κ → Laurent → Laurent) (q : α) :
    ofList ((x.fold (fun out k p => accumulate out (key k) (value k p)) ∅).getD q []) =
      total x.toList (fun (k,p) => if key k == q then ofList (value k p) else 0) := by
  rw [Std.HashMap.fold_eq_foldl_toList, fold_accumulate_poly]
  simp

theorem hashmap_total_lookup {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (q : α) (f : Laurent → Poly) (hz : f [] = 0) :
    total x.toList (fun (k,p) => if k == q then f p else 0) = f (x.getD q []) := by
  classical
  have hnd : x.toList.Nodup := by
    apply List.Pairwise.imp _ x.distinct_keys_toList
    intro a b hab he
    subst b
    simpa using hab
  have hf : total x.toList (fun (k,p) => if k == q then f p else 0) =
      total x.toList (fun z => if z = (q,x.getD q []) then f (x.getD q []) else 0) := by
    apply total_congr_mem
    rintro ⟨k,p⟩ hm
    by_cases hk : k = q
    · subst k
      have he : x[q]? = some p := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm
      have hp : x.getD q [] = p := by simp [Std.HashMap.getD_eq_getD_getElem?, he]
      simp [hp]
    · simp [hk]
  rw [hf, total_delta _ hnd]
  split
  · rfl
  next h =>
    have hn : x[q]? = none := by
      cases he : x[q]? with
      | none => rfl
      | some p =>
        have hp : x.getD q [] = p := by simp [Std.HashMap.getD_eq_getD_getElem?, he]
        exact False.elim (h (by apply Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr; simpa [hp] using he))
    simp [Std.HashMap.getD_eq_getD_getElem?, hn, hz]

def scaleMap {α : Type} [BEq α] [Hashable α]
    (x : Std.HashMap α Laurent) (a : Laurent) : Std.HashMap α Laurent :=
  x.fold (fun out k p => accumulate out k (mul p a)) ∅

def addMap {α : Type} [BEq α] [Hashable α]
    (x y : Std.HashMap α Laurent) : Std.HashMap α Laurent :=
  y.fold (fun out k p => accumulate out k p) x

def sumMap {α : Type} [BEq α] [Hashable α]
    (xs : List (Std.HashMap α Laurent)) : Std.HashMap α Laurent := xs.foldl addMap ∅

theorem scaleMap_poly {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (a : Laurent) (q : α) :
    ofList ((scaleMap x a).getD q []) = ofList (x.getD q []) * ofList a := by
  rw [scaleMap, hashmap_fold_poly]
  exact hashmap_total_lookup x q (fun p => ofList (mul p a)) rfl

theorem addMap_poly {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x y : Std.HashMap α Laurent) (q : α) :
    ofList ((addMap x y).getD q []) = ofList (x.getD q []) + ofList (y.getD q []) := by
  rw [addMap, Std.HashMap.fold_eq_foldl_toList, fold_accumulate_poly]
  rw [hashmap_total_lookup y q ofList rfl]

theorem sumMap_poly {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (xs : List (Std.HashMap α Laurent)) (q : α) :
    ofList ((sumMap xs).getD q []) = total xs (fun x => ofList (x.getD q [])) := by
  have hf (xs : List (Std.HashMap α Laurent)) (x : Std.HashMap α Laurent) :
      ofList ((xs.foldl addMap x).getD q []) =
      ofList (x.getD q []) + total xs (fun x => ofList (x.getD q [])) := by
    induction xs generalizing x with
    | nil => simp
    | cons y ys ih => simp only [List.foldl_cons, ih, addMap_poly, total_cons, poly_add_assoc]
  rw [sumMap, hf]
  simp

def getRow (x : Column) (i : Nat) : Std.HashMap Nat Laurent :=
  x.fold (fun out (j,w) p => accumulate out w (if j = i then p else [])) ∅

def putRow (x : Std.HashMap Nat Laurent) (i : Nat) : Column :=
  x.fold (fun out w p => accumulate out (i,w) p) ∅

theorem getRow_poly (x : Column) (i w : Nat) :
    ofList ((getRow x i).getD w []) = ofList (x.getD (i,w) []) := by
  rw [getRow, hashmap_fold_poly]
  have hf : total x.toList (fun (k,p) => if k.2 == w then ofList (if k.1 = i then p else []) else 0) =
      total x.toList (fun (k,p) => if k == (i,w) then ofList p else 0) := by
    apply total_congr_mem
    rintro ⟨⟨j,v⟩,p⟩ _
    by_cases hj : j = i <;> by_cases hv : v = w <;> simp [hj,hv]
  rw [hf, hashmap_total_lookup x (i,w) ofList rfl]

theorem putRow_poly (x : Std.HashMap Nat Laurent) (i j w : Nat) :
    ofList ((putRow x i).getD (j,w) []) =
      if i = j then ofList (x.getD w []) else 0 := by
  rw [putRow, hashmap_fold_poly]
  by_cases hij : i = j
  · subst j
    simpa using hashmap_total_lookup x w ofList rfl
  · have hf : total x.toList (fun (v,p) => if (i,v) == (j,w) then ofList p else 0) =
        total x.toList (fun _ => 0) := by
      apply total_congr_mem
      rintro ⟨v,p⟩ _
      simp [hij]
    simpa [hij, hf]

theorem total_map {ι κ : Type} (is : List ι) (f : ι → κ) (g : κ → Poly) :
    total (is.map f) g = total is (fun i => g (f i)) := by
  induction is <;> simp_all

def denseRight {α : Type} [BEq α] [Hashable α]
    (a : Nat → Nat → Laurent) (cols : Nat → Std.HashMap α Laurent) (j : Nat) :
    Std.HashMap α Laurent :=
  sumMap ((List.finRange 28).map (fun (k : Fin 28) =>
    if (a k j).isEmpty then ∅ else scaleMap (cols k) (a k j)))

def denseLeft (a : Nat → Nat → Laurent) (x : Column) : Column :=
  sumMap ((List.finRange 28).map fun (i : Fin 28) =>
    putRow (sumMap ((List.finRange 28).map fun (k : Fin 28) =>
      if (a i k).isEmpty then ∅ else scaleMap (getRow x k) (a i k))) i)

theorem guardedScale_poly {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (a : Laurent) (q : α) :
    ofList ((if a.isEmpty then ∅ else scaleMap x a).getD q []) =
      ofList (x.getD q []) * ofList a := by
  by_cases ha : a = []
  · simp [ha]
  · have hh : a.isEmpty = false := by simpa using ha
    simp [hh, scaleMap_poly]

theorem denseRight_poly {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (a : Nat → Nat → Laurent) (cols : Nat → Std.HashMap α Laurent) (j : Nat) (q : α) :
    ofList ((denseRight a cols j).getD q []) =
      total (List.finRange 28) (fun k => ofList ((cols k).getD q []) * ofList (a k j)) := by
  simp only [denseRight, sumMap_poly, total_map, guardedScale_poly]

theorem denseLeft_poly (a : Nat → Nat → Laurent) (x : Column) (i : Fin 28) (w : Nat) :
    ofList ((denseLeft a x).getD (i.val,w) []) =
      total (List.finRange 28) (fun k => ofList (a i k) * ofList (x.getD (k.val,w) [])) := by
  simp only [denseLeft, sumMap_poly, total_map, putRow_poly, guardedScale_poly, getRow_poly]
  have hf : total (List.finRange 28)
      (fun j => if j.val = i.val then
        total (List.finRange 28) (fun k => ofList (x.getD (k.val,w) []) * ofList (a j k)) else 0) =
      total (List.finRange 28) (fun j => if j = i then
        total (List.finRange 28) (fun k => ofList (a i k) * ofList (x.getD (k.val,w) [])) else 0) := by
    apply total_congr_mem
    intro j _
    by_cases hj : j = i
    · subst j; simp [poly_mul_comm]
    · have hn : j.val ≠ i.val := fun h => hj (Fin.ext h)
      simp [hj,hn]
  rw [hf, total_delta _ (by decide)]
  have hi : ∀ j : Fin 28, j ∈ List.finRange 28 := by decide
  simp [hi i]

end WebMu.Revised
