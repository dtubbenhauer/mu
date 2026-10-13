import WebMu.Revised.Bar
import WebMu.Revised.GrowthBridge
import WebMu.Revised.SupportBounds
import WebMu.Revised.NormBoundary

/-! Generic coefficient semantics of sparse circuit combinators.
These are implementation theorems with no reference assumptions. -/
namespace WebMu.Revised.Bar
open Laurent Algebra GrowthBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem bindSparse_poly (x : Tensor) (f : Word → Tensor) (w : Word) :
    ofList ((bindSparse x f).getD w []) =
      total x.toList (fun (u,p) => ofList ((f u).getD w []) * ofList p) := by
  have inner (u : Word) (p : Laurent) (acc : Tensor) :
      ofList (((f u).fold (fun result v q => accumulate result v (Laurent.mul q p)) acc).getD w []) =
        ofList (acc.getD w []) + ofList ((f u).getD w []) * ofList p := by
    rw [Std.HashMap.fold_eq_foldl_toList, fold_accumulate_poly]
    congr 1
    calc
      total (f u).toList (fun z => if z.1 == w then ofList (Laurent.mul z.2 p) else 0) =
        ofList (Laurent.mul ((f u).getD w []) p) :=
          hashmap_total_lookup (f u) w (fun q => ofList (Laurent.mul q p)) rfl
      _ = _ := ofList_mul _ _
  have outer (xs : List (Word × Laurent)) (acc : Tensor) :
      ofList ((xs.foldl (fun out z => (f z.1).fold
        (fun result v q => accumulate result v (Laurent.mul q z.2)) out) acc).getD w []) =
      ofList (acc.getD w []) + total xs (fun (u,p) => ofList ((f u).getD w []) * ofList p) := by
    induction xs generalizing acc with
    | nil => simp
    | cons z zs ih => simp only [List.foldl_cons, ih, inner, total_cons, poly_add_assoc]
  unfold bindSparse
  rw [Std.HashMap.fold_eq_foldl_toList, outer]
  simp

def tensorFold (x y : Tensor) : Tensor :=
  x.toList.foldl (fun out up => y.toList.foldl
    (fun out wq => accumulate out (up.1 ++ wq.1) (Laurent.mul up.2 wq.2)) out) ∅

theorem tensorProduct_eq_fold (x y : Tensor) : tensorProduct x y = tensorFold x y := by
  unfold tensorProduct tensorFold
  simp only [Std.HashMap.forIn_eq_forIn_toList, pure_bind]
  dsimp only [Id.run, Bind.bind, Pure.pure]
  simp only [id_forIn_yield]

theorem tensorProduct_poly (x y : Tensor) (w : Word) :
    ofList ((tensorProduct x y).getD w []) =
      total x.toList (fun (u,p) => total y.toList (fun (v,q) =>
        if u++v == w then ofList p * ofList q else 0)) := by
  have outer (xs : List (Word × Laurent)) (acc : Tensor) :
      ofList ((xs.foldl (fun out up => y.toList.foldl
        (fun out vq => accumulate out (up.1++vq.1) (Laurent.mul up.2 vq.2)) out) acc).getD w []) =
      ofList (acc.getD w []) + total xs (fun (u,p) => total y.toList (fun (v,q) =>
        if u++v == w then ofList p * ofList q else 0)) := by
    induction xs generalizing acc with
    | nil => simp
    | cons z zs ih =>
      simp only [List.foldl_cons, ih, fold_accumulate_poly, total_cons, ofList_mul, poly_add_assoc]
  rw [tensorProduct_eq_fold]
  unfold tensorFold
  rw [outer]
  simp

/-- Sparse support, coefficientwise so stored zero values do not matter. -/
def Supported (n : Nat) (x : Tensor) : Prop :=
  ∀ w, ofList (x.getD w []) ≠ 0 → validWord n w = true

theorem total_eq_zero_of_each {α : Type} (xs : List α) (f : α → Poly)
    (h : ∀ x ∈ xs, f x = 0) : total xs f = 0 := by
  rw [total_congr_mem xs f (fun _ => 0) h]
  exact total_zero xs

theorem bindSparse_supported (n : Nat) (x : Tensor) (f : Word → Tensor)
    (h : ∀ u, Supported n (f u)) : Supported n (bindSparse x f) := by
  intro w hw
  by_cases hv : validWord n w = true
  · exact hv
  · apply False.elim
    apply hw
    rw [bindSparse_poly]
    apply total_eq_zero_of_each
    rintro ⟨u,p⟩ _
    have hz : ofList ((f u).getD w []) = 0 := by
      by_cases hz : ofList ((f u).getD w []) = 0
      · exact hz
      · exact False.elim (hv (h u w hz))
    simpa only [hz,poly_zero_mul]

theorem singleton_poly (u w : Word) (p : Laurent) :
    ofList ((singleton u p).getD w []) = if u=w then ofList p else 0 := by
  by_cases h : u = w <;> simp [singleton, Std.HashMap.getD_insert, beq_iff_eq,h]


def completeWords (n : Nat) : List Word :=
  (List.finRange (3^n)).map (fun i => decodeWord n i.val)

theorem decode_valid (n a : Nat) : validWord n (decodeWord n a) = true := by
  exact (Revised.validWord_iff _ _).mpr ⟨ShortNorm.decode_length _ _,ShortNorm.decode_ternary _ _⟩

theorem completeWords_mem (n : Nat) (w : Word) : w ∈ completeWords n ↔ validWord n w = true := by
  constructor
  · intro h
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    exact decode_valid _ _
  · intro h
    obtain ⟨hl,ht⟩ := (Revised.validWord_iff n w).mp h
    let i : Fin (3^n) := ⟨encode w,by simpa [hl] using ShortNorm.encode_bound w ht⟩
    apply List.mem_map.mpr
    refine ⟨i,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    exact hl ▸ decodeWord_encode w ht

theorem completeWords_nodup (n : Nat) : (completeWords n).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij he
  simp only [completeWords,List.length_map,List.length_finRange] at hi hj
  simp only [completeWords,List.getElem_map,List.getElem_finRange] at he
  have hh := congrArg encode he
  change encode (decodeWord n i) = encode (decodeWord n j) at hh
  rw [ShortNorm.encode_decode n i hi,ShortNorm.encode_decode n j hj] at hh
  omega

theorem entry_lookup (x : Tensor) (w : Word) (p : Laurent) (h : (w,p) ∈ x.toList) :
    x.getD w [] = p := by
  have he := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp h
  simp [Std.HashMap.getD_eq_getD_getElem?,he]

theorem weighted_sparse_reindex (x : Tensor) (ws : List Word) (hnd : ws.Nodup)
    (h : ∀ w, ofList (x.getD w []) ≠ 0 → w ∈ ws) (f : Word → Poly) :
    total x.toList (fun (w,p) => f w * ofList p) =
      total ws (fun w => f w * ofList (x.getD w [])) := by
  symm
  calc
    total ws (fun w => f w * ofList (x.getD w [])) =
        total ws (fun w => total x.toList (fun (u,p) => if u == w then f w * ofList p else 0)) := by
      apply total_congr_mem
      intro w _
      exact (hashmap_total_lookup x w (fun p => f w * ofList p) (poly_mul_zero _)).symm
    _ = total x.toList (fun (u,p) => total ws (fun w => if u == w then f w * ofList p else 0)) :=
      total_swap _ _ _
    _ = total x.toList (fun (w,p) => f w * ofList p) := by
      apply total_congr_mem
      rintro ⟨u,p⟩ hm
      dsimp only
      by_cases hp : ofList p = 0
      · simp only [hp,poly_mul_zero]
        exact total_eq_zero_of_each _ _ (by intro w _; split <;> rfl)
      · have hu : u ∈ ws := h u (by rw [entry_lookup x u p hm]; exact hp)
        have he (w : Word) : (if u == w then f w * ofList p else 0) =
            if w=u then f u * ofList p else 0 := by
          by_cases hw : w=u <;> simp [hw,Ne.symm]
        simp only [he]
        rw [total_delta ws hnd u,if_pos hu]

theorem bindSparse_dense (n : Nat) (x : Tensor) (f : Word → Tensor) (w : Word)
    (hx : Supported n x) :
    ofList ((bindSparse x f).getD w []) =
      total (List.finRange (3^n)) (fun i =>
        ofList ((f (decodeWord n i.val)).getD w []) *
          ofList (x.getD (decodeWord n i.val) [])) := by
  rw [bindSparse_poly,weighted_sparse_reindex x (completeWords n) (completeWords_nodup n)
    (fun u hu => (completeWords_mem n u).mpr (hx u hu))
    (fun u => ofList ((f u).getD w [])),completeWords,total_map]


theorem applyStep_dense (n : Nat) (x : Tensor) (step : Step) (w : Word)
    (hx : Supported n x) :
    ofList ((applyStep x step).getD w []) =
      total (List.finRange (3^n)) (fun i =>
        transitionCoefficient (transitions step) (decodeWord n i.val) w *
          ofList (x.getD (decodeWord n i.val) [])) := by
  rw [applyStep_poly]
  calc
    total x.toList (fun (u,p) => ofList p * transitionCoefficient (transitions step) u w) =
      total x.toList (fun (u,p) => transitionCoefficient (transitions step) u w * ofList p) := by
        apply total_congr_mem
        rintro ⟨u,p⟩ _
        exact poly_mul_comm _ _
    _ = _ := by
      rw [weighted_sparse_reindex x (completeWords n) (completeWords_nodup n)
        (fun u hu => (completeWords_mem n u).mpr (hx u hu))
        (fun u => transitionCoefficient (transitions step) u w),completeWords,total_map]


theorem tensorProduct_split (n : Nat) (x y : Tensor) (u v : Word)
    (hx : Supported n x) (hu : u.length = n) :
    ofList ((tensorProduct x y).getD (u++v) []) =
      ofList (x.getD u []) * ofList (y.getD v []) := by
  rw [tensorProduct_poly]
  calc
    total x.toList (fun (a,p) => total y.toList (fun (b,q) =>
      if a++b == u++v then ofList p * ofList q else 0)) =
      total x.toList (fun (a,p) => if a == u then ofList p * ofList (y.getD v []) else 0) := by
      apply total_congr_mem
      rintro ⟨a,p⟩ hm
      dsimp only
      by_cases hp : ofList p = 0
      · simp only [hp,poly_zero_mul]
        rw [total_eq_zero_of_each y.toList _ (by intro z _; split <;> rfl)]
        split <;> rfl
      · have ha : a.length = n := ((Revised.validWord_iff n a).mp
          (hx a (by rw [entry_lookup x a p hm];exact hp))).1
        by_cases he : a=u
        · subst a
          simp only [beq_self_eq_true,↓reduceIte,beq_iff_eq,List.append_right_inj]
          simpa only [beq_iff_eq] using
            hashmap_total_lookup y v (fun q => ofList p * ofList q) (poly_mul_zero _)
        · have hab (b : Word) : a++b ≠ u++v := fun heq =>
            he (List.append_inj_left heq (ha.trans hu.symm))
          simp only [beq_iff_eq,he,↓reduceIte]
          exact total_eq_zero_of_each y.toList _ (by rintro ⟨b,q⟩ _; simp [hab b])
    _ = _ := hashmap_total_lookup x u (fun p => ofList p * ofList (y.getD v [])) (poly_zero_mul _)

theorem validWord_append_local {n m : Nat} {u v : Word}
    (hu : validWord n u = true) (hv : validWord m v = true) :
    validWord (n+m) (u++v) = true := by
  obtain ⟨hul,hut⟩ := (Revised.validWord_iff n u).mp hu
  obtain ⟨hvl,hvt⟩ := (Revised.validWord_iff m v).mp hv
  apply (Revised.validWord_iff _ _).mpr
  constructor
  · simp [hul,hvl]
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hut a ha
    · exact hvt a ha

theorem tensorProduct_supported (n m : Nat) (x y : Tensor)
    (hx : Supported n x) (hy : Supported m y) : Supported (n+m) (tensorProduct x y) := by
  intro w hw
  by_cases hv : validWord (n+m) w = true
  · exact hv
  · apply False.elim
    apply hw
    rw [tensorProduct_poly]
    apply total_eq_zero_of_each
    rintro ⟨a,p⟩ hp
    apply total_eq_zero_of_each
    rintro ⟨b,q⟩ hq
    dsimp only
    by_cases hz : ofList p = 0
    · simp [hz]
    by_cases hzq : ofList q = 0
    · simp [hzq]
    have ha := hx a (by rw [entry_lookup x a p hp];exact hz)
    have hb := hy b (by rw [entry_lookup y b q hq];exact hzq)
    have hab : a++b ≠ w := by
      intro he
      exact hv (he ▸ validWord_append_local ha hb)
    simp [hab]


theorem bindSparse_supported_input (n m : Nat) (x : Tensor) (f : Word → Tensor)
    (hx : Supported n x) (hf : ∀ u, validWord n u = true → Supported m (f u)) :
    Supported m (bindSparse x f) := by
  intro w hw
  by_cases hv : validWord m w = true
  · exact hv
  · apply False.elim
    apply hw
    rw [bindSparse_dense n x f w hx]
    apply total_eq_zero_of_each
    intro i _
    have hz : ofList ((f (decodeWord n i.val)).getD w []) = 0 := by
      by_cases hz : ofList ((f (decodeWord n i.val)).getD w []) = 0
      · exact hz
      · exact False.elim (hv (hf _ (decode_valid n i.val) w hz))
    rw [hz,poly_zero_mul]

end WebMu.Revised.Bar
