import WebMu.Revised.CircuitSparseSemantics
import WebMu.Revised.GrowthAdjoint

/-! Uncollected monomial paths through the elementary tensor tables.
A path retains every intermediate word and every chosen exponent and integer
multiplicity. No identical endpoints are merged during enumeration. -/
namespace WebMu.Revised.LocalPaths
open Laurent Algebra GrowthBridge Bar
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Edge where
  output : Word
  degree : Int
  multiplicity : Int
  deriving Repr, BEq, DecidableEq

structure Path where
  input : Word
  output : Word
  edges : List Edge
  degree : Int
  multiplicity : Int
  deriving Repr, BEq, DecidableEq

def initial (u : Word) : Path := ⟨u,u,[],0,1⟩
def extend (p : Path) (e : Edge) : Path :=
  ⟨p.input,e.output,p.edges ++ [e],p.degree+e.degree,p.multiplicity*e.multiplicity⟩

def branches (s : Step) (u : Word) : List Edge :=
  (transitions s u).flatMap fun (w,q) => q.map fun (d,c) => ⟨w,d,c⟩

def advance (s : Step) (ps : List Path) : List Path :=
  ps.flatMap fun p => (branches s p.output).map (extend p)

def paths (upward : List Step) (u : Word) : List Path :=
  upward.foldl (fun ps s => advance s ps) [initial u]

def downPaths (downward : List Step) (u : Word) : List Path :=
  paths downward.reverse u

def pathTensor (ps : List Path) : Tensor :=
  ps.foldl (fun x p => accumulate x p.output (monomial p.degree p.multiplicity)) ∅

def pathValue (p : Path) : Poly := ofList (monomial p.degree p.multiplicity)

theorem monomial_mul (d e a b : Int) :
    ofList (monomial (d+e) (a*b)) =
      ofList (monomial d a) * ofList (monomial e b) := by
  apply poly_ext
  intro k
  simp only [← ofList_mul,coefficient_ofList]
  by_cases ha : a=0
  · simp [monomial,ha,mul,coeff]
  by_cases hb : b=0
  · simp [monomial,ha,hb,mul,shiftScale,coeff,add]
  have hab : a*b ≠ 0 := Int.mul_ne_zero ha hb
  simp [monomial,ha,hb,hab,mul,shiftScale,coeff,add,Int.mul_comm,Int.add_comm]

theorem monomial_sum (q : Laurent) :
    ofList q = total q (fun (d,c) => ofList (monomial d c)) := by
  induction q with
  | nil => rfl
  | cons z q ih =>
    rw [total_cons,← ih]
    apply poly_ext
    intro k
    rcases z with ⟨d,c⟩
    by_cases hc : c=0 <;> simp [coeff,monomial,hc]

theorem branches_sum (s : Step) (u w : Word) :
    total (branches s u) (fun e => if e.output == w then
      ofList (monomial e.degree e.multiplicity) else 0) =
    transitionCoefficient (transitions s) u w := by
  unfold branches transitionCoefficient
  rw [GrowthAdjoint.total_flatMap]
  apply total_congr_mem
  rintro ⟨v,q⟩ _
  rw [total_map]
  by_cases hv : v == w
  · simp only [hv,↓reduceIte]
    exact (monomial_sum q).symm
  · simp [hv]

theorem pathTensor_poly (ps : List Path) (w : Word) :
    ofList ((pathTensor ps).getD w []) =
      total ps (fun p => if p.output == w then pathValue p else 0) := by
  unfold pathTensor pathValue
  rw [fold_accumulate_poly]
  simp

theorem weighted_pathTensor (ps : List Path) (f : Word → Poly) :
    total (pathTensor ps).toList (fun (u,q) => f u * ofList q) =
      total ps (fun p => f p.output * pathValue p) := by
  let ws := TruncatedGrowth.dedup (ps.map Path.output)
  have hm (p : Path) (hp : p ∈ ps) : p.output ∈ ws := by
    exact TruncatedGrowth.mem_dedup _ _ |>.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hs (u : Word) (hu : ofList ((pathTensor ps).getD u []) ≠ 0) : u ∈ ws := by
    by_cases hn : u ∈ ws
    · exact hn
    apply False.elim
    apply hu
    rw [pathTensor_poly]
    apply total_eq_zero_of_each
    intro p hp
    have hne : p.output ≠ u := fun he => hn (he ▸ hm p hp)
    simp [hne]
  rw [weighted_sparse_reindex _ ws (TruncatedGrowth.dedup_nodup _) hs f]
  simp only [pathTensor_poly,← mul_total]
  rw [total_swap]
  apply total_congr_mem
  intro p hp
  have hf (u : Word) : f u * (if p.output == u then pathValue p else 0) =
      if u = p.output then f p.output * pathValue p else 0 := by
    by_cases he : u=p.output <;> simp [he,Ne.symm]
  simp only [hf]
  rw [total_delta ws (TruncatedGrowth.dedup_nodup _) p.output,if_pos (hm p hp)]

theorem advance_poly (s : Step) (ps : List Path) (w : Word) :
    ofList ((pathTensor (advance s ps)).getD w []) =
      ofList ((applyStep (pathTensor ps) s).getD w []) := by
  rw [pathTensor_poly,applyStep_poly]
  unfold advance
  rw [GrowthAdjoint.total_flatMap]
  have hleft : total ps (fun p => total ((branches s p.output).map (extend p))
      (fun p => if p.output == w then pathValue p else 0)) =
      total ps (fun p => pathValue p * transitionCoefficient (transitions s) p.output w) := by
    apply total_congr_mem
    intro p _
    rw [total_map,← branches_sum s p.output w,← mul_total]
    apply total_congr_mem
    intro e _
    simp only [extend,pathValue]
    rw [monomial_mul]
    split <;> simp_all
  rw [hleft]
  simpa only [poly_mul_comm] using (weighted_pathTensor ps
    (fun u => transitionCoefficient (transitions s) u w)).symm

/-- Sparse map equality is coefficient equality; it does not assume canonical storage. -/
def TensorEq (x y : Tensor) : Prop := ∀ w, ofList (x.getD w []) = ofList (y.getD w [])

theorem applyStep_congr (s : Step) (x y : Tensor) (h : TensorEq x y) :
    TensorEq (applyStep x s) (applyStep y s) := by
  intro w
  apply poly_ext
  intro d
  have hh : TruncatedGrowth.MapAgreeFrom d x y := by
    intro u k _
    exact congrArg (fun p => coefficient p k) (h u)
  simp only [applyStep_eq_linearMap]
  exact TruncatedGrowth.linearMap_agrees (transitions s) d (opBound s.1) x y
    (transitions_bounded s) (fun u k _ => congrArg (fun p => coefficient p k) (h u)) w d
      (Int.le_refl _) |>.trans (Eq.refl _)

 theorem paths_poly_aux (ss : List Step) (ps : List Path) (x : Tensor)
    (h : TensorEq (pathTensor ps) x) :
    TensorEq (pathTensor (ss.foldl (fun ps s => advance s ps) ps)) (compose ss x) := by
  induction ss generalizing ps x with
  | nil => exact h
  | cons s ss ih =>
    apply ih
    intro w
    exact (advance_poly s ps w).trans (applyStep_congr s _ _ h w)

theorem paths_poly (ss : List Step) (u w : Word) :
    ofList ((compose ss (singleton u)).getD w []) =
      total (paths ss u) (fun p => if p.output == w then pathValue p else 0) := by
  have h : TensorEq (pathTensor [initial u]) (singleton u) := by
    intro v
    rw [pathTensor_poly,singleton_poly]
    simp [initial,pathValue,one,beq_iff_eq]
  exact (paths_poly_aux ss [initial u] (singleton u) h w).symm.trans (pathTensor_poly _ _)

theorem downPaths_poly (ss : List Step) (u w : Word) :
    ofList ((expand ss (singleton u)).getD w []) =
      total (downPaths ss u) (fun p => if p.output == w then pathValue p else 0) :=
  paths_poly ss.reverse u w


def pathCoefficient (ps : List Path) (w : Word) (d : Int) : Int :=
  (ps.map fun p => if p.output == w && p.degree == d then p.multiplicity else 0).sum

theorem coefficient_total {α : Type} (xs : List α) (f : α → Poly) (d : Int) :
    coefficient (total xs f) d = (xs.map fun x => coefficient (f x) d).sum := by
  induction xs <;> simp_all

theorem paths_coefficient (ss : List Step) (u w : Word) (d : Int) :
    coeff ((expand ss (singleton u)).getD w []) d =
      pathCoefficient (downPaths ss u) w d := by
  change coefficient (ofList ((expand ss (singleton u)).getD w [])) d = _
  rw [downPaths_poly,coefficient_total]
  unfold pathCoefficient
  congr 1
  apply List.map_congr_left
  intro p _
  by_cases hw : p.output=w <;> by_cases hd : p.degree=d <;>
    by_cases hc : p.multiplicity=0 <;>
    simp [pathValue,monomial,coeff,hw,hd,hc]

theorem paths_degree_bound (ss : List Step) (u : Word) (b : Int)
    (h : ∀ p ∈ downPaths ss u, p.degree ≤ b) (w : Word) (d : Int) (hd : b < d) :
    coeff ((expand ss (singleton u)).getD w []) d = 0 := by
  rw [paths_coefficient]
  unfold pathCoefficient
  have hh : (downPaths ss u).map (fun p =>
      if p.output == w && p.degree == d then p.multiplicity else 0) =
      (downPaths ss u).map (fun _ => (0 : Int)) := by
    apply List.map_congr_left
    intro p hp
    have he : p.degree ≠ d := by have := h p hp; omega
    simp [he]
  rw [hh]
  have hz (xs : List Path) : (xs.map (fun _ => (0 : Int))).sum = 0 := by
    induction xs <;> simp_all
  exact hz _

/-- The stored totals are the sums and products of the chosen elementary data. -/
def degreeTotal : List Edge → Int
  | [] => 0
  | e::es => e.degree + degreeTotal es

def multiplicityTotal : List Edge → Int
  | [] => 1
  | e::es => e.multiplicity * multiplicityTotal es

def Consistent (p : Path) : Prop :=
  p.degree = degreeTotal p.edges ∧ p.multiplicity = multiplicityTotal p.edges

theorem extend_consistent (p : Path) (e : Edge) (h : Consistent p) :
    Consistent (extend p e) := by
  have hd (es : List Edge) : degreeTotal (es ++ [e]) = degreeTotal es + e.degree := by
    induction es <;> simp_all [degreeTotal,Int.add_assoc]
  have hc (es : List Edge) : multiplicityTotal (es ++ [e]) =
      multiplicityTotal es * e.multiplicity := by
    induction es <;> simp_all [multiplicityTotal,Int.mul_assoc]
  simp [Consistent,extend,hd,hc,h.1,h.2]

theorem paths_consistent (ss : List Step) (u : Word) :
    ∀ p ∈ paths ss u, Consistent p := by
  have aux (ss : List Step) (ps : List Path) (h : ∀ p ∈ ps, Consistent p) :
      ∀ p ∈ ss.foldl (fun ps s => advance s ps) ps, Consistent p := by
    induction ss generalizing ps with
    | nil => exact h
    | cons s ss ih =>
      apply ih
      intro p hp
      obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
      exact extend_consistent q e (h q hq)
  apply aux
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  simp [Consistent,initial,degreeTotal,multiplicityTotal]


theorem paths_input (ss : List Step) (u : Word) : ∀ p ∈ paths ss u, p.input = u := by
  have aux (ss : List Step) (ps : List Path) (h : ∀ p ∈ ps, p.input=u) :
      ∀ p ∈ ss.foldl (fun ps s => advance s ps) ps, p.input=u := by
    induction ss generalizing ps with
    | nil => exact h
    | cons s ss ih =>
      apply ih
      intro p hp
      obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
      exact h q hq
  apply aux
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  rfl

theorem pathCoefficient_filter (ps : List Path) (w : Word) (d : Int)
    (f : Path → Bool) (h : ∀ p ∈ ps, p.degree = d → f p = true) :
    pathCoefficient ps w d = pathCoefficient (ps.filter f) w d := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have ih' := ih (fun q hq hd => h q (by simp [hq]) hd)
    by_cases hf : f p = true
    · simpa [pathCoefficient,List.filter_cons,hf] using congrArg
        (fun z => (if p.output == w && p.degree == d then p.multiplicity else 0)+z) ih'
    · have hd : p.degree ≠ d := fun hd => hf (h p (by simp) hd)
      simpa [pathCoefficient,List.filter_cons,hf,hd] using ih'

/-- A pathwise bound need only hold for paths ending at the selected coordinate. -/
theorem paths_coordinate_degree_bound (ss : List Step) (u w : Word) (b : Int)
    (h : ∀ p ∈ downPaths ss u, p.output = w → p.degree ≤ b)
    (d : Int) (hd : b < d) : coeff ((expand ss (singleton u)).getD w []) d = 0 := by
  rw [paths_coefficient]
  have hf : pathCoefficient (downPaths ss u) w d =
      pathCoefficient ((downPaths ss u).filter (fun p => p.degree == d)) w d :=
    pathCoefficient_filter _ w d _ (by intro p _ he; simp [he])
  unfold pathCoefficient
  have hz (ps : List Path) (hh : ∀ p ∈ ps, p.output = w → p.degree ≤ b) :
      (ps.map (fun p => if p.output == w && p.degree == d then p.multiplicity else 0)).sum = 0 := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      have hx : ¬(p.output=w ∧ p.degree=d) := by
        intro ⟨hw,he⟩
        have hb := hh p (by simp) hw
        omega
      have ht := ih (by intro q hq; exact hh q (by simp [hq]))
      simp only [List.map_cons,List.sum_cons,ht,Int.add_zero]
      simp only [Bool.and_eq_true,beq_iff_eq,if_neg hx]
  exact hz _ h


theorem pathCoefficient_filter_at (ps : List Path) (w : Word) (d : Int)
    (f : Path → Bool) (h : ∀ p ∈ ps, p.output = w → p.degree = d → f p = true) :
    pathCoefficient ps w d = pathCoefficient (ps.filter f) w d := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have ih' := ih (fun q hq hw hd => h q (by simp [hq]) hw hd)
    by_cases hf : f p = true
    · simpa [pathCoefficient,List.filter_cons,hf] using congrArg
        (fun z => (if p.output == w && p.degree == d then p.multiplicity else 0)+z) ih'
    · have hn : ¬(p.output=w ∧ p.degree=d) := fun ⟨hw,hd⟩ => hf (h p (by simp) hw hd)
      simpa [pathCoefficient,List.filter_cons,hf,Bool.and_eq_true,beq_iff_eq,hn] using ih'

end WebMu.Revised.LocalPaths
