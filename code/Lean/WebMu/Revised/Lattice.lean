import WebMu.LaurentProofs

/-! The polynomial lattice used by the revised local proof.
All degrees below are v-degrees; t = v⁻¹.  This file uses no literature
axioms and no native decision procedure. -/
namespace WebMu.Revised
open Laurent

/-- Syntactic membership in Z[t], sufficient even for unnormalised lists. -/
def Nonpositive (p : Laurent) : Prop :=
  p.all (fun term => term.1 ≤ 0) = true

instance (p : Laurent) : Decidable (Nonpositive p) := inferInstanceAs
  (Decidable (p.all (fun term => term.1 ≤ 0) = true))

@[simp] theorem nonpositive_nil : Nonpositive [] := rfl

@[simp] theorem nonpositive_cons (i a : Int) (p : Laurent) :
    Nonpositive ((i,a)::p) ↔ i ≤ 0 ∧ Nonpositive p := by
  simp [Nonpositive]

theorem nonpositive_add (p q : Laurent) (hp : Nonpositive p) (hq : Nonpositive q) :
    Nonpositive (add p q) := by
  induction p, q using add.induct with
  | case1 q => simpa [add] using hq
  | case2 p => simpa [add] using hp
  | case3 i a ps j b qs hij ih =>
    rw [nonpositive_cons] at hp
    simp only [add, if_pos hij, nonpositive_cons]
    exact ⟨hp.1, ih hp.2 hq⟩
  | case4 i a ps j b qs hij hji ih =>
    rw [nonpositive_cons] at hq
    simp only [add, if_neg hij, if_pos hji, nonpositive_cons]
    exact ⟨hq.1, ih hp hq.2⟩
  | case5 i a ps j b qs hij hji hab ih =>
    rw [nonpositive_cons] at hp hq
    simp only [add, if_neg hij, if_neg hji, if_pos hab]
    exact ih hp.2 hq.2
  | case6 i a ps j b qs hij hji hab ih =>
    rw [nonpositive_cons] at hp hq
    simp only [add, if_neg hij, if_neg hji, if_neg hab, nonpositive_cons]
    exact ⟨hp.1, ih hp.2 hq.2⟩

theorem nonpositive_shift (p : Laurent) (e c : Int)
    (hp : Nonpositive p) (he : e ≤ 0) : Nonpositive (shiftScale p e c) := by
  by_cases hc : c = 0
  · simp [shiftScale, hc]
  · have hb : (c == 0) = false := by simp [hc]
    induction p with
    | nil => simp [shiftScale, hb]
    | cons term rest ih =>
      rcases term with ⟨i,a⟩
      rw [nonpositive_cons] at hp
      simp only [shiftScale, hb, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        nonpositive_cons]
      exact ⟨by omega, by simpa [shiftScale, hb] using ih hp.2⟩

theorem nonpositive_mul (p q : Laurent) (hp : Nonpositive p) (hq : Nonpositive q) :
    Nonpositive (mul p q) := by
  induction p with
  | nil => exact nonpositive_nil
  | cons term rest ih =>
    rcases term with ⟨i,a⟩
    rw [nonpositive_cons] at hp
    exact nonpositive_add _ _ (nonpositive_shift q i a hq hp.1) (ih hp.2)

theorem nonpositive_sum (ps : List Laurent) (h : ∀ p ∈ ps, Nonpositive p) :
    Nonpositive (Laurent.sum ps) := by
  induction ps with
  | nil => exact nonpositive_nil
  | cons p ps ih =>
    exact nonpositive_add _ _ (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem coeff_positive (p : Laurent) (hp : Nonpositive p) (d : Int) (hd : 0 < d) :
    coeff p d = 0 := by
  induction p with
  | nil => rfl
  | cons term rest ih =>
    rcases term with ⟨i,a⟩
    rw [nonpositive_cons] at hp
    have hi : i ≠ d := by omega
    simp [coeff, hi, ih hp.2]

theorem coeff_mul_zero (p q : Laurent) (hp : Nonpositive p) (hq : Nonpositive q) :
    coeff (mul p q) 0 = coeff p 0 * coeff q 0 := by
  induction p with
  | nil => simp [mul, coeff]
  | cons term rest ih =>
    rcases term with ⟨i,a⟩
    rw [nonpositive_cons] at hp
    rw [mul, coeff_add, coeff_shiftScale, ih hp.2]
    by_cases hi : i = 0
    · simp [coeff, hi, Int.mul_add, Int.mul_comm]
    · have hd : 0 < 0-i := by omega
      rw [coeff_positive q hq (0-i) hd]
      simp [coeff, hi]

/-- The coefficient of t in a product of two integral Laurent polynomials. -/
theorem coeff_mul_neg_one (p q : Laurent) (hp : Nonpositive p) (hq : Nonpositive q) :
    coeff (mul p q) (-1) = coeff p 0 * coeff q (-1) + coeff p (-1) * coeff q 0 := by
  induction p with
  | nil => simp [mul, coeff]
  | cons term rest ih =>
    rcases term with ⟨i,a⟩
    rw [nonpositive_cons] at hp
    rw [mul, coeff_add, coeff_shiftScale, ih hp.2]
    by_cases hz : i = 0
    · subst i
      simp [coeff, Int.add_mul, Int.mul_add, Int.mul_comm, Int.add_assoc, Int.add_left_comm]
    · by_cases ho : i = -1
      · subst i
        simp [coeff, Int.add_mul, Int.mul_add, Int.mul_comm, Int.add_assoc, Int.add_left_comm]
      · have hd : 0 < -1-i := by omega
        rw [coeff_positive q hq (-1-i) hd]
        simp [coeff, hz, ho]

/-- Matrix action; an explicit index list keeps the construction executable. -/
def step {ι : Type} (indices : List ι) (a : ι → ι → Laurent)
    (x : ι → Laurent) (i : ι) : Laurent :=
  Laurent.sum (indices.map (fun j => mul (a i j) (x j)))

def intStep {ι : Type} (indices : List ι) (a : ι → ι → Int)
    (x : ι → Int) (i : ι) : Int :=
  (indices.map (fun j => a i j * x j)).sum

def iterate {ι : Type} (indices : List ι) (a : ι → ι → Laurent)
    (q : ι → Laurent) : Nat → ι → Laurent
  | 0 => q
  | n+1 => step indices a (iterate indices a q n)

def intIterate {ι : Type} (indices : List ι) (a : ι → ι → Int)
    (q : ι → Int) : Nat → ι → Int
  | 0 => q
  | n+1 => intStep indices a (intIterate indices a q n)

theorem step_nonpositive {ι : Type} (indices : List ι) (a : ι → ι → Laurent)
    (x : ι → Laurent) (ha : ∀ i j, Nonpositive (a i j))
    (hx : ∀ i, Nonpositive (x i)) (i : ι) : Nonpositive (step indices a x i) := by
  apply nonpositive_sum
  intro p hp
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
  exact nonpositive_mul _ _ (ha i j) (hx j)

theorem step_constant {ι : Type} (indices : List ι) (a : ι → ι → Laurent)
    (x : ι → Laurent) (ha : ∀ i j, Nonpositive (a i j))
    (hx : ∀ i, Nonpositive (x i)) (i : ι) :
    coeff (step indices a x i) 0 =
      intStep indices (fun i j => coeff (a i j) 0) (fun j => coeff (x j) 0) i := by
  simp only [step, intStep, coeff_sum, List.map_map, Function.comp_def]
  congr 2
  funext j
  exact coeff_mul_zero _ _ (ha i j) (hx j)

theorem step_first_of_zero_constant {ι : Type} (indices : List ι)
    (a : ι → ι → Laurent) (x : ι → Laurent) (ha : ∀ i j, Nonpositive (a i j))
    (hx : ∀ i, Nonpositive (x i)) (hzero : ∀ i, coeff (x i) 0 = 0) (i : ι) :
    coeff (step indices a x i) (-1) =
      intStep indices (fun i j => coeff (a i j) 0) (fun j => coeff (x j) (-1)) i := by
  simp only [step, intStep, coeff_sum, List.map_map, Function.comp_def]
  congr 2
  funext j
  simp [coeff_mul_neg_one _ _ (ha i j) (hx j), hzero]

theorem iterate_nonpositive {ι : Type} (indices : List ι) (a : ι → ι → Laurent)
    (q : ι → Laurent) (ha : ∀ i j, Nonpositive (a i j))
    (hq : ∀ i, Nonpositive (q i)) (m : Nat) (i : ι) :
    Nonpositive (iterate indices a q m i) := by
  induction m generalizing i with
  | zero => exact hq i
  | succ m ih => exact step_nonpositive indices a _ ha ih i

theorem iterate_constant {ι : Type} (indices : List ι) (a : ι → ι → Laurent)
    (q : ι → Laurent) (ha : ∀ i j, Nonpositive (a i j))
    (hq : ∀ i, Nonpositive (q i)) (m : Nat) :
    (fun i => coeff (iterate indices a q m i) 0) =
      intIterate indices (fun i j => coeff (a i j) 0) (fun i => coeff (q i) 0) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i
    rw [iterate, step_constant indices a _ ha (iterate_nonpositive indices a q ha hq m), ih]
    rfl

theorem intStep_zero {ι : Type} (indices : List ι) (a : ι → ι → Int) :
    intStep indices a (fun _ => 0) = fun _ => 0 := by
  funext i
  simp only [intStep, Int.mul_zero]
  induction indices <;> simp_all

theorem intIterate_zero {ι : Type} (indices : List ι) (a : ι → ι → Int) (m : Nat) :
    intIterate indices a (fun _ => 0) m = fun _ => 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [intIterate, ih, intStep_zero]

theorem iterate_zero_constant {ι : Type} (indices : List ι) (a : ι → ι → Laurent)
    (q : ι → Laurent) (ha : ∀ i j, Nonpositive (a i j))
    (hq : ∀ i, Nonpositive (q i)) (hzero : ∀ i, coeff (q i) 0 = 0) (m : Nat) (i : ι) :
    coeff (iterate indices a q m i) 0 = 0 := by
  have hz : (fun i => coeff (q i) 0) = fun _ => 0 := funext hzero
  have h := iterate_constant indices a q ha hq m
  rw [hz, intIterate_zero] at h
  exact congrFun h i

/-- No first-order block terms contribute when the terminal vector is zero modulo t. -/
theorem iterate_first_of_zero_constant {ι : Type} (indices : List ι)
    (a : ι → ι → Laurent) (q : ι → Laurent) (ha : ∀ i j, Nonpositive (a i j))
    (hq : ∀ i, Nonpositive (q i)) (hzero : ∀ i, coeff (q i) 0 = 0) (m : Nat) :
    (fun i => coeff (iterate indices a q m i) (-1)) =
      intIterate indices (fun i j => coeff (a i j) 0) (fun i => coeff (q i) (-1)) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i
    rw [iterate, step_first_of_zero_constant indices a _ ha
      (iterate_nonpositive indices a q ha hq m)
      (iterate_zero_constant indices a q ha hq hzero m), ih]
    rfl

end WebMu.Revised
