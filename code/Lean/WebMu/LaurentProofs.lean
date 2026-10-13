import WebMu.Laurent

namespace WebMu.Laurent

/-- Addition preserves the sum of coefficients, including on unnormalised lists. -/
theorem coeff_add (p q : Laurent) (d : Int) :
    coeff (add p q) d = coeff p d + coeff q d := by
  induction p, q using add.induct with
  | case1 q => simp [add, coeff]
  | case2 p => simp [add, coeff]
  | case3 i a ps j b qs hij ih =>
    simp only [add, if_pos hij, coeff, ih]
    omega
  | case4 i a ps j b qs hij hji ih =>
    simp only [add, if_neg hij, if_pos hji, coeff, ih]
    omega
  | case5 i a ps j b qs hij hji hab ih =>
    have he : i = j := by omega
    subst j
    simp only [add, if_neg hij, if_pos hab, ih, coeff]
    have hc : a + b = 0 := by simpa using hab
    split <;> omega
  | case6 i a ps j b qs hij hji hab ih =>
    have he : i = j := by omega
    subst j
    simp only [add, if_neg hij, if_neg hab, coeff, ih]
    split <;> omega

/-- A monomial shift is the usual shift of the coefficient function. -/
theorem coeff_shiftScale (p : Laurent) (e c d : Int) :
    coeff (shiftScale p e c) d = coeff p (d-e) * c := by
  by_cases hc : c = 0
  · simp [shiftScale, hc, coeff]
  · have hb : (c == 0) = false := by simp [hc]
    induction p with
    | nil => simp [shiftScale, hb, coeff]
    | cons term rest ih =>
      rcases term with ⟨i,a⟩
      have hd : i + e = d ↔ i = d-e := by omega
      simp only [shiftScale, hb, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        coeff, hd] at ih ⊢
      rw [ih, Int.add_mul]
      by_cases hi : i = d-e <;> simp [hi]

def convolution (p q : Laurent) (d : Int) : Int :=
  match p with
  | [] => 0
  | (i,a) :: rest => a * coeff q (d-i) + convolution rest q d

/-- Multiplication implements Laurent coefficient convolution. -/
theorem coeff_mul (p q : Laurent) (d : Int) :
    coeff (mul p q) d = convolution p q d := by
  induction p with
  | nil => rfl
  | cons term rest ih =>
    rcases term with ⟨i,a⟩
    simp [mul, coeff_add, coeff_shiftScale, convolution, ih, Int.mul_comm]

/-- A syntactic support condition implying membership in Z[v^(-2)]. -/
def EvenNonpositive (p : Laurent) : Prop :=
  p.all (fun (d, _) => d ≤ 0 && d % 2 == 0) = true

instance (p : Laurent) : Decidable (EvenNonpositive p) := inferInstanceAs
  (Decidable (p.all (fun (d, _) => d ≤ 0 && d % 2 == 0) = true))

@[simp] theorem support_nil : EvenNonpositive [] := rfl

@[simp] theorem support_cons (i a : Int) (p : Laurent) :
    EvenNonpositive ((i,a)::p) ↔ i ≤ 0 ∧ i % 2 = 0 ∧ EvenNonpositive p := by
  simp [EvenNonpositive, Bool.and_eq_true, and_assoc]

theorem support_add (p q : Laurent) (hp : EvenNonpositive p) (hq : EvenNonpositive q) :
    EvenNonpositive (add p q) := by
  induction p, q using add.induct with
  | case1 q => simpa [add] using hq
  | case2 p => simpa [add] using hp
  | case3 i a ps j b qs hij ih =>
    rw [support_cons] at hp
    simp only [add, if_pos hij, support_cons]
    exact ⟨hp.1, hp.2.1, ih hp.2.2 hq⟩
  | case4 i a ps j b qs hij hji ih =>
    rw [support_cons] at hq
    simp only [add, if_neg hij, if_pos hji, support_cons]
    exact ⟨hq.1, hq.2.1, ih hp hq.2.2⟩
  | case5 i a ps j b qs hij hji hab ih =>
    rw [support_cons] at hp hq
    simp only [add, if_neg hij, if_neg hji, if_pos hab]
    exact ih hp.2.2 hq.2.2
  | case6 i a ps j b qs hij hji hab ih =>
    rw [support_cons] at hp hq
    simp only [add, if_neg hij, if_neg hji, if_neg hab, support_cons]
    exact ⟨hp.1, hp.2.1, ih hp.2.2 hq.2.2⟩

theorem support_shift (p : Laurent) (e c : Int)
    (hp : EvenNonpositive p) (he : e ≤ 0) (heven : e % 2 = 0) :
    EvenNonpositive (shiftScale p e c) := by
  by_cases hc : c = 0
  · simp [shiftScale, hc]
  · have hb : (c == 0) = false := by simp [hc]
    induction p with
    | nil => simp [shiftScale, hb]
    | cons term rest ih =>
      rcases term with ⟨i,a⟩
      rw [support_cons] at hp
      simp only [shiftScale, hb, Bool.false_eq_true, ↓reduceIte, List.map_cons, support_cons]
      exact ⟨by omega, by omega, by simpa [shiftScale, hb] using ih hp.2.2⟩

theorem support_mul (p q : Laurent) (hp : EvenNonpositive p) (hq : EvenNonpositive q) :
    EvenNonpositive (mul p q) := by
  induction p with
  | nil => exact support_nil
  | cons term rest ih =>
    rcases term with ⟨i,a⟩
    rw [support_cons] at hp
    exact support_add _ _ (support_shift q i a hq hp.1 hp.2.1) (ih hp.2.2)

theorem coeff_positive (p : Laurent) (hp : EvenNonpositive p) (d : Int) (hd : 0 < d) :
    coeff p d = 0 := by
  induction p with
  | nil => rfl
  | cons term rest ih =>
    rcases term with ⟨i,a⟩
    rw [support_cons] at hp
    have hi : i ≠ d := by omega
    simp [coeff, hi, ih hp.2.2]

theorem coeff_odd (p : Laurent) (hp : EvenNonpositive p) (d : Int) (hd : d % 2 ≠ 0) :
    coeff p d = 0 := by
  induction p with
  | nil => rfl
  | cons term rest ih =>
    rcases term with ⟨i,a⟩
    rw [support_cons] at hp
    have hi : i ≠ d := by omega
    simp [coeff, hi, ih hp.2.2]

theorem coeff_mul_zero (p q : Laurent) (hp : EvenNonpositive p) (hq : EvenNonpositive q) :
    coeff (mul p q) 0 = coeff p 0 * coeff q 0 := by
  induction p with
  | nil => simp [mul, coeff]
  | cons term rest ih =>
    rcases term with ⟨i,a⟩
    rw [support_cons] at hp
    rw [mul, coeff_add, coeff_shiftScale, ih hp.2.2]
    by_cases hi : i = 0
    · simp [coeff, hi, Int.mul_add, Int.mul_comm]
    · have hd : 0 < 0-i := by omega
      rw [coeff_positive q hq (0-i) hd]
      simp [coeff, hi]

def sum : List Laurent → Laurent
  | [] => []
  | p :: ps => add p (sum ps)

theorem support_sum (ps : List Laurent) (h : ∀ p ∈ ps, EvenNonpositive p) :
    EvenNonpositive (sum ps) := by
  induction ps with
  | nil => exact support_nil
  | cons p ps ih =>
    exact support_add _ _ (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem coeff_sum (ps : List Laurent) (d : Int) :
    coeff (sum ps) d = (ps.map (fun p => coeff p d)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sum, coeff_add, ih]

end WebMu.Laurent
