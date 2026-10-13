import WebMu.LaurentProofs

/-! Coefficient semantics for the exact Laurent lists and finite contractions.
No representation-theoretic assumption is used in this file. -/
namespace WebMu.Revised.Algebra
open Laurent

def Equiv (p q : Laurent) : Prop := ∀ d, coeff p d = coeff q d

@[refl] theorem equiv_refl (p : Laurent) : Equiv p p := fun _ => rfl
@[symm] theorem equiv_symm {p q : Laurent} (h : Equiv p q) : Equiv q p := fun d => (h d).symm
theorem equiv_trans {p q r : Laurent} (h : Equiv p q) (k : Equiv q r) : Equiv p r :=
  fun d => (h d).trans (k d)

theorem coeff_neg (p : Laurent) (d : Int) : coeff (neg p) d = -coeff p d := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rcases a with ⟨i,c⟩
    simp only [neg, List.map_cons, coeff] at ih ⊢
    rw [ih]
    split <;> omega

theorem coeff_one (d : Int) : coeff one d = if d = 0 then 1 else 0 := by
  simp [one, monomial, coeff, eq_comm]

theorem coeff_mul_cons (p q : Laurent) (j b d : Int) :
    coeff (mul p ((j,b)::q)) d = coeff p (d-j)*b + coeff (mul p q) d := by
  induction p with
  | nil => simp [mul, coeff]
  | cons term p ih =>
    rcases term with ⟨i,a⟩
    simp only [mul, coeff_add, coeff_shiftScale, coeff]
    rw [ih]
    have he : j = d-i ↔ i = d-j := by omega
    simp only [he, Int.add_mul]
    by_cases h : i = d-j <;>
      simp [h, Int.mul_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm]

theorem mul_comm (p q : Laurent) : Equiv (mul p q) (mul q p) := by
  intro d
  induction p with
  | nil =>
    induction q with
    | nil => rfl
    | cons term q ih =>
      rcases term with ⟨j,b⟩
      simp [mul, coeff_add, coeff_shiftScale, coeff] at ih ⊢
      exact ih
  | cons term p ih =>
    rcases term with ⟨i,a⟩
    rw [mul, coeff_add, coeff_shiftScale, coeff_mul_cons, ih]

theorem mul_congr_right (p : Laurent) {q r : Laurent} (h : Equiv q r) :
    Equiv (mul p q) (mul p r) := by
  intro d
  induction p with
  | nil => rfl
  | cons term p ih =>
    rcases term with ⟨i,a⟩
    simp only [mul, coeff_add, coeff_shiftScale, ih]
    rw [h]

theorem mul_congr {p q r s : Laurent} (h : Equiv p q) (k : Equiv r s) :
    Equiv (mul p r) (mul q s) := by
  intro d
  rw [mul_comm p r d, mul_congr_right r h d, mul_comm r q d,
    mul_congr_right q k d]

theorem add_congr {p q r s : Laurent} (h : Equiv p q) (k : Equiv r s) :
    Equiv (add p r) (add q s) := by
  intro d
  rw [coeff_add, coeff_add, h, k]

theorem mul_add (p q r : Laurent) :
    Equiv (mul p (add q r)) (add (mul p q) (mul p r)) := by
  intro d
  induction p with
  | nil => simp [mul, coeff_add, coeff]
  | cons term p ih =>
    rcases term with ⟨i,a⟩
    simp only [mul, coeff_add, coeff_shiftScale, ih, Int.add_mul]
    omega

theorem add_mul (p q r : Laurent) :
    Equiv (mul (add p q) r) (add (mul p r) (mul q r)) := by
  intro d
  rw [mul_comm, mul_add, coeff_add, coeff_add, mul_comm r p d, mul_comm r q d]

theorem coeff_mul_shift_right (p q : Laurent) (e c d : Int) :
    coeff (mul p (shiftScale q e c)) d = coeff (mul p q) (d-e)*c := by
  induction p with
  | nil => simp [mul, coeff]
  | cons term p ih =>
    rcases term with ⟨i,a⟩
    simp only [mul, coeff_add, coeff_shiftScale, ih]
    have he : d-i-e = d-e-i := by omega
    rw [he, Int.add_mul]
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem coeff_mul_shift_left (p q : Laurent) (e c d : Int) :
    coeff (mul (shiftScale p e c) q) d = coeff (mul p q) (d-e)*c := by
  rw [mul_comm, coeff_mul_shift_right, mul_comm q p]

theorem mul_assoc (p q r : Laurent) :
    Equiv (mul (mul p q) r) (mul p (mul q r)) := by
  intro d
  induction p with
  | nil => rfl
  | cons term p ih =>
    rcases term with ⟨i,a⟩
    rw [mul, add_mul, coeff_add, coeff_mul_shift_left, mul, coeff_add, coeff_shiftScale, ih]

theorem mul_one (p : Laurent) : Equiv (mul p one) p := by
  intro d
  rw [mul_comm]
  simp [one, monomial, mul, coeff_add, coeff_shiftScale, coeff]

theorem one_mul (p : Laurent) : Equiv (mul one p) p := by
  intro d
  rw [mul_comm, mul_one]

/-- Laurent polynomials, with different list representations identified by coefficients. -/
instance laurentSetoid : Setoid Laurent where
  r := Equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

abbrev Poly := Quotient laurentSetoid

def ofList (p : Laurent) : Poly := Quotient.mk _ p

def coefficient (p : Poly) (d : Int) : Int :=
  Quotient.liftOn p (fun q => coeff q d) (fun _ _ h => h d)

instance : Zero Poly := ⟨ofList []⟩
instance : One Poly := ⟨ofList one⟩
instance : Add Poly := ⟨fun p q => Quotient.liftOn₂ p q
  (fun a b => ofList (add a b)) (fun _ _ _ _ h k => Quotient.sound (add_congr h k))⟩
instance : Mul Poly := ⟨fun p q => Quotient.liftOn₂ p q
  (fun a b => ofList (mul a b)) (fun _ _ _ _ h k => Quotient.sound (mul_congr h k))⟩

@[simp] theorem coefficient_ofList (p : Laurent) (d : Int) :
    coefficient (ofList p) d = coeff p d := rfl
@[simp] theorem ofList_add (p q : Laurent) : ofList (add p q) = ofList p + ofList q := rfl
@[simp] theorem ofList_mul (p q : Laurent) : ofList (mul p q) = ofList p * ofList q := rfl

theorem poly_ext {p q : Poly} (h : ∀ d, coefficient p d = coefficient q d) : p = q := by
  induction p using Quotient.inductionOn with | _ p =>
  induction q using Quotient.inductionOn with | _ q =>
  exact Quotient.sound h

@[simp] theorem coefficient_zero (d : Int) : coefficient 0 d = 0 := rfl
@[simp] theorem coefficient_add (p q : Poly) (d : Int) :
    coefficient (p+q) d = coefficient p d + coefficient q d := by
  induction p using Quotient.inductionOn with | _ p =>
  induction q using Quotient.inductionOn with | _ q =>
  exact coeff_add p q d

theorem poly_add_assoc (a b c : Poly) : (a+b)+c=a+(b+c) := by
  apply poly_ext; intro d; simp only [coefficient_add]; omega

theorem poly_add_comm (a b : Poly) : a+b=b+a := by
  apply poly_ext; intro d; simp only [coefficient_add]; omega

@[simp] theorem poly_zero_add (a : Poly) : 0+a=a := by
  apply poly_ext; intro d; simp
@[simp] theorem poly_add_zero (a : Poly) : a+0=a := by
  apply poly_ext; intro d; simp

theorem poly_mul_assoc (a b c : Poly) : (a*b)*c=a*(b*c) := by
  induction a using Quotient.inductionOn with | _ a =>
  induction b using Quotient.inductionOn with | _ b =>
  induction c using Quotient.inductionOn with | _ c =>
  exact Quotient.sound (mul_assoc a b c)

theorem poly_mul_comm (a b : Poly) : a*b=b*a := by
  induction a using Quotient.inductionOn with | _ a =>
  induction b using Quotient.inductionOn with | _ b =>
  exact Quotient.sound (mul_comm a b)

theorem poly_mul_add (a b c : Poly) : a*(b+c)=a*b+a*c := by
  induction a using Quotient.inductionOn with | _ a =>
  induction b using Quotient.inductionOn with | _ b =>
  induction c using Quotient.inductionOn with | _ c =>
  exact Quotient.sound (mul_add a b c)

theorem poly_add_mul (a b c : Poly) : (a+b)*c=a*c+b*c := by
  rw [poly_mul_comm, poly_mul_add, poly_mul_comm c a, poly_mul_comm c b]

@[simp] theorem poly_one_mul (a : Poly) : 1*a=a := by
  induction a using Quotient.inductionOn with | _ a =>
  exact Quotient.sound (one_mul a)
@[simp] theorem poly_mul_one (a : Poly) : a*1=a := by rw [poly_mul_comm, poly_one_mul]
@[simp] theorem poly_zero_mul (a : Poly) : 0*a=0 := by
  induction a using Quotient.inductionOn with | _ a => rfl
@[simp] theorem poly_mul_zero (a : Poly) : a*0=0 := by rw [poly_mul_comm, poly_zero_mul]

end WebMu.Revised.Algebra
