import WebMu.Local
import WebMu.LaurentProofs

namespace WebMu
open Laurent

abbrev Coordinates := Fin 7 → Laurent
abbrev ConstantCoordinates := Fin 7 → Int

def indices : List (Fin 7) := List.finRange 7
def kEntry (i j : Fin 7) : Laurent := transferData[i.val*7+j.val]!
def aEntry (i : Fin 7) : Laurent := initialData[i.val]!
def bEntry (i : Fin 7) : Laurent := terminalData[i.val]!
def kZero (i j : Fin 7) : Int := constantK[i.val*7+j.val]!
def aZero (i : Fin 7) : Int := constantA[i.val]!
def bZero (i : Fin 7) : Int := constantB[i.val]!

def coordinateStep (x : Coordinates) : Coordinates := fun i =>
  Laurent.sum (indices.map (fun j => mul (kEntry i j) (x j)))

def normCoordinates : Nat → Coordinates
  | 0 => aEntry
  | m+1 => coordinateStep (normCoordinates m)

/-- Exactly b K^m a, with Laurent polynomial arithmetic throughout. -/
def coordinateNorm (m : Nat) : Laurent :=
  Laurent.sum (indices.map (fun i => mul (bEntry i) (normCoordinates m i)))

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem k_support : ∀ i j, EvenNonpositive (kEntry i j) := by decide +kernel
theorem a_support : ∀ i, EvenNonpositive (aEntry i) := by
  simp [aEntry, initialData, pow, mul, add, one, monomial, shiftScale, neg]
  decide +kernel
theorem b_support : ∀ i, EvenNonpositive (bEntry i) := by
  simp [bEntry, terminalData, pow, mul, add, one, monomial, shiftScale, neg]
  decide +kernel
theorem k_constant : ∀ i j, coeff (kEntry i j) 0 = kZero i j := by decide +kernel
theorem a_constant : ∀ i, coeff (aEntry i) 0 = aZero i := by
  simp [aEntry, initialData, pow, mul, add, one, monomial, shiftScale, neg]
  decide +kernel
theorem b_constant : ∀ i, coeff (bEntry i) 0 = bZero i := by
  simp [bEntry, terminalData, pow, mul, add, one, monomial, shiftScale, neg]
  decide +kernel

/-- The integer fixed-vector calculation is checked by kernel reduction. -/
theorem constant_fixed : ∀ i, (indices.map (fun j => kZero i j * aZero j)).sum = aZero i := by
  decide

theorem constant_terminal : (indices.map (fun i => bZero i * aZero i)).sum = 1 := by
  decide

theorem norm_coordinates_support (m : Nat) : ∀ i, EvenNonpositive (normCoordinates m i) := by
  induction m with
  | zero => exact a_support
  | succ m ih =>
    intro i
    apply support_sum
    intro p hp
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
    exact support_mul _ _ (k_support i j) (ih j)

theorem norm_coordinates_constant (m : Nat) : ∀ i, coeff (normCoordinates m i) 0 = aZero i := by
  induction m with
  | zero => exact a_constant
  | succ m ih =>
    intro i
    simp only [normCoordinates, coordinateStep, coeff_sum, List.map_map]
    have h : (fun j => coeff (mul (kEntry i j) (normCoordinates m j)) 0) =
        (fun j => kZero i j * aZero j) := by
      funext j
      rw [coeff_mul_zero _ _ (k_support i j) (norm_coordinates_support m j), k_constant, ih]
    simpa only [Function.comp_def, h] using constant_fixed i

/-- Infinite-parameter conclusion; no tests of finitely many m replace this induction. -/
theorem norm_integral_constant_one (m : Nat) :
    EvenNonpositive (coordinateNorm m) ∧ coeff (coordinateNorm m) 0 = 1 := by
  constructor
  · apply support_sum
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact support_mul _ _ (b_support i) (norm_coordinates_support m i)
  · simp only [coordinateNorm, coeff_sum, List.map_map]
    have h : (fun i => coeff (mul (bEntry i) (normCoordinates m i)) 0) =
        (fun i => bZero i * aZero i) := by
      funext i
      rw [coeff_mul_zero _ _ (b_support i) (norm_coordinates_support m i),
        b_constant, norm_coordinates_constant]
    simpa only [Function.comp_def, h] using constant_terminal

#print axioms norm_integral_constant_one
#print axioms constant_fixed

end WebMu
