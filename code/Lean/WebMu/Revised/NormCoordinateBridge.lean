import WebMu.Revised.NormSemantics
import WebMu.NormInduction

/-! The seven exact Laurent-coordinate recurrence in the existing certificate
is the coefficient recurrence in the full tensor norm semantics. -/
namespace WebMu.Revised.NormCoordinateBridge
open Algebra NormSemantics

def transfer (i j : Fin 7) : Poly := ofList (kEntry i j)
def initial (i : Fin 7) : Poly := ofList (aEntry i)
def terminal (i : Fin 7) : Poly := ofList (bEntry i)

theorem ofList_sum_total {ι : Type} (is : List ι) (f : ι → Laurent) :
    ofList (Laurent.sum (is.map f)) = total is (fun i => ofList (f i)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, Laurent.sum, ofList_add, total_cons, ih]

theorem coefficientIterate_actual (n : Nat) :
    coefficientIterate WebMu.indices transfer initial n =
      fun i => ofList (normCoordinates n i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    simp only [coefficientIterate, ih, action, normCoordinates, coordinateStep,
      ofList_sum_total, ofList_mul]
    rfl

theorem coordinateNorm_poly (n : Nat) :
    pairing WebMu.indices terminal (coefficientIterate WebMu.indices transfer initial n) =
      ofList (coordinateNorm n) := by
  rw [coefficientIterate_actual]
  simp only [pairing, coordinateNorm, ofList_sum_total, ofList_mul]
  rfl

theorem coordinateNorm_positive_zero (n : Nat) (d : Int) (hd : 0 < d) :
    coefficient (ofList (coordinateNorm n)) d=0 :=
  Laurent.coeff_positive _ (norm_integral_constant_one n).1 d hd

theorem coordinateNorm_constant_one (n : Nat) :
    coefficient (ofList (coordinateNorm n)) 0=1 :=
  (norm_integral_constant_one n).2

/-- Once the concrete three finite contractions have been discharged, the
supplementary seven-coordinate certificate controls the entire tensor norm. -/
theorem full_norm_integral_constant_one {α ε ι ω : Type}
    (is : List ι) (as : List α) (es : List ε) (ws : List ω)
    (p : α → ι → Poly) (a : ε → ι → ι → Poly) (q : ω → ι → Poly)
    (basis : Fin 7 → ι → ι → Poly)
    (hinitial : gram as p=combine WebMu.indices basis initial)
    (hstep : ∀ k, normStep is es a (basis k)=
      combine WebMu.indices basis (fun j => transfer j k))
    (hterminal : ∀ k, normReadout is ws q (basis k)=terminal k) (n : Nat) :
    (∀ d, 0 < d → coefficient (fullNorm is as es ws p a q n) d=0) ∧
    coefficient (fullNorm is as es ws p a q n) 0=1 := by
  rw [full_norm_transfer is as es ws WebMu.indices p a q basis transfer initial terminal
    hinitial hstep hterminal n, coordinateNorm_poly]
  exact ⟨coordinateNorm_positive_zero n, coordinateNorm_constant_one n⟩

#print axioms coefficientIterate_actual
#print axioms full_norm_integral_constant_one
end WebMu.Revised.NormCoordinateBridge
