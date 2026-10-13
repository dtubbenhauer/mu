import Std

/-! Coefficient extraction from the alternating parabolic formula.
No KL result is an axiom here: the ordinary support bound is an explicit premise.
It is the usual strict-pair degree bound together with the diagonal polynomial 1.
-/
namespace WebMu.Revised.KLTop

abbrev Coefficients := Nat → Int

/-- `delta` is ℓ(y)-ℓ(x); `hLength` is ℓ(h), with ℓ(xh)=ℓ(x)+ℓ(h).
Only terms with xh ≤ y are included. -/
def OrdinarySupport (delta hLength : Nat) (p : Coefficients) : Prop :=
  ∀ d, p d ≠ 0 →
    (hLength = delta ∧ d = 0) ∨ (hLength < delta ∧ 2*d+hLength+1 ≤ delta)

theorem nonidentity_top_vanishes (delta k hLength : Nat) (p : Coefficients)
    (hdelta : delta = 2*k+1) (hlarge : 3 ≤ delta) (hpos : 0 < hLength)
    (hsupport : OrdinarySupport delta hLength p) : p k = 0 := by
  apply Classical.byContradiction
  intro hn
  obtain hdiag | hstrict := hsupport k hn
  · omega
  · omega

def alternatingRest {ι : Type} (terms : List ι) (hLength : ι → Nat)
    (p : ι → Coefficients) (d : Nat) : Int :=
  match terms with
  | [] => 0
  | h::hs => (-1)^(hLength h) * p h d + alternatingRest hs hLength p d

theorem alternatingRest_zero {ι : Type} (terms : List ι) (hLength : ι → Nat)
    (p : ι → Coefficients) (d : Nat) (hz : ∀ h ∈ terms, p h d = 0) :
    alternatingRest terms hLength p d = 0 := by
  induction terms with
  | nil => rfl
  | cons h hs ih =>
    simp only [alternatingRest, hz h (by simp), Int.mul_zero, Int.zero_add]
    apply ih
    intro h hh
    exact hz h (by simp [hh])

/-- Removing the identity from the alternating parabolic sum changes no critical
coefficient. The tail may contain repetitions: the proof needs only its support. -/
theorem top_transfer {ι : Type} (terms : List ι) (hLength : ι → Nat)
    (p : ι → Coefficients) (ordinary parabolic : Coefficients) (delta k : Nat)
    (hdelta : delta = 2*k+1) (hlarge : 3 ≤ delta)
    (hpos : ∀ h ∈ terms, 0 < hLength h)
    (hsupport : ∀ h ∈ terms, OrdinarySupport delta (hLength h) (p h))
    (halt : parabolic k = ordinary k + alternatingRest terms hLength p k) :
    parabolic k = ordinary k := by
  have hz : ∀ h ∈ terms, p h k = 0 := by
    intro h hh
    exact nonidentity_top_vanishes delta k (hLength h) (p h)
      hdelta hlarge (hpos h hh) (hsupport h hh)
  rw [alternatingRest_zero _ _ _ _ hz, Int.add_zero] at halt
  exact halt

/-- With t=v⁻¹ and q=v², v⁻δ q^d contributes to [t] exactly at 2d=δ-1. -/
theorem first_order_exponent (delta k d : Nat) (hdelta : delta = 2*k+1) :
    -(delta : Int) + 2*(d : Int) = -1 ↔ d = k := by omega

theorem family_top_transfer {ι : Type} (r : Nat) (terms : List ι)
    (hLength : ι → Nat) (p : ι → Coefficients) (ordinary parabolic : Coefficients)
    (hpos : ∀ h ∈ terms, 0 < hLength h)
    (hsupport : ∀ h ∈ terms, OrdinarySupport (34*r+11) (hLength h) (p h))
    (halt : parabolic (17*r+5) = ordinary (17*r+5) +
      alternatingRest terms hLength p (17*r+5)) :
    parabolic (17*r+5) = ordinary (17*r+5) :=
  top_transfer terms hLength p ordinary parabolic (34*r+11) (17*r+5)
    (by omega) (by omega) hpos hsupport halt

theorem odd_parameter_no_first_order (r d : Nat) :
    -((17*(2*r+1)+11 : Nat) : Int) + 2*(d : Int) ≠ -1 := by omega

#print axioms top_transfer
#print axioms first_order_exponent
end WebMu.Revised.KLTop
