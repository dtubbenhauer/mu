import WebMu.Revised.OriginalTensor

/-! The only canonical-basis input is the uniform tensor characterization
(Lusztig, Introduction to Quantum Groups, Chapter 27; Khovanov–Kuperberg,
Section 6). The basis is indexed in the ordered 6|9|...|9|6 tensor convention.
Bar is the tensor bar, not entrywise coefficient conjugation. -/
namespace WebMu.Revised
open Algebra

abbrev TensorBar := (m : Nat) → (Boundary m → Poly) → (Boundary m → Poly)

structure CanonicalReferences (bar : TensorBar) where
  canonical : (m : Nat) → Boundary m → Boundary m → Poly
  unique : ∀ m c f, bar m f = f →
    (∀ b d, 0 < d → coefficient (f b) d = 0) →
    (∀ b, coefficient (f b) 0 = if b = c then 1 else 0) →
    f = canonical m c

/-- The remaining representation-theoretic hypothesis is stated explicitly;
local integrality and the full leading-state property are already proved. -/
theorem canonical_from_original_bar (bar : TensorBar) (R : CanonicalReferences bar)
    (m : Nat) (hbar : bar m (tensorOriginal m) = tensorOriginal m) :
    tensorOriginal m = R.canonical m (leadingBoundary m) :=
  R.unique m (leadingBoundary m) (tensorOriginal m) hbar
    (tensorOriginal_integral m) (tensorOriginal_constant m)

end WebMu.Revised
