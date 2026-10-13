import WebMu.Revised.ShorteningCanonical
import WebMu.Revised.BarCoordinates

/-! The same cited tensor-bar and canonical characterization, on arbitrary
signed boundaries, for the manuscript's small examples and tripod insertion.
The reference inputs are uniform over all boundary words and tensor vectors. -/
namespace WebMu.Revised.WebCanonical
open Laurent Algebra Bar ShorteningCanonical

abbrev TensorWord (s : Signs) := { w : Word // validWord s.length w = true }

/-- General tensor coordinates indexed by their actual ordered signed boundary. -/
def coordinates (R : BarReferences) (E : CoordinateReferences R)
    {s : Signs} (x : R.Space s) (w : TensorWord s) : Poly := E.coord s x w.val

/-- The cited general theorem, stated independently of any chosen web or family.
This is the arbitrary-boundary form of `CanonicalReferences`. -/
structure References (R : BarReferences) (E : CoordinateReferences R) where
  tensorBar : (s : Signs) → (TensorWord s → Poly) → TensorWord s → Poly
  coordinate_bar : ∀ s (x : R.Space s),
    tensorBar s (coordinates R E x) = coordinates R E (R.bar s x)
  characterization : ∀ s, CanonicalCharacterization (TensorWord s) (tensorBar s)

def circuitCoordinates (R : BarReferences) (E : CoordinateReferences R)
    {s : Signs} (f : Circuit [] s) : TensorWord s → Poly :=
  coordinates R E (R.interpret f R.vacuum)

/-- Additive syntax and sparse evaluation agree coefficient by coefficient. -/
theorem evalSparse_add {s t : Signs} (f g : Circuit s t) (u w : Word) :
    ofList ((evalSparse (.add f g) u).getD w []) =
      ofList ((evalSparse f u).getD w []) + ofList ((evalSparse g u).getD w []) := by
  change ofList ((sumMap [evalSparse f u,evalSparse g u]).getD w []) = _
  rw [sumMap_poly]
  simp

theorem evalSparse_sum {s t : Signs} (fs : List (Circuit s t)) (u w : Word) :
    ofList ((evalSparse (circuitSum fs) u).getD w []) =
      total fs (fun f => ofList ((evalSparse f u).getD w [])) := by
  induction fs with
  | nil => simp [circuitSum,evalSparse]
  | cons f fs ih => simp only [circuitSum,evalSparse_add,ih,total_cons]

theorem circuitCoordinates_fixed (R : BarReferences) (E : CoordinateReferences R)
    (C : References R E) {s : Signs} (f : Circuit [] s) :
    C.tensorBar s (circuitCoordinates R E f) = circuitCoordinates R E f := by
  rw [circuitCoordinates,C.coordinate_bar,circuit_natural,R.bar_vacuum]

theorem circuitCoordinates_evaluation (R : BarReferences) (E : CoordinateReferences R)
    {s : Signs} (f : Circuit [] s) (w : TensorWord s) :
    circuitCoordinates R E f w = ofList ((evalSparse f []).getD w.val []) :=
  E.closed_coordinates f w.val w.property

/-- Any exact all-word leading congruence gives the corresponding canonical
vector. The proof uses bar invariance of the actual typed spider circuit. -/
theorem canonical_of_circuit_congruence (R : BarReferences) (E : CoordinateReferences R)
    (C : References R E) {s : Signs} (f : Circuit [] s) (c : TensorWord s)
    (h : ∀ w d, 0 ≤ d → coeff ((evalSparse f []).getD w []) d =
      if w=c.val ∧ d=0 then 1 else 0) :
    (fun w : TensorWord s => ofList ((evalSparse f []).getD w.val [])) =
      (C.characterization s).canonical c := by
  have he : (fun w : TensorWord s => ofList ((evalSparse f []).getD w.val [])) =
      circuitCoordinates R E f := by
    funext w
    exact (circuitCoordinates_evaluation R E f w).symm
  apply (C.characterization s).unique
  · rw [he]
    exact circuitCoordinates_fixed R E C f
  · constructor
    · intro w d hd
      change coeff ((evalSparse f []).getD w.val []) d = 0
      simpa only [show d≠0 by omega,and_false,if_false] using h w.val d (by omega)
    · intro w
      change coeff ((evalSparse f []).getD w.val []) 0 = _
      simpa [Subtype.ext_iff] using h w.val 0 (by decide)

/-- Specialized to an arbitrary valid growth string; no example-specific bar
or canonicality assertion is supplied as a hypothesis. -/
theorem canonical_of_growth_congruence (R : BarReferences) (E : CoordinateReferences R)
    (C : References R E) (s : Signs) (steps : List Step)
    (typed : steps.foldlM descendSigns s = some []) (c : TensorWord s)
    (h : ∀ w d, 0 ≤ d → coeff ((expand steps (singleton [])).getD w []) d =
      if w=c.val ∧ d=0 then 1 else 0) :
    (fun w : TensorWord s => ofList ((expand steps (singleton [])).getD w.val [])) =
      (C.characterization s).canonical c :=
  canonical_of_circuit_congruence R E C (.down [] s steps typed) c h

#print axioms canonical_of_growth_congruence
end WebMu.Revised.WebCanonical
