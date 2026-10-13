import WebMu.Revised.AtomicCoordinates
import WebMu.Revised.BoundaryChart

/-! The tensor bar in the manuscript's ordered output chart is defined by
coordinate reconstruction. Its compatibility is a theorem, not a reference
field about the project's boundary encoding. -/
namespace WebMu.Revised.Bar
open Algebra BoundaryChart

def AtomicCoordinates.boundaryRealize (A : AtomicCoordinates R) (m : Nat)
    (f : Boundary m → Poly) : R.Space (positive 6 ++ exterior m) :=
  A.realize _ (BoundaryChart.extend m f)

theorem AtomicCoordinates.boundaryRealize_coordinates (A : AtomicCoordinates R)
    (m : Nat) (x : R.Space (positive 6 ++ exterior m)) :
    A.boundaryRealize m (fun b => A.coord _ x b.word) = x := by
  apply A.coord_ext
  intro w hw
  have hv : validWord (12+9*m) w = true := by
    simpa only [original_boundary_length] using hw
  change A.coord _ (A.realize _ _) w = _
  rw [A.coord_realize _ _ w hw]
  simp only [BoundaryChart.extend,dif_pos hv,boundaryOfWord_word]

def AtomicCoordinates.tensorBar (A : AtomicCoordinates R) :
    (m : Nat) → (Boundary m → Poly) → Boundary m → Poly :=
  fun m f b => A.coord _ (R.bar _ (A.boundaryRealize m f)) b.word

theorem AtomicCoordinates.boundary_coordinates (A : AtomicCoordinates R)
    (m : Nat) (x : R.Space (positive 6 ++ exterior m)) :
    A.tensorBar m (fun b => A.coord _ x b.word) =
      fun b => A.coord _ (R.bar _ x) b.word := by
  funext b
  change A.coord _ (R.bar _ (A.boundaryRealize m (fun c => A.coord _ x c.word))) b.word = _
  rw [A.boundaryRealize_coordinates]

#print axioms AtomicCoordinates.boundary_coordinates

end WebMu.Revised.Bar
