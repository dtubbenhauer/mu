import WebMu.Revised.Conclusion
import WebMu.Revised.RSKBumping

/-! Only the type-A cell classification remains a prior input in this adapter.
The insertion and recording tableaux are computed by row insertion, and the
row-reading conclusions follow from the manuscript's three block inductions. -/
namespace WebMu.Revised.RSKBumping
open Family Tableaux

/-- The cited type-A cell criterion for the actual recording algorithm. -/
structure CellClassification where
  sameLeftCell : List Nat → List Nat → Prop
  criterion : ∀ p q n,
    p.Perm (List.range' 1 n) → q.Perm (List.range' 1 n) →
    recording p = recording q → sameLeftCell p q

/-- Compatibility with existing conclusion types, with no row-reading input. -/
def cellReferences (S : CellClassification) : CellReferences where
  insertion := insertion
  recording := recording
  sameLeftCell := S.sameLeftCell
  rowReading := derived_row_reading
  leftCellCriterion := S.criterion

/-- The cell assertion in `lem:rectangular-cell`, now following the explicit
bumping calculation and then precisely the cited cell classification. -/
theorem common_left_cell_written (S : CellClassification) (m : Nat) :
    S.sameLeftCell (xPermutation m) (yPermutation m) :=
  family_common_left_cell insertion recording S.sameLeftCell
    derived_row_reading S.criterion m

#print axioms common_left_cell_written
end WebMu.Revised.RSKBumping
