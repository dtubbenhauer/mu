import WebMu.Revised.CoordinateData

/-! The sparse transformed maps are the actual matrix coordinate change.
All exterior coordinates are universally quantified in the public statements. -/
namespace WebMu.Revised
open Laurent Algebra

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def gaugeMatrix (i j : Fin 28) : Poly := ofList (g i j)
def inverseGaugeMatrix (i j : Fin 28) : Poly := ofList (ginv i j)
def originalPrefix (w : Word) (i : Fin 28) : Poly := ofList ((shortPrefix i).getD w [])
def originalBlock (w : Nat) (i j : Fin 28) : Poly := ofList ((block j).getD (i.val,w) [])
def originalTail (w : Nat) (i : Fin 28) : Poly := ofList (tail.getD (i.val,w) [])

theorem prefix_gauge (w : Word) (j : Fin 28) :
    ofList ((prefixHat j).getD w []) =
      rowmul (List.finRange 28) (originalPrefix w) inverseGaugeMatrix j := by
  rw [sameEntries_getD _ _ (prefix_dense_check j), denseRight_poly]
  rfl

theorem block_gauge (w : Nat) (i j : Fin 28) :
    ofList ((blockHat j).getD (i.val,w) []) =
      matmul (List.finRange 28)
        (matmul (List.finRange 28) gaugeMatrix (originalBlock w)) inverseGaugeMatrix i j := by
  rw [sameEntries_getD _ _ (block_dense_check j), denseLeft_poly]
  simp only [denseRight_poly]
  change total (List.finRange 28) (fun k => gaugeMatrix i k *
      total (List.finRange 28) (fun l => originalBlock w k l * inverseGaugeMatrix l j)) = _
  simp only [← mul_total, ← poly_mul_assoc]
  rw [total_swap]
  simp only [total_mul]
  rfl

theorem tail_gauge (w : Nat) (i : Fin 28) :
    ofList (tailHat.getD (i.val,w) []) =
      action (List.finRange 28) gaugeMatrix (originalTail w) i := by
  rw [sameEntries_getD _ _ tail_dense_check, denseLeft_poly]
  rfl

theorem ofList_sum (xs : List Laurent) : ofList (Laurent.sum xs) = sumP (xs.map ofList) := by
  induction xs with
  | nil => rfl
  | cons p ps ih => simp [Laurent.sum, ofList_add, ih]

theorem gauge_inverse : matmul (List.finRange 28) inverseGaugeMatrix gaugeMatrix =
    fun i j => if i = j then (1 : Poly) else 0 := by
  funext i j
  have h := congrArg ofList (inverse_sum_check i j)
  simp only [ofList_sum, List.map_map, Function.comp_def, ofList_mul] at h
  change _ = _ at h
  by_cases hij : i = j
  · simpa [matmul, total, inverseGaugeMatrix, gaugeMatrix, hij] using h
  · simpa [matmul, total, inverseGaugeMatrix, gaugeMatrix, hij] using h

end WebMu.Revised
