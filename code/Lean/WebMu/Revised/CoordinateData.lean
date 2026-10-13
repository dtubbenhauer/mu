import WebMu.Revised.Sparse

namespace WebMu.Revised
open Laurent Algebra
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem prefix_dense_check : ∀ j : Fin 28,
    sameEntries (prefixHat j) (denseRight ginv shortPrefix j) = true := by native_decide

theorem block_dense_check : ∀ j : Fin 28,
    sameEntries (blockHat j) (denseLeft g (denseRight ginv block j)) = true := by
  native_decide

theorem tail_dense_check : sameEntries tailHat (denseLeft g tail) = true := by native_decide

theorem inverse_sum_check : ∀ i j : Fin 28,
    Laurent.sum ((List.finRange 28).map (fun (k : Fin 28) => mul (ginv i k) (g k j))) =
      if i = j then one else [] := by native_decide

end WebMu.Revised
