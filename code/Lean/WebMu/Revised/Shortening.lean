import WebMu.RevisedLocal
import WebMu.Revised.Sparse

namespace WebMu.Revised
open Laurent Algebra

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The padded first correction really is P⊗τ with τ in the final three slots. -/
theorem removable_tripod_check : ∀ i : Fin 27,
    sameEntries (expand prefixSteps (singleton (triple i)))
      (tensorProduct (shortPrefix i) tripod) = true := by native_decide

theorem removable_tripod (i : Fin 27) (w : Word) :
    (expand prefixSteps (singleton (triple i))).getD w [] =
      (tensorProduct (shortPrefix i) tripod).getD w [] :=
  sameEntries_getD _ _ (removable_tripod_check i) w

def tripodNorm : Laurent := Laurent.sum (tripod.toList.map (fun (_,p) => mul p p))

theorem tripod_norm_exact : tripodNorm = [(-6,1),(-4,2),(-2,2),(0,1)] := by native_decide

theorem tripod_norm_factorization : tripodNorm =
    mul [(-2,1),(0,1)] [(-4,1),(-2,1),(0,1)] := by native_decide

theorem tripod_ABC : tripod.getD [0,1,2] [] = one := by native_decide

theorem tripod_nonpositive : allEntries tripod (fun _ p => bounded 0 p) = true := by native_decide

theorem tripod_unique_constant : singleConstant tripod [0,1,2] = true := by native_decide

end WebMu.Revised
