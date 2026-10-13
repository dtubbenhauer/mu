import WebMu.RevisedLocal

/-! Coordinate verification of the supplementary closed cap identities.
These statements do not assert that a particular drawn ribbon graph realizes
the coordinate maps; that geometric interpretation is separate. -/
namespace WebMu.Revised
open Laurent

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def e : Laurent := [(-2,1),(0,1),(2,1)]

def applyTripod (f : Nat → Tensor) : Tensor :=
  sumTensor ((List.range 27).map (fun i => scaleTensor (f i) (tripod.getD (triple i) [])))

def capAll : Nat → Tensor → Laurent
  | 0,x => x.getD [] []
  | n+1,x => capAll n (cap x)

def capLastSix (x : Tensor) : Tensor :=
  x.fold (fun out w p => accumulate out (w.take 3)
    (mul p (mul (eta (encode ((w.drop 3).take 3))) (eta (encode (w.drop 6)))))) ∅

theorem cap_tripod : capAll 1 tripod = mul d e := by native_decide

theorem closed_prefix : capAll 2 (applyTripod shortPrefix) = mul (pow d 5) e := by
  native_decide

theorem closed_tail_check : sameEntries (capLastSix rawQ) (scaleTensor tripod (pow d 4)) = true := by
  native_decide

theorem closed_tail (w : Word) :
    (capLastSix rawQ).getD w [] = (scaleTensor tripod (pow d 4)).getD w [] :=
  sameEntries_getD _ _ closed_tail_check w

theorem closed_block : capAll 4 (applyTripod rawB) =
    mul (mul (pow d 7) e) (pow (add (pow d 2) (monomial 0 2)) 2) := by
  native_decide

theorem closed_correction : capAll 3 (applyTripod rawD) =
    mul (mul (pow d 8) e) (add (pow d 2) (monomial 0 2)) := by native_decide

theorem closed_remainder : capAll 3 (applyTripod rawH) =
    shiftScale (mul (mul (pow d 7) e) (add (pow d 2) (monomial 0 2))) 0 2 := by
  native_decide

end WebMu.Revised
