import WebMu.Revised.Boundary
import WebMu.Revised.CoordinateBridge

namespace WebMu.Revised
open Algebra

/-- The original corrected tensor, in its ordered standard tensor coordinates. -/
def tensorOriginal (m : Nat) (b : Boundary m) : Poly :=
  pairing interfaceIndices (originalPrefix b.initial)
    (wordAction interfaceIndices originalBlock (originalTail (encode b.terminal))
      (b.blocks.map encode))

/-- Equality of the complete tensor, not merely of the selected coordinate. -/
theorem tensor_coordinate_change (m : Nat) : tensorHat m = tensorOriginal m := by
  funext b
  unfold tensorHat gaugedTensor
  rw [ofList_tensorCoefficient]
  have hp : (fun i => ofList (prefixCoordinate b.initial i)) =
      rowmul interfaceIndices (originalPrefix b.initial) inverseGaugeMatrix :=
    funext (prefix_gauge b.initial)
  have ha : (fun e i j => ofList (blockCoordinate e i j)) =
      fun e => matmul interfaceIndices
        (matmul interfaceIndices gaugeMatrix (originalBlock e)) inverseGaugeMatrix := by
    funext e i j
    exact block_gauge e i j
  have hq : (fun i => ofList (tailCoordinate (encode b.terminal) i)) =
      action interfaceIndices gaugeMatrix (originalTail (encode b.terminal)) :=
    funext (tail_gauge (encode b.terminal))
  rw [hp,ha,hq]
  exact gauge_cancellation interfaceIndices interfaceIndices_nodup interfaceIndices_mem
    gaugeMatrix inverseGaugeMatrix gauge_inverse _ _ _ _

theorem tensorOriginal_integral (m : Nat) (b : Boundary m) (d : Int) (hd : 0 < d) :
    coefficient (tensorOriginal m b) d = 0 := by
  rw [← tensor_coordinate_change]
  exact tensorHat_integral m b d hd

theorem tensorOriginal_constant (m : Nat) (b : Boundary m) :
    coefficient (tensorOriginal m b) 0 = if b = leadingBoundary m then 1 else 0 := by
  rw [← tensor_coordinate_change]
  exact tensorHat_constant m b

theorem tensorOriginal_source_even (r : Nat) :
    coefficient (tensorOriginal (2*r) (sourceBoundary (2*r))) (-1) = (2:Int)^r := by
  rw [← tensor_coordinate_change]
  exact tensorHat_source_even r

end WebMu.Revised
