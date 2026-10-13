import WebMu.Revised.Bar
import WebMu.Revised.OriginalMaps

/-! Local identification of the typed, ungauged spider circuits with the
actual sparse web maps. No bar-invariance premise is used for these checks. -/
namespace WebMu.Revised.Bar

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem prefix_circuit_check : ∀ i : Fin 27,
    sameEntries (evalSparse prefixCircuit (triple i)) (shortPrefix i) = true := by
  native_decide

theorem b_circuit_check : ∀ i : Fin 27,
    sameEntries (evalSparse bCircuit (triple i)) (rawB i) = true := by native_decide

theorem c_circuit_check : sameEntries (evalSparse cCircuit []) rawC = true := by native_decide

theorem d_circuit_check : ∀ i : Fin 27,
    sameEntries (evalSparse dCircuit (triple i)) (rawD i) = true := by native_decide

theorem q_circuit_check : sameEntries (evalSparse qCircuit []) rawQ = true := by native_decide

theorem tau_two_circuit_check : sameEntries (evalSparse tauTwoCircuit []) tau2 = true := by
  native_decide

theorem tau_three_circuit_check : sameEntries (evalSparse tauThreeCircuit []) tau3 = true := by
  native_decide

theorem prefix_circuit (i : Fin 27) (w : Word) :
    (evalSparse prefixCircuit (triple i)).getD w [] = (shortPrefix i).getD w [] :=
  sameEntries_getD _ _ (prefix_circuit_check i) w

theorem b_circuit (i : Fin 27) (w : Word) :
    (evalSparse bCircuit (triple i)).getD w [] = (rawB i).getD w [] :=
  sameEntries_getD _ _ (b_circuit_check i) w

theorem c_circuit (w : Word) : (evalSparse cCircuit []).getD w [] = rawC.getD w [] :=
  sameEntries_getD _ _ c_circuit_check w

theorem d_circuit (i : Fin 27) (w : Word) :
    (evalSparse dCircuit (triple i)).getD w [] = (rawD i).getD w [] :=
  sameEntries_getD _ _ (d_circuit_check i) w

theorem q_circuit (w : Word) : (evalSparse qCircuit []).getD w [] = rawQ.getD w [] :=
  sameEntries_getD _ _ q_circuit_check w

theorem tau_two_circuit (w : Word) : (evalSparse tauTwoCircuit []).getD w [] = tau2.getD w [] :=
  sameEntries_getD _ _ tau_two_circuit_check w

theorem tau_three_circuit (w : Word) :
    (evalSparse tauThreeCircuit []).getD w [] = tau3.getD w [] :=
  sameEntries_getD _ _ tau_three_circuit_check w

end WebMu.Revised.Bar
