import WebMu.Local
import WebMu.LaurentProofs

/-!
The fixed-size calculation in Proposition 4.2 of finite-type-A-draft.tex.
The large decisions use `native_decide`: the trusted base includes Lean's
compiler/runtime via Lean.ofReduceBool. There are no sorry or project axioms.
The canonical-basis criterion and FKK identification are NOT formalised here.
-/
namespace WebMu

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem signed_growth_types : growthTypes = true := by decide

theorem transfer_identities : actualTransfer = predictedTransfer := by native_decide

theorem initial_identity : actualInitial = predictedInitial := by native_decide

theorem terminal_identities : actualTerminal = terminalData := by native_decide

theorem integral_even_and_constants : integralityAndConstants = true := by native_decide

theorem leading_path_entries : leadingEntries = true := by native_decide

/-- Exact local tensor certificate. No hypothesis assumes an identity being checked. -/
theorem proposition_4_2 :
    actualTransfer = predictedTransfer ∧
    actualInitial = predictedInitial ∧
    actualTerminal = terminalData ∧
    integralityAndConstants = true ∧
    leadingEntries = true ∧
    growthTypes = true :=
  ⟨transfer_identities, initial_identity, terminal_identities,
    integral_even_and_constants, leading_path_entries, signed_growth_types⟩

#print axioms proposition_4_2
#print axioms Laurent.coeff_add
#print axioms Laurent.coeff_mul

end WebMu
