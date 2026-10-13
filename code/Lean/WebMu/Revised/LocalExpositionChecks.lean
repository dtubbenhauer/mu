import WebMu.Revised.GrowthPairing

/-! Exact checks of the intermediate covectors printed in the proof and appendix.
All are evaluated from the elementary tables, with the displayed boundary order. -/
namespace WebMu.Revised.LocalExpositionChecks
open Laurent Algebra M2Flow GrowthPairing
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def tensorOf (terms : List (Word × Laurent)) : Tensor :=
  terms.foldl (fun x (w,p) => accumulate x w p) ∅

def dPrefixExpected : Array Tensor := #[
  tensorOf [([0,1,2],monomial 1),([0,2,1],one),([1,0,2],one)],
  tensorOf [([0,1,2],monomial (-1)),([1,0,2],monomial (-2))],
  tensorOf [([0,2],one),([1,1],monomial (-1))],
  tensorOf [([0,2],monomial (-1)),([1,1],monomial (-2))],
  tensorOf [([0,2],monomial (-2))],
  tensorOf [([0,2],monomial (-1))],
  tensorOf [([0,2],one)]]

def hPrefixExpected : Array Tensor := #[
  tensorOf [([0,1,2],one),([0,2,1],monomial (-1))],
  tensorOf [([0,1,2],monomial (-2))],
  tensorOf [([0,2],monomial (-1))],
  tensorOf [([0,2],[(-2,1),(0,1)]),([1,1],monomial (-1))],
  tensorOf [([0,2],monomial (-3))],
  tensorOf [([0,1,2],one),([0,2,1],monomial (-1)),([1,0,2],monomial (-1))],
  tensorOf [([0,2],one)],
  tensorOf [([0,1,2],one),([1,0,2],monomial (-1))],
  tensorOf [([0,2],monomial (-1))],
  tensorOf [([0,2],monomial (-1)),([1,1],monomial (-2))],
  tensorOf [([0,2],monomial (-3))]]

def downwardCovector (steps : List Step) (output : Word) : Tensor :=
  steps.foldl downwardStep (singleton output)

theorem d_prefix_check : ∀ i : Fin 7,
    sameEntries (downwardCovector correctionSteps[i.val]!.1 wordBlock) dPrefixExpected[i.val]! = true := by
  native_decide

theorem h_prefix_check : ∀ i : Fin 11,
    sameEntries (downwardCovector hSteps[i.val]!.1 wordBlock) hPrefixExpected[i.val]! = true := by
  native_decide

theorem d_prefix_covector (i : Fin 7) (w : Word) :
    (downwardCovector correctionSteps[i.val]!.1 wordBlock).getD w [] = dPrefixExpected[i.val]!.getD w [] :=
  sameEntries_getD _ _ (d_prefix_check i) w

theorem h_prefix_covector (i : Fin 11) (w : Word) :
    (downwardCovector hSteps[i.val]!.1 wordBlock).getD w [] = hPrefixExpected[i.val]!.getD w [] :=
  sameEntries_getD _ _ (h_prefix_check i) w

theorem covector_is_coordinate (steps : List Step) (input output : Word) :
    ofList ((downwardCovector steps output).getD input []) =
      ofList ((expand steps (singleton input)).getD output []) := by
  have h := expand_transpose steps (singleton input) (singleton output)
  rw [pair_singleton,singleton_pair] at h
  exact h.symm

theorem d_prefix_coordinate (i : Fin 7) (w : Word) :
    ofList ((expand correctionSteps[i.val]!.1 (singleton w)).getD wordBlock []) =
      ofList (dPrefixExpected[i.val]!.getD w []) := by
  rw [← covector_is_coordinate,d_prefix_covector]

theorem h_prefix_coordinate (i : Fin 11) (w : Word) :
    ofList ((expand hSteps[i.val]!.1 (singleton w)).getD wordBlock []) =
      ofList (hPrefixExpected[i.val]!.getD w []) := by
  rw [← covector_is_coordinate,h_prefix_covector]

theorem s_row_check : sameEntries (downwardCovector sSteps [0,2,0,2])
    dPrefixExpected[0]! = true := by native_decide

theorem s_row (w : Word) : (downwardCovector sSteps [0,2,0,2]).getD w [] =
    dPrefixExpected[0]!.getD w [] := sameEntries_getD _ _ s_row_check w

theorem s_AAA_check : sameEntries (expand sSteps (singleton [0,0,0]))
    (tensorOf [([0,0,0,1],one),([1,0,0,0],monomial (-1))]) = true := by native_decide

theorem s_AAA (w : Word) : (expand sSteps (singleton [0,0,0])).getD w [] =
    (tensorOf [([0,0,0,1],one),([1,0,0,0],monomial (-1))]).getD w [] :=
  sameEntries_getD _ _ s_AAA_check w

#print axioms d_prefix_coordinate
#print axioms h_prefix_coordinate
end WebMu.Revised.LocalExpositionChecks
