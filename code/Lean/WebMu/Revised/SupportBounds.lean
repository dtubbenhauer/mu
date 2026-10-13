import WebMu.RevisedLocal

/-! Complete coordinate-support checks for the prescribed boundary lengths.
Numbers encode words in base 3 in the given tensor-factor order. -/
namespace WebMu.Revised

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def validWord (n : Nat) (w : Word) : Bool := w.length == n && w.all (fun i => i < 3)

theorem raw_boundaries_check : ∀ i : Fin 27,
    allEntries (rawB i) (fun w _ => validWord 12 w) = true ∧
    allEntries (rawD i) (fun w _ => validWord 9 w) = true ∧
    allEntries (rawH i) (fun w _ => validWord 9 w) = true ∧
    allEntries (shortPrefix i) (fun w _ => validWord 6 w) = true := by native_decide

theorem scalar_boundaries_check :
    allEntries rawC (fun w _ => validWord 12 w) = true ∧
    allEntries rawQ (fun w _ => validWord 9 w) = true ∧
    allEntries tau2 (fun w _ => validWord 6 w) = true ∧
    allEntries tau3 (fun w _ => validWord 9 w) = true := by native_decide

theorem map_valid_nonzero {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (valid : α → Bool)
    (h : allEntries x (fun k _ => valid k) = true) (k : α)
    (hn : x.getD k [] ≠ []) : valid k = true := by
  cases he : x[k]? with
  | none => simp [Std.HashMap.getD_eq_getD_getElem?, he] at hn
  | some p =>
    exact List.all_eq_true.mp h (k,p) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr he)

theorem rawB_valid (i : Fin 27) (w : Word) (h : (rawB i).getD w [] ≠ []) :
    validWord 12 w = true := map_valid_nonzero _ _ (raw_boundaries_check i).1 w h

theorem rawD_valid (i : Fin 27) (w : Word) (h : (rawD i).getD w [] ≠ []) :
    validWord 9 w = true := map_valid_nonzero _ _ (raw_boundaries_check i).2.1 w h

theorem rawH_valid (i : Fin 27) (w : Word) (h : (rawH i).getD w [] ≠ []) :
    validWord 9 w = true := map_valid_nonzero _ _ (raw_boundaries_check i).2.2.1 w h

theorem shortPrefix_valid (i : Fin 27) (w : Word) (h : (shortPrefix i).getD w [] ≠ []) :
    validWord 6 w = true := map_valid_nonzero _ _ (raw_boundaries_check i).2.2.2 w h

theorem rawC_valid (w : Word) (h : rawC.getD w [] ≠ []) :
    validWord 12 w = true := map_valid_nonzero _ _ scalar_boundaries_check.1 w h

theorem rawQ_valid (w : Word) (h : rawQ.getD w [] ≠ []) :
    validWord 9 w = true := map_valid_nonzero _ _ scalar_boundaries_check.2.1 w h

theorem tau2_valid (w : Word) (h : tau2.getD w [] ≠ []) :
    validWord 6 w = true := map_valid_nonzero _ _ scalar_boundaries_check.2.2.1 w h

theorem tau3_valid (w : Word) (h : tau3.getD w [] ≠ []) :
    validWord 9 w = true := map_valid_nonzero _ _ scalar_boundaries_check.2.2.2 w h

end WebMu.Revised
