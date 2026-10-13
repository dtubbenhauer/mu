import WebMu.Revised.UpperDegreeProof
import WebMu.Revised.LocalPathEnds
import WebMu.Revised.StagedAscent

/-! The lower-row and end degree estimates, applied term by term to the
formulas obtained from the diagrammatic cap relations. -/
namespace WebMu.Revised.LocalDegreeProof
open Laurent Algebra Bar
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def lowerDegreeExpr (j : Nat) (w : Word) : Laurent :=
  shiftScale (add (add (shiftScale ((rawD₀ j).getD w []) (-2) 1)
    (shiftScale ((rawH j).getD w []) (-1) 1))
    (neg (shiftScale (mul (tau3.getD w []) (eta j)) (-4) 1))) (-height j) 1

theorem eta_degree (j : Fin 27) : DegreeLE (eta j) (height j+2) := by
  apply degree_of_bound
  have h : ∀ j : Fin 27, (eta j).all (fun p => p.1≤height j+2)=true := by decide
  intro x hx
  exact of_decide_eq_true (List.all_eq_true.mp (h j) x hx)

theorem lower_expression_integral (j : Fin 27) (w : Word) : DegreeLE (lowerDegreeExpr j w) 0 := by
  have ha := StagedAscent.ascent_le_height j
  have hd := degree_shift (StagedAscent.d₀_ascent_degree j w) (-2) 1
  have hh := degree_shift (StagedAscent.h_ascent_degree j w) (-1) 1
  have ht := degree_neg (degree_shift (degree_mul (LocalPaths.tau3_degree w) (eta_degree j)) (-4) 1)
  have hb := degree_add (degree_add (degree_mono hd (show LocalPaths.ascWord (triple j)+(-2)≤height j by omega))
    (degree_mono hh (show LocalPaths.ascWord (triple j)+(-1)≤height j by omega)))
    (degree_mono ht (show (0+(height j+2))+(-4)≤height j by omega))
  have hs := degree_shift hb (-height j) 1
  have hz : height j+(-height j)=0 := by omega
  simpa only [hz] using hs

theorem lower_zero_input_negative (w : Word) : DegreeLE (lowerDegreeExpr 0 w) (-1) := by
  have hd := degree_shift (StagedAscent.d₀_ascent_degree 0 w) (-2) 1
  have hh := degree_shift (StagedAscent.h_ascent_degree 0 w) (-1) 1
  have ha : LocalPaths.ascWord (triple 0)=0 := by decide
  simp only [Fin.val_zero] at hd hh
  rw [ha] at hd hh
  have he : DegreeLE (eta 0) 0 := by intro e he; rfl
  have ht := degree_neg (degree_shift (degree_mul (LocalPaths.tau3_degree w) he) (-4) 1)
  have hb := degree_add (degree_add (degree_mono hd (by decide)) hh)
    (degree_mono ht (by decide))
  have hs := degree_shift hb (-height 0) 1
  exact hs

theorem d_degree : DegreeLE d 1 := by
  apply degree_of_bound
  simp [TruncatedGrowth.BoundedAbove,d,add,monomial]

theorem lower_scalar_negative (w : Word) :
    DegreeLE (shiftScale (mul (tau3.getD w []) d) (-2) 1) (-1) :=
  degree_shift (degree_mul (LocalPaths.tau3_degree w) d_degree) (-2) 1

theorem tail_scalar_negative (w : Word) :
    DegreeLE (add (shiftScale (tau2.getD w []) (-2) 1)
      (shiftScale (tailTree.getD w []) (-1) 1)) (-1) :=
  degree_add (degree_mono (degree_shift (LocalPaths.tau2_degree w) (-2) 1) (by decide))
    (degree_shift (LocalPaths.tailTree_degree w) (-1) 1)

theorem prefix_formula (j : Fin 27) (w : Word) :
    ofList ((prefixHat j).getD w [])=
      ofList (shiftScale ((expand shortPrefixSteps (singleton (triple j))).getD w []) (-height j) 1) := by
  change ofList ((scaleMap (shortPrefix j) (monomial (-height j))).getD w [])=_
  rw [scaleMap_poly]
  simp only [shortPrefix,if_pos j.isLt]
  apply poly_ext
  intro e
  change coeff (mul _ (monomial (-height j))) e=coeff (shiftScale _ (-height j) 1) e
  rw [Algebra.mul_comm]
  simp [monomial,mul,coeff_add,coeff_shiftScale,coeff]

theorem prefix_scalar_zero (w : Word) : (prefixHat 27).getD w []=[] := by
  simp [prefixHat,shortPrefix,scaleTensor,Std.HashMap.fold_eq_foldl_toList]
  have he : (∅ : Tensor).toList=[] := by native_decide
  rw [he,List.foldl_nil,Std.HashMap.getD_empty]

theorem prefix_degree (j : Fin 28) (w : Word) : DegreeLE ((prefixHat j).getD w []) 0 := by
  by_cases hj : j.val<27
  · have hb := degree_shift (LocalPaths.prefix_degree ⟨j.val,hj⟩ w) (-height j) 1
    have hz : height j+(-height j)=0 := by omega
    rw [hz] at hb
    exact degree_congr (prefix_formula ⟨j.val,hj⟩ w) hb
  · have he : j.val=27 := by omega
    rw [he,prefix_scalar_zero]
    intro e he; rfl

theorem prefix_constant_from_paths (w : Word) :
    coeff ((prefixHat 0).getD w []) 0=if w=wordY then 1 else 0 := by
  have h := congrArg (fun p => coefficient p 0) (prefix_formula 0 w)
  simp only [coefficient_ofList,coeff_shiftScale] at h
  have hz : height 0=0 := by decide
  simp only [Fin.val_zero] at h
  rw [hz] at h
  simp only [Int.neg_zero,Int.sub_zero,Int.mul_one] at h
  exact h.trans (LocalPaths.prefix_constant w)

#print axioms lower_expression_integral
#print axioms prefix_constant_from_paths
end WebMu.Revised.LocalDegreeProof
