import WebMu.Revised.Labels
import WebMu.Revised.LocalDegreeAlgebra
import WebMu.Revised.LocalPathConsequences
import WebMu.Revised.GrowthPairing
import WebMu.Revised.CircuitSparseSemantics

/-! The manuscript's upper-row proof: subtract the single excessive cup
monomial before composing with the height-shifted outer map. -/
namespace WebMu.Revised.LocalDegreeProof
open Laurent Algebra GrowthPairing Bar TruncatedGrowth
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem degree_congr {p q : Laurent} {b : Int} (h : ofList p=ofList q)
    (hq : DegreeLE q b) : DegreeLE p b := by
  intro e he
  exact (congrArg (fun z => coefficient z e) h).trans (hq e he)

theorem expand_matrix (ss : List Step) (x : Tensor) (w : Word) :
    ofList ((expand ss x).getD w []) = total x.toList (fun (u,p) =>
      ofList ((expand ss (singleton u)).getD w []) * ofList p) := by
  have h := expand_transpose ss x (singleton w)
  rw [pair_singleton] at h
  rw [h]
  unfold sparsePair
  apply total_congr_mem
  rintro ⟨u,p⟩ _
  have he := expand_transpose ss (singleton u) (singleton w)
  rw [pair_singleton,singleton_pair] at he
  dsimp only
  rw [← he,poly_mul_comm]

theorem expand_degree (ss : List Step) (x : Tensor) (w : Word) (a b : Int)
    (ho : ∀ u p, (u,p) ∈ x.toList → DegreeLE ((expand ss (singleton u)).getD w []) a)
    (hi : ∀ u, DegreeLE (x.getD u []) b) : DegreeLE ((expand ss x).getD w []) (a+b) := by
  apply degree_congr (expand_matrix ss x w |>.trans (ofList_total _ _).symm)
  apply degree_sum
  intro p hp
  obtain ⟨⟨u,q⟩,hu,rfl⟩ := List.mem_map.mp hp
  apply degree_mul (ho u q hu)
  rw [← entry_lookup x u q hu]
  exact hi u

theorem pair_right_add (x y z : Tensor) :
    sparsePair x (addMap y z) = sparsePair x y+sparsePair x z := by
  unfold sparsePair
  simp only [addMap_poly,poly_mul_add]
  exact total_add _ _ _

theorem pair_right_scale (x y : Tensor) (a : Laurent) :
    sparsePair x (scaleMap y a) = sparsePair x y*ofList a := by
  unfold sparsePair
  simp only [scaleMap_poly,← poly_mul_assoc]
  exact total_mul _ _ _

theorem expand_add (ss : List Step) (x y : Tensor) (w : Word) :
    ofList ((expand ss (addMap x y)).getD w []) =
      ofList ((expand ss x).getD w [])+ofList ((expand ss y).getD w []) := by
  have h := expand_transpose ss (addMap x y) (singleton w)
  have hx := expand_transpose ss x (singleton w)
  have hy := expand_transpose ss y (singleton w)
  rw [pair_singleton] at h hx hy
  rw [h,sparsePair_comm,pair_right_add,sparsePair_comm _ x,sparsePair_comm _ y,← hx,← hy]

theorem expand_scale (ss : List Step) (x : Tensor) (a : Laurent) (w : Word) :
    ofList ((expand ss (scaleMap x a)).getD w []) =
      ofList ((expand ss x).getD w [])*ofList a := by
  have h := expand_transpose ss (scaleMap x a) (singleton w)
  have hx := expand_transpose ss x (singleton w)
  rw [pair_singleton] at h hx
  rw [h,sparsePair_comm,pair_right_scale,sparsePair_comm _ x,← hx]

def innerResidual (j : Nat) : Tensor :=
  addMap (expand innerSteps (singleton (triple j)))
    (scaleMap fourCups (neg (shiftScale (eta j) (-1) 1)))

theorem innerResidual_coordinate (j : Nat) (w : Word) :
    ofList ((innerResidual j).getD w []) =
      ofList ((expand innerSteps (singleton (triple j))).getD w [])+
        ofList (fourCups.getD w [])*ofList (neg (shiftScale (eta j) (-1) 1)) := by
  simp only [innerResidual,addMap_poly,scaleMap_poly]

theorem expand_append (a b : List Step) (x : Tensor) :
    expand (a++b) x=expand a (expand b x) := by
  simp [expand,compose,List.reverse_append,List.foldl_append]

theorem upper_factorization (j : Fin 27) (w : Word) :
    ofList ((expand cSteps (innerResidual j)).getD w []) =
      ofList (add ((rawB j).getD w [])
        (neg (mul (rawC.getD w []) (shiftScale (eta j) (-1) 1)))) := by
  rw [innerResidual,expand_add,expand_scale,← expand_append,← block_factorization]
  change ofList ((rawB j).getD w [])+ofList (rawC.getD w []) *
    ofList (neg (shiftScale (eta j) (-1) 1)) = _
  rw [ofList_add]
  congr 1
  apply poly_ext
  intro e
  change coeff (mul (rawC.getD w []) (neg (shiftScale (eta j) (-1) 1))) e = _
  simp only [coefficient_ofList,Algebra.coeff_neg]
  have hneg (p q : Laurent) : coeff (mul p (neg q)) e = -coeff (mul p q) e := by
    induction p generalizing e with
    | nil => rfl
    | cons x p ih =>
      rw [mul,coeff_add,coeff_shiftScale,Algebra.coeff_neg,ih,mul,coeff_add,coeff_shiftScale]
      simp [Int.neg_mul,Int.neg_add]
  exact hneg _ _

theorem residual_support_check : ∀ j : Fin 27,
    allEntries (innerResidual j) (fun w _ => validWord 8 w)=true := by native_decide

theorem four_cups_support : allEntries fourCups (fun w _ => validWord 8 w)=true := by native_decide

theorem four_cups_nonpositive : allEntries fourCups (fun _ p => bounded 0 p)=true := by native_decide

def cupCorrection (j : Nat) : Tensor := scaleMap fourCups (shiftScale (eta j) (-1) 1)

/-- The only term of t c8 eta exceeding the input height is the same
coefficient-one monomial as the excessive inner path. -/
theorem cup_excess_check : ∀ j : Fin 27,
    sameEntries (above (cupCorrection j) (height j)) (innerExcessExpected j)=true := by native_decide

theorem above_poly (x : Tensor) (b : Int) (w : Word) :
    ofList ((above x b).getD w [])=ofList ((x.getD w []).filter (fun a => b<a.1)) := by
  rw [above,hashmap_fold_poly]
  exact hashmap_total_lookup x w (fun p => ofList (p.filter (fun a => b<a.1))) rfl

theorem coeff_above (p : Laurent) (b e : Int) (he : b<e) :
    coeff (p.filter (fun a => b<a.1)) e=coeff p e := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    rcases x with ⟨k,c⟩
    simp only [List.filter_cons,decide_eq_true_eq]
    by_cases hk : b<k
    · simp only [if_pos hk,coeff,ih]
    · simp only [if_neg hk,coeff,if_neg (show k≠e by omega),Int.zero_add,ih]

/-- The only constant of c_8 is obtained by taking the AC branch in each cup. -/
theorem four_cups_constant (w : Word) : coeff (fourCups.getD w []) 0=
    if w=[0,2,0,2,0,2,0,2] then 1 else 0 := by
  have h : singleConstant fourCups [0,2,0,2,0,2,0,2]=true := by native_decide
  simpa only [beq_iff_eq] using singleConstant_getD _ _ h w

theorem four_cups_degree (w : Word) : DegreeLE (fourCups.getD w []) 0 := by
  have hc := allEntries_getD fourCups (fun _ p => bounded 0 p)
    four_cups_nonpositive (by intro; rfl) w
  apply degree_of_bound
  have hh : canonical (fourCups.getD w [])=true ∧
      ((fourCups.getD w []).all (fun x => x.1≤0))=true := by simpa [bounded] using hc
  intro x hx
  exact of_decide_eq_true (List.all_eq_true.mp hh.2 x hx)

def capInversions (j : Nat) : Int :=
  Family.inversions ((triple j).map Revised.decodeLetter)

/-- The cap table in precisely the permutation/inversion convention printed
in the upper-row proof. It is zero on every other three-letter state. -/
theorem eta_inversion_formula : ∀ j : Fin 27,
    eta j = if (triple j).Perm [0,1,2] then monomial (3-capInversions j) else [] := by decide

/-- After multiplication by t, the cap degree is 2-inv(s). The six cases
show that only ABC can exceed the chosen input height. -/
theorem cap_peak_bound : ∀ j : Fin 27, (triple j).Perm [0,1,2] → j.val≠5 →
    2-capInversions j≤height j := by decide

theorem cup_correction_coefficient (j : Fin 27) (w : Word) (e : Int) :
    coeff ((cupCorrection j).getD w []) e=
      if (triple j).Perm [0,1,2] then
        coeff (fourCups.getD w []) (e-(2-capInversions j)) else 0 := by
  have hc := congrArg (fun p => coefficient p e)
    (scaleMap_poly fourCups (shiftScale (eta j) (-1) 1) w)
  change coeff ((cupCorrection j).getD w []) e=
    coeff (mul (fourCups.getD w []) (shiftScale (eta j) (-1) 1)) e at hc
  rw [hc,eta_inversion_formula]
  by_cases hp : (triple j).Perm [0,1,2]
  · rw [if_pos hp,if_pos hp]
    have hs : shiftScale (monomial (3-capInversions j)) (-1) 1=monomial (2-capInversions j) := by
      simp [shiftScale,monomial]
      omega
    rw [hs,Algebra.mul_comm]
    simp [monomial,mul,coeff_add,coeff_shiftScale,coeff]
  · rw [if_neg hp,if_neg hp,Algebra.mul_comm]
    rfl

/-- Derived from the four-cup top monomial and the six cap degrees, rather
than checking the already multiplied correction against a target classifier. -/
theorem cup_excess_coefficient (j : Fin 27) (w : Word) (e : Int) (he : height j<e) :
    coeff ((cupCorrection j).getD w []) e=
      if j.val=5 ∧ w=[0,2,0,2,0,2,0,2] ∧ e=2 then 1 else 0 := by
  rw [cup_correction_coefficient]
  by_cases hp : (triple j).Perm [0,1,2]
  · rw [if_pos hp]
    by_cases hj : j.val=5
    · have heq : j=⟨5,by decide⟩ := Fin.ext hj
      subst j
      have hd : capInversions 5=0 := by decide
      have hh : height 5=1 := by decide
      change height 5<e at he
      rw [hh] at he
      simp only [hd,Int.sub_zero,true_and]
      by_cases he2 : e=2
      · subst e
        simpa only [Int.sub_self,and_true] using four_cups_constant w
      · have ht : 0<e-2 := by omega
        rw [four_cups_degree w (e-2) ht]
        simp [he2]
    · have hb := cap_peak_bound j hp hj
      have ht : 0<e-(2-capInversions j) := by omega
      rw [four_cups_degree w _ ht]
      simp [hj]
  · rw [if_neg hp]
    have hj : j.val≠5 := by
      intro heq
      have hj : j=⟨5,by decide⟩ := Fin.ext heq
      subst j
      exact hp (by decide)
    simp [hj]

theorem mul_neg_coeff (p q : Laurent) (e : Int) :
    coeff (mul p (neg q)) e = -coeff (mul p q) e := by
  induction p generalizing e with
  | nil => rfl
  | cons x p ih =>
    rw [mul,coeff_add,coeff_shiftScale,Algebra.coeff_neg,ih,mul,coeff_add,coeff_shiftScale]
    simp [Int.neg_mul,Int.neg_add]

theorem residual_coefficient (j : Fin 27) (w : Word) (e : Int) :
    coeff ((innerResidual j).getD w []) e =
      coeff ((expand innerSteps (singleton (triple j))).getD w []) e -
        coeff ((cupCorrection j).getD w []) e := by
  have h := congrArg (fun p => coefficient p e) (innerResidual_coordinate j w)
  have hc := congrArg (fun p => coefficient p e)
    (scaleMap_poly fourCups (shiftScale (eta j) (-1) 1) w)
  change coeff ((cupCorrection j).getD w []) e=coeff (mul (fourCups.getD w []) (shiftScale (eta j) (-1) 1)) e at hc
  simp only [coefficient_add,coefficient_ofList] at h
  change _ = _ + coeff (mul (fourCups.getD w []) (neg (shiftScale (eta j) (-1) 1))) e at h
  rw [mul_neg_coeff,← hc] at h
  exact h

/-- Exact coefficient-one cancellation of the sole excessive path. -/
theorem residual_degree (j : Fin 27) (w : Word) :
    DegreeLE ((innerResidual j).getD w []) (height j) := by
  intro e he
  rw [residual_coefficient,LocalPaths.inner_above_coefficient j w e he,
    cup_excess_coefficient j w e he]
  have hw : LocalPaths.word "ACACACAC"=[0,2,0,2,0,2,0,2] := by decide
  rw [hw,Int.sub_self]

theorem outer_composed_degree (j : Fin 27) (out : Word) :
    DegreeLE ((expand cSteps (innerResidual j)).getD out [])
      (-height (encode (out.take 3))+height j) := by
  apply expand_degree
  · intro u p hp
    exact LocalPaths.outer_degree u (List.all_eq_true.mp (residual_support_check j) (u,p) hp) out
  · exact residual_degree j

theorem outer_cups_degree (out : Word) :
    DegreeLE (rawC.getD out []) (-height (encode (out.take 3))) := by
  have h : DegreeLE (rawC.getD out []) (-height (encode (out.take 3))+0) := by
    apply expand_degree
    · intro u p hp
      exact LocalPaths.outer_degree u (List.all_eq_true.mp four_cups_support (u,p) hp) out
    · intro u
      have hc := allEntries_getD fourCups (fun _ p => bounded 0 p) four_cups_nonpositive (by intro; rfl) u
      apply degree_of_bound
      have hh : canonical (fourCups.getD u [])=true ∧ ((fourCups.getD u []).all (fun x => x.1≤0))=true := by simpa [bounded] using hc
      have hb := hh.2
      intro x hx
      exact of_decide_eq_true (List.all_eq_true.mp hb x hx)
  simpa using h

theorem height_interface (i : Fin 27) (w : Word) :
    height (encode ((triple i++w).take 3))=height i := by
  have ht : (triple i++w).take 3=triple i := by simp [triple]
  rw [ht,encode_triple]

/-- Upper-left block is integral by composing the corrected inner map with
the shifted outer map. No final transformed-block degree check is used. -/
theorem upper_expression_integral (i j : Fin 27) (w : Word) :
    DegreeLE (shiftScale (add ((rawB j).getD (triple i++w) [])
      (neg (mul (rawC.getD (triple i++w) []) (shiftScale (eta j) (-1) 1))))
        (height i-height j) 1) 0 := by
  have h := degree_congr (upper_factorization j (triple i++w)).symm
    (outer_composed_degree j (triple i++w))
  rw [height_interface] at h
  have hs := degree_shift h (height i-height j) 1
  have hb : -height i+height j+(height i-height j)=0 := by omega
  simpa only [hb] using hs

theorem upper_scalar_expression_integral (i : Fin 27) (w : Word) :
    DegreeLE (shiftScale (rawC.getD (triple i++w) []) (height i) 1) 0 := by
  have h := outer_cups_degree (triple i++w)
  rw [height_interface] at h
  have hs := degree_shift h (height i) 1
  have hz : -height i+height i=0 := by omega
  rw [hz] at hs
  exact hs

#print axioms residual_degree
#print axioms upper_expression_integral
end WebMu.Revised.LocalDegreeProof
