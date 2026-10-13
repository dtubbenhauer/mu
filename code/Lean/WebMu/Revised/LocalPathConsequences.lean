import WebMu.Revised.StagedPathDerivations
import WebMu.Revised.ElementaryPathDerivations
import WebMu.Revised.LocalDegreeAlgebra

/-! Coefficient consequences derived from the uncollected path certificates. -/
namespace WebMu.Revised.LocalPaths
open Laurent Algebra Bar LocalDegreeProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem allPaths_contains (n : Nat) (ss : List Step) (u : Word)
    (hu : validWord n u = true) (p : Path) (hp : p ∈ downPaths ss u) : p ∈ allPaths n ss := by
  exact List.mem_flatMap.mpr ⟨u,(completeWords_mem n u).mpr hu,hp⟩

theorem inner_above_coefficient (j : Fin 27) (w : Word) (e : Int) (he : height j < e) :
    coeff ((expand innerSteps (singleton (triple j))).getD w []) e =
      if j.val=5 ∧ w=word "ACACACAC" ∧ e=2 then 1 else 0 := by
  rw [paths_coefficient,pathCoefficient_filter _ w e (fun p => height j < p.degree)
    (by intro p _ hp; simp [hp,he]),Staged.inner_excess_per_input]
  by_cases hj : j.val=5
  · simp only [hj,↓reduceIte]
    simp only [pathCoefficient,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Int.add_zero,offender_exact_data.2.1,offender_exact_data.2.2.1,offender_exact_data.2.2.2,
      Bool.and_eq_true,beq_iff_eq]
    simp [eq_comm]
  · simp [hj,pathCoefficient]

theorem outer_degree (u : Word) (hu : validWord 8 u = true) (out : Word) :
    DegreeLE ((expand cSteps (singleton u)).getD out []) (-height (encode (out.take 3))) := by
  apply paths_coordinate_degree_bound
  intro p hp he
  have h := List.all_eq_true.mp Elementary.outer_path_bound_written p (allPaths_contains 8 cSteps u hu p hp)
  simp only [decide_eq_true_eq] at h
  rw [he] at h
  omega

theorem prefix_degree (j : Fin 27) (w : Word) :
    DegreeLE ((expand shortPrefixSteps (singleton (triple j))).getD w []) (height j) := by
  apply paths_degree_bound
  intro p hp
  have h := List.all_eq_true.mp Staged.prefix_path_height_bound p
    (allPaths_contains 3 shortPrefixSteps (triple j) ((show ∀ j : Fin 27, validWord 3 (triple j) = true from by decide) j) p hp)
  simp only [decide_eq_true_eq] at h
  rw [paths_input shortPrefixSteps.reverse (triple j) p hp] at h
  have hj : encode (triple j) = j.val := by
    have hh : ∀ j : Fin 27, encode (triple j) = j.val := by decide
    exact hh j
  simpa [hj] using h

theorem shifted_degree_from_paths (ss : List Step) (u : Word) (hgt : Word → Int)
    (h : (downPaths ss u).all (fun p => p.degree + hgt p.output ≤ 0) = true) (w : Word) :
    DegreeLE ((expand ss (singleton u)).getD w []) (-hgt w) := by
  apply paths_coordinate_degree_bound
  intro p hp hw
  have hb := List.all_eq_true.mp h p hp
  simp only [decide_eq_true_eq] at hb
  rw [hw] at hb
  omega

theorem single_top_constant (ss : List Step) (u : Word) (hgt : Word → Int) (p₀ : Path)
    (h : (downPaths ss u).filter (fun p => 0 ≤ p.degree + hgt p.output) = [p₀])
    (hd : p₀.degree=0) (hc : p₀.multiplicity=1) (hh : hgt p₀.output=0) (w : Word) :
    coeff ((expand ss (singleton u)).getD w []) (-hgt w) = if w=p₀.output then 1 else 0 := by
  rw [paths_coefficient,pathCoefficient_filter_at _ w (-hgt w)
    (fun p => 0 ≤ p.degree + hgt p.output) (by
      intro p _ hw he
      simp only [hw,he,decide_eq_true_eq]
      omega),h]
  unfold pathCoefficient
  by_cases hw : w=p₀.output
  · simp [hd,hc,hw,hh]
  · simp [hw,Ne.symm,hd]

theorem tail_degree (w : Word) :
    DegreeLE (rawQ.getD w []) (-height (encode (w.take 3))) :=
  shifted_degree_from_paths tailSteps [] (fun w => height (encode (w.take 3))) Staged.tail_path_height_bound w

theorem tail_shifted_constant (w : Word) :
    coeff (rawQ.getD w []) (-height (encode (w.take 3))) =
      if w=word "AAABBCBCC" then 1 else 0 := by
  exact single_top_constant tailSteps [] (fun w => height (encode (w.take 3))) tailZeroRoute
    Staged.tail_unique_shifted_constant (by decide) (by decide) (by decide) w

theorem prefix_constant (w : Word) :
    coeff ((expand shortPrefixSteps (singleton (word "AAA"))).getD w []) 0 =
      if w=word "ABAAAC" then 1 else 0 := by
  exact single_top_constant shortPrefixSteps (word "AAA") (fun _ => 0) prefixRoute
    Staged.prefix_unique_constant (by decide) (by decide) rfl w

theorem aaa_block_shifted_constant (w : Word) :
    coeff ((rawB 0).getD w []) (-height (encode (w.take 3))) =
      if w=word "AAABBBAACACC" then 1 else 0 := by
  exact single_top_constant blockSteps (word "AAA") (fun w => height (encode (w.take 3))) aaaBlockRoute
    Staged.aaa_block_constant (by decide) (by decide) (by decide) w


theorem summand_as_expand (s : List Step × List Step) (i : Nat) :
    summand s i = expand (s.1 ++ s.2.reverse) (singleton (triple i)) := by
  simp [summand,expand,compose,List.reverse_append,List.foldl_append]

theorem summand_ascent_degree (ss : List (List Step × List Step))
    (h : (ss.flatMap fun s => (completeWords 3).flatMap (summandPaths s)).all
      (fun p => p.degree ≤ ascWord p.input) = true)
    (s : List Step × List Step) (hs : s ∈ ss) (j : Fin 27) (w : Word) :
    DegreeLE ((summand s j).getD w []) (ascWord (triple j)) := by
  rw [summand_as_expand]
  apply paths_degree_bound
  intro p hp
  have hv : validWord 3 (triple j)=true :=
    (show ∀ j : Fin 27, validWord 3 (triple j)=true from by decide) j
  have hm : p ∈ ss.flatMap (fun s => (completeWords 3).flatMap (summandPaths s)) :=
    List.mem_flatMap.mpr ⟨s,hs,List.mem_flatMap.mpr
      ⟨triple j,(completeWords_mem 3 _).mpr hv,hp⟩⟩
  have hh := List.all_eq_true.mp h p hm
  simp only [decide_eq_true_eq] at hh
  rw [paths_input (s.1++s.2.reverse).reverse (triple j) p hp] at hh
  exact hh

theorem sumTensor_degree (xs : List Tensor) (b : Int)
    (h : ∀ x ∈ xs, ∀ w, DegreeLE (x.getD w []) b) (w : Word) :
    DegreeLE ((sumTensor xs).getD w []) b := by
  intro e he
  change coefficient (ofList ((sumTensor xs).getD w [])) e = 0
  rw [show ofList ((sumTensor xs).getD w []) =
    total xs (fun x => ofList (x.getD w [])) from sumMap_poly xs w]
  have hh := TruncatedGrowth.total_coefficient_congr xs
    (fun x => ofList (x.getD w [])) (fun _ => 0) e (by
      intro x hx
      exact h x hx w e he)
  simpa using hh

theorem d₀_ascent_degree (j : Fin 27) (w : Word) :
    DegreeLE ((rawD₀ j).getD w []) (ascWord (triple j)) := by
  apply sumTensor_degree
  intro x hx w
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
  exact summand_ascent_degree _ correction_ascent_paths s hs j w

theorem h_ascent_degree (j : Fin 27) (w : Word) :
    DegreeLE ((rawH j).getD w []) (ascWord (triple j)) := by
  apply sumTensor_degree
  intro x hx w
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
  exact summand_ascent_degree _ h_ascent_paths s hs j w

theorem ascent_le_height (j : Fin 27) : ascWord (triple j) ≤ 1+height j := by
  have h := List.all_eq_true.mp ascent_height (triple j)
    ((completeWords_mem 3 _).mpr ((show ∀ j : Fin 27, validWord 3 (triple j)=true from by decide) j))
  have he : encode (triple j)=j.val := (show ∀ j : Fin 27, encode (triple j)=j.val from by decide) j
  simpa [he] using h


theorem single_top_degree (ss : List Step) (u : Word) (hgt : Word → Int) (p₀ : Path)
    (h : (downPaths ss u).filter (fun p => 0 ≤ p.degree + hgt p.output) = [p₀])
    (hz : p₀.degree + hgt p₀.output = 0) (w : Word) :
    DegreeLE ((expand ss (singleton u)).getD w []) (-hgt w) := by
  apply shifted_degree_from_paths
  apply List.all_eq_true.mpr
  intro p hp
  apply decide_eq_true
  by_cases hb : p.degree + hgt p.output ≤ 0
  · exact hb
  have hm : p ∈ (downPaths ss u).filter (fun p => 0 ≤ p.degree + hgt p.output) :=
    List.mem_filter.mpr ⟨hp,by simp only [decide_eq_true_eq]; omega⟩
  rw [h,List.mem_singleton] at hm
  rw [hm,hz]
  exact Int.le_refl _

theorem aaa_block_degree (w : Word) :
    DegreeLE ((rawB 0).getD w []) (-height (encode (w.take 3))) :=
  single_top_degree blockSteps (word "AAA") (fun w => height (encode (w.take 3))) aaaBlockRoute
    Staged.aaa_block_constant (by decide) w

end WebMu.Revised.LocalPaths
