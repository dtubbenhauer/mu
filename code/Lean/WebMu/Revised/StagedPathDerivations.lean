import WebMu.Revised.AAAOuterPaths
import WebMu.Revised.StagedMiddle
import WebMu.Revised.StagedS

/-! Deductions from the intermediate path statements printed in the manuscript.
In particular the tail's nine listed paths, not a separate complete shifted
classifier, supply both the bound and the constant term. -/
namespace WebMu.Revised.LocalPaths.Staged
open Laurent Algebra Bar
local instance : BEq Path := instBEqOfDecidableEq
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_bounds (n : Nat) : 0 ≤ height n ∧ height n ≤ 1 := by
  unfold height
  split <;> omega

theorem tail_unique_shifted_constant :
    (downPaths tailSteps []).filter
      (fun p => 0 ≤ p.degree + height (encode (p.output.take 3))) = [tailZeroRoute] := by
  have h : (downPaths tailSteps []).filter
      (fun p => 0 ≤ p.degree + height (encode (p.output.take 3))) =
      ((downPaths tailSteps []).filter (fun p => -1 ≤ p.degree)).filter
        (fun p => 0 ≤ p.degree + height (encode (p.output.take 3))) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro p hp
    have hh := height_bounds (encode (p.output.take 3))
    by_cases hd : 0 ≤ p.degree + height (encode (p.output.take 3))
    · have he : -1 ≤ p.degree := by omega
      simp [hd,he]
    · simp [hd]
  rw [h,tail_complete_top_paths]
  decide

theorem tail_path_height_bound :
    (downPaths tailSteps []).all
      (fun p => p.degree+height (encode (p.output.take 3)) ≤ 0)=true := by
  apply List.all_eq_true.mpr
  intro p hp
  apply decide_eq_true
  by_cases h : 0 ≤ p.degree+height (encode (p.output.take 3))
  · have hm : p ∈ (downPaths tailSteps []).filter
        (fun p => 0 ≤ p.degree+height (encode (p.output.take 3))) :=
      List.mem_filter.mpr ⟨hp,by simpa⟩
    rw [tail_unique_shifted_constant,List.mem_singleton] at hm
    subst p
    decide
  · omega

theorem downPaths_nil (u : Word) : downPaths [] u=[initial u] := rfl

theorem paths_member_input (ss : List Step) (u : Word) (p : Path)
    (h : p ∈ downPaths ss u) : p.input=u := paths_input ss.reverse u p h

theorem member_allPaths (n : Nat) (ss : List Step) (u : Word)
    (hu : validWord n u=true) (p : Path) (hp : p ∈ downPaths ss u) : p ∈ allPaths n ss :=
  List.mem_flatMap.mpr ⟨u,(completeWords_mem n u).mpr hu,hp⟩

theorem triple_valid (i : Fin 27) : validWord 3 (triple i)=true := by
  exact (show ∀ i : Fin 27, validWord 3 (triple i)=true from by decide) i

theorem triple_encoding (i : Fin 27) : encode (triple i)=i.val := by
  exact (show ∀ i : Fin 27, encode (triple i)=i.val from by decide) i

theorem first_s_bound (u : Word) (hu : validWord 3 u=true) (p : Path)
    (hp : p ∈ downPaths sSteps u) :
    p.degree ≤ if u=word "ABC" then 1 else 0 := by
  by_cases hd : 0 < p.degree
  · have hm : p ∈ (allPaths 3 sSteps).filter (fun p => 0 < p.degree) :=
      List.mem_filter.mpr ⟨member_allPaths 3 sSteps u hu p hp,by simpa⟩
    rw [SDerivation.s_unique_positive_written,List.mem_singleton] at hm
    have hi := paths_member_input sSteps u p hp
    subst p
    have hu' : u=word "ABC" := hi.symm
    rw [hu']
    decide
  · split <;> omega

theorem first_s_support :
    (allPaths 3 sSteps).all (fun p => validWord 4 p.output)=true := by native_decide

theorem middle_support :
    (allPaths 4 middleSteps).all (fun p => validWord 7 p.output)=true := by native_decide

theorem exceptional_le_ascent (i : Fin 27) :
    (if triple i=word "ABC" then (1:Int) else 0) ≤ ascWord (triple i) := by
  exact (show ∀ i : Fin 27,
    (if triple i=word "ABC" then (1:Int) else 0) ≤ ascWord (triple i) from by decide) i

/-- The same three-step S table with four untouched spectator letters. -/
theorem second_s_table : (allPaths 7 sSteps).all (fun p =>
    p.degree ≤ 1 && (p.degree ≤ 0 || p.input.take 3 == word "ABC"))=true :=
  SDerivation.second_s_table_written

def secondPositive : Path := route "ABCACAC"
  [("ABBCACAC",0),("ACACACAC",0),("ACACACAC",1)]

theorem second_s_positive :
    (downPaths sSteps (word "ABCACAC")).filter (fun p => 0<p.degree)=[secondPositive] :=
  SDerivation.second_s_positive_written

theorem s_to_acac_height : (allPaths 3 sSteps).all (fun p =>
    p.output != word "ACAC" || height (encode p.input)==1)=true := by
  apply List.all_eq_true.mpr
  intro p hp
  by_cases ho : p.output=word "ACAC"
  · have hm : p ∈ (allPaths 3 sSteps).filter (fun p => p.output==word "ACAC") :=
      List.mem_filter.mpr ⟨hp,by simp [ho]⟩
    rw [SDerivation.s_complete_ACAC_written] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h | h | h <;> subst p <;> decide
  · simp [ho]

theorem inner_excessive_forced (i : Fin 27) (p : Path)
    (hp : p ∈ downPaths innerSteps (triple i)) (he : height i<p.degree) :
    i.val=5 ∧ p=offenderRoute := by
  have hs : innerSteps = sSteps ++ (middleSteps ++ sSteps) := by
    simp [innerSteps,List.append_assoc]
  rw [hs] at hp
  obtain ⟨r,hr,q3,h3,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hp
  obtain ⟨q1,h1,q2,h2,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hr
  have v1 := List.all_eq_true.mp first_s_support q1
    (member_allPaths 3 sSteps _ (triple_valid i) _ h1)
  have v2 := List.all_eq_true.mp middle_support q2
    (member_allPaths 4 middleSteps _ v1 _ h2)
  have d1 := first_s_bound _ (triple_valid i) q1 h1
  have d2 := List.all_eq_true.mp Middle.middle_nonpositive_written q2
    (member_allPaths 4 middleSteps _ v1 _ h2)
  have d3 := List.all_eq_true.mp second_s_table q3
    (member_allPaths 7 sSteps _ v2 _ h3)
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq] at d2 d3
  have hi := paths_member_input sSteps _ q1 h1
  have hm := paths_member_input middleSteps _ q2 h2
  have hl := paths_member_input sSteps _ q3 h3
  change height i < q1.degree+q2.degree+q3.degree at he
  have di : (if triple i=word "ABC" then (1:Int) else 0) ≤ height i := by
    exact (show ∀ i : Fin 27,
      (if triple i=word "ABC" then (1:Int) else 0) ≤ height i from by decide) i
  have hpos : 0<q3.degree := by omega
  have hprefix : q2.output.take 3=word "ABC" := by
    rcases d3.2 with h | h
    · omega
    · simpa only [hl] using h
  have hz : q2.degree=0 := by omega
  have hmid : q2=middleRoute := by
    have hmem : q2 ∈ (allPaths 4 middleSteps).filter
        (fun p => p.degree==0 && p.output.take 3==word "ABC") :=
      List.mem_filter.mpr ⟨member_allPaths 4 middleSteps _ v1 _ h2,by simp [hz,hprefix]⟩
    simpa only [Middle.middle_unique_zero_ABC_written,List.mem_singleton] using hmem
  have hACAC : q1.output=word "ACAC" := by simpa only [hmid] using hm.symm
  have hheight : height i=1 := by
    have hc := List.all_eq_true.mp s_to_acac_height q1
      (member_allPaths 3 sSteps _ (triple_valid i) _ h1)
    simpa [hACAC,hi,triple_encoding] using hc
  have h1pos : 0<q1.degree := by omega
  have hfirst : q1=route "ABC" [("ABBC",0),("ACAC",0),("ACAC",1)] := by
    have hmem : q1 ∈ (allPaths 3 sSteps).filter (fun p => 0<p.degree) :=
      List.mem_filter.mpr ⟨member_allPaths 3 sSteps _ (triple_valid i) _ h1,by simpa⟩
    simpa only [SDerivation.s_unique_positive_written,List.mem_singleton] using hmem
  have heq : i.val=5 := by
    have ht : triple i=word "ABC" := by simpa only [hfirst] using hi.symm
    have hh := congrArg encode ht
    simpa only [triple_encoding] using hh
  have hlast : q3=secondPositive := by
    have hmem : q3 ∈ (downPaths sSteps (word "ABCACAC")).filter (fun p => 0<p.degree) := by
      refine List.mem_filter.mpr ⟨?_,by simpa⟩
      simpa only [hmid] using h3
    simpa only [second_s_positive,List.mem_singleton] using hmem
  refine ⟨heq,?_⟩
  rw [hfirst,hmid,hlast]
  rfl

theorem singleton_of_unique {α : Type} (xs : List α) (a : α) (hn : xs.Nodup)
    (ha : a∈xs) (hu : ∀ x∈xs, x=a) : xs=[a] := by
  cases xs with
  | nil => simp at ha
  | cons x xs =>
    have hx := hu x (by simp)
    subst x
    have he : xs=[] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro b hb
      have hba := hu b (by simp [hb])
      have hnot := (List.nodup_cons.mp hn).1
      exact hnot (hba ▸ hb))
    simp [he]

theorem inner_excess_per_input (i : Fin 27) :
    (downPaths innerSteps (triple i)).filter (fun p => height i < p.degree) =
      if i.val=5 then [offenderRoute] else [] := by
  by_cases hi : i.val=5
  · rw [if_pos hi]
    have hn : ((downPaths innerSteps (triple i)).filter (fun p => height i < p.degree)).Nodup :=
      (show ∀ i : Fin 27, ((downPaths innerSteps (triple i)).filter (fun p => height i < p.degree)).Nodup from by native_decide) i
    apply singleton_of_unique _ _ hn
    · have he : i=⟨5,by decide⟩ := Fin.ext hi
      subst i
      native_decide
    · intro p hp
      obtain ⟨hm,hd⟩ := List.mem_filter.mp hp
      exact (inner_excessive_forced i p hm (by simpa using hd)).2
  · rw [if_neg hi]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    obtain ⟨hm,hd⟩ := List.mem_filter.mp hp
    exact hi (inner_excessive_forced i p hm (by simpa using hd)).1

def aaaLastRoute : Path := route "AAAABBC"
  [("ABAAABBC",0),("AABAABBC",0),("AAABABBC",0)]

theorem aaa_last_zero : (downPaths sSteps (word "AAAABBC")).filter
    (fun p => p.degree==0)=[aaaLastRoute] := by
  have hc := SDerivation.s_suffix (word "AAA") (word "ABBC") (by decide)
  change downPaths sSteps (word "AAAABBC")=_ at hc
  rw [hc,List.filter_map]
  change ((downPaths sSteps (word "AAA")).filter (fun p => p.degree==0)).map
    (frame [] (word "ABBC"))=_
  rw [SDerivation.s_AAA_complete_paths_written]
  rfl

theorem aaa_inner_forced (p : Path) (hp : p ∈ downPaths innerSteps (word "AAA"))
    (he : 0 ≤ p.degree) : p=aaaInnerRoute := by
  rw [show innerSteps=sSteps++(middleSteps++sSteps) by simp [innerSteps,List.append_assoc]] at hp
  obtain ⟨r,hr,q3,h3,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hp
  obtain ⟨q1,h1,q2,h2,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hr
  have hv : validWord 3 (word "AAA")=true := by decide
  have v1 := List.all_eq_true.mp first_s_support q1 (member_allPaths _ _ _ hv _ h1)
  have v2 := List.all_eq_true.mp middle_support q2 (member_allPaths _ _ _ v1 _ h2)
  have d1 := first_s_bound _ hv q1 h1
  have d2 := List.all_eq_true.mp Middle.middle_nonpositive_written q2 (member_allPaths _ _ _ v1 _ h2)
  have d3 := List.all_eq_true.mp second_s_table q3 (member_allPaths _ _ _ v2 _ h3)
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq] at d2 d3
  have hl := paths_member_input sSteps _ q3 h3
  change 0 ≤ q1.degree+q2.degree+q3.degree at he
  have hfirst := h1
  rw [SDerivation.s_AAA_complete_paths_written] at hfirst
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hfirst
  have hnot : q2.output.take 3 ≠ word "ABC" := by
    have hm : q2 ∈ downPaths middleSteps (word "AAAB") ++
        downPaths middleSteps (word "BAAA") := by
      rcases hfirst with h | h
      · exact List.mem_append_left _ (by simpa only [h] using h2)
      · exact List.mem_append_right _ (by simpa only [h] using h2)
    have hn := List.all_eq_true.mp Middle.aaa_no_second_positive_written q2 hm
    simpa using hn
  have hd3 : q3.degree ≤ 0 := by
    rcases d3.2 with h | h
    · exact h
    · exact False.elim (hnot (by simpa only [hl] using h))
  rcases hfirst with hfirst | hfirst
  · have hd1 : q1.degree=0 := by rw [hfirst]; rfl
    have hd2 : q2.degree=0 := by omega
    have hd3' : q3.degree=0 := by omega
    have hmid : q2=aaaMiddleRoute := by
      have hm : q2 ∈ (downPaths middleSteps (word "AAAB")).filter (fun p => p.degree==0) :=
        List.mem_filter.mpr ⟨by simpa only [hfirst] using h2,by simp [hd2]⟩
      simpa only [Middle.aaa_middle_constant_written,List.mem_singleton] using hm
    have hlast : q3=aaaLastRoute := by
      have hm : q3 ∈ (downPaths sSteps (word "AAAABBC")).filter (fun p => p.degree==0) :=
        List.mem_filter.mpr ⟨by simpa only [hmid] using h3,by simp [hd3']⟩
      simpa only [aaa_last_zero,List.mem_singleton] using hm
    rw [hfirst,hmid,hlast]
    rfl
  · have hd1 : q1.degree = -1 := by rw [hfirst]; rfl
    omega

theorem aaa_inner_constant :
    (downPaths innerSteps (word "AAA")).filter (fun p => 0≤p.degree)=[aaaInnerRoute] := by
  have hn : ((downPaths innerSteps (word "AAA")).filter (fun p => 0≤p.degree)).Nodup := by native_decide
  apply singleton_of_unique _ _ hn
  · native_decide
  · intro p hp
    obtain ⟨hm,hd⟩ := List.mem_filter.mp hp
    exact aaa_inner_forced p hm (by simpa using hd)

theorem aaa_inner_nonpositive (p : Path) (hp : p ∈ downPaths innerSteps (word "AAA")) :
    p.degree ≤ 0 := by
  by_cases h : 0 ≤ p.degree
  · rw [aaa_inner_forced p hp h]
    decide
  · omega

theorem aaa_block_forced (p : Path) (hp : p ∈ downPaths blockSteps (word "AAA"))
    (he : 0 ≤ p.degree+height (encode (p.output.take 3))) : p=aaaBlockRoute := by
  rw [block_factorization] at hp
  obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hp
  have hqdeg := aaa_inner_nonpositive q hq
  have hv : validWord 8 q.output=true := by
    have hb : (downPaths innerSteps (word "AAA")).all (fun p => validWord 8 p.output)=true := by
      native_decide
    exact List.all_eq_true.mp hb q hq
  have hrdeg := List.all_eq_true.mp Elementary.outer_path_bound_written r (member_allPaths _ _ _ hv _ hr)
  simp only [decide_eq_true_eq] at hrdeg
  change 0 ≤ q.degree+r.degree+height (encode (r.output.take 3)) at he
  have hqpos : 0 ≤ q.degree := by omega
  have hqeq := aaa_inner_forced q hq hqpos
  have hre : r=aaaOuterRoute := by
    have hd : 0≤r.degree+height (encode (r.output.take 3)) := by omega
    exact AAAOuter.shifted_forced r (by simpa only [hqeq] using hr) hd
  rw [hqeq,hre]
  rfl

theorem aaa_block_constant :
    (downPaths blockSteps (word "AAA")).filter
      (fun p => 0 ≤ p.degree+height (encode (p.output.take 3)))=[aaaBlockRoute] := by
  have hn : ((downPaths blockSteps (word "AAA")).filter
      (fun p => 0 ≤ p.degree+height (encode (p.output.take 3)))).Nodup := by native_decide
  apply singleton_of_unique _ _ hn
  · native_decide
  · intro p hp
    obtain ⟨hm,hd⟩ := List.mem_filter.mp hp
    exact aaa_block_forced p hm (by simpa using hd)

def prefixYs : List Step := [(.y,0),(.y,3)]

theorem prefix_y_nonpositive : (allPaths 4 prefixYs).all (fun p => p.degree≤0)=true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨u,_,hp⟩ := List.mem_flatMap.mp hp
  exact decide_eq_true (AAAOuter.nonpositive prefixYs (by simp [prefixYs,GrowthBridge.opBound]) u p hp)

def prefixYRoute : Path := route "AAAB" [("AAAAC",0),("ABAAAC",0)]

theorem prefix_y_zero : (downPaths prefixYs (word "AAAB")).filter
    (fun p => 0≤p.degree)=[prefixYRoute] := by native_decide

theorem prefix_path_degree (u : Word) (hu : validWord 3 u=true) (p : Path)
    (hp : p ∈ downPaths shortPrefixSteps u) :
    p.degree ≤ if u=word "ABC" then 1 else 0 := by
  rw [show shortPrefixSteps=prefixYs++sSteps from rfl] at hp
  obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hp
  have hv := List.all_eq_true.mp first_s_support q (member_allPaths _ _ _ hu _ hq)
  have hqdeg := first_s_bound u hu q hq
  have hrdeg := List.all_eq_true.mp prefix_y_nonpositive r (member_allPaths _ _ _ hv _ hr)
  simp only [decide_eq_true_eq] at hrdeg
  change q.degree+r.degree ≤ _
  omega

theorem prefix_path_height_bound : (allPaths 3 shortPrefixSteps).all
    (fun p => p.degree≤height (encode p.input))=true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp hp
  have hv := (completeWords_mem 3 u).mp hu
  have hb := prefix_path_degree u hv p hp
  have hi := paths_member_input _ u p hp
  have hh : (if u=word "ABC" then (1:Int) else 0) ≤ height (encode u) := by
    by_cases he : u=word "ABC"
    · rw [he]; decide
    · simpa [he] using (height_bounds (encode u)).1
  apply decide_eq_true
  rw [hi]
  omega

theorem prefix_unique_constant :
    (downPaths shortPrefixSteps (word "AAA")).filter (fun p => 0≤p.degree)=[prefixRoute] := by
  have hn : (downPaths shortPrefixSteps (word "AAA")).Nodup := by native_decide
  apply singleton_of_unique _ _ (hn.filter _)
  · native_decide
  · intro p hp
    obtain ⟨hm,hd⟩ := List.mem_filter.mp hp
    have hd' : 0≤p.degree := by simpa using hd
    rw [show shortPrefixSteps=prefixYs++sSteps from rfl] at hm
    obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hm
    have hv := List.all_eq_true.mp first_s_support q (member_allPaths _ _ _ (by decide) _ hq)
    have hrdeg := List.all_eq_true.mp prefix_y_nonpositive r (member_allPaths _ _ _ hv _ hr)
    simp only [decide_eq_true_eq] at hrdeg
    change 0≤q.degree+r.degree at hd'
    rw [SDerivation.s_AAA_complete_paths_written] at hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq | hq
    · have hz : q.degree=0 := by rw [hq]; rfl
      have hpos : 0≤r.degree := by omega
      have he : r=prefixYRoute := by
        have hm : r ∈ (downPaths prefixYs (word "AAAB")).filter (fun p => 0≤p.degree) :=
          List.mem_filter.mpr ⟨by simpa only [hq] using hr,by simpa⟩
        simpa only [prefix_y_zero,List.mem_singleton] using hm
      rw [hq,he]
      rfl
    · have hz : q.degree = -1 := by rw [hq]; rfl
      omega

end WebMu.Revised.LocalPaths.Staged
