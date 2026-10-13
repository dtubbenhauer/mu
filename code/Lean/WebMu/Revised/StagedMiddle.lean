import WebMu.Revised.PathContext

/-! The backward forced R,L,R branches in the printed middle-map proof. -/
namespace WebMu.Revised.LocalPaths.Middle
open Laurent Algebra Bar Elementary
local instance : BEq Path := instBEqOfDecidableEq
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem fits_r (a b : Nat) (ha : a<3) (hb : b<3) : fits rSteps.reverse [a,b]=true := by
  exact (show ∀ a b : Fin 3, fits rSteps.reverse [a,b]=true from by decide) ⟨a,ha⟩ ⟨b,hb⟩
theorem fits_l (a b : Nat) (ha : a<3) (hb : b<3) : fits lSteps.reverse [a,b]=true := by
  exact (show ∀ a b : Fin 3, fits lSteps.reverse [a,b]=true from by decide) ⟨a,ha⟩ ⟨b,hb⟩

theorem small_support (ss : List Step) (hs : ss=rSteps ∨ ss=lSteps)
    (a b : Nat) (ha : a<3) (hb : b<3) (p : Path) (hp : p∈downPaths ss [a,b]) :
    ∃ x y z, p.output=[x,y,z] ∧ x<3 ∧ y<3 ∧ z<3 := by
  have hc : (allPaths 2 ss).all (fun p => validWord 3 p.output)=true := by
    rcases hs with rfl | rfl <;> decide
  have hm : p∈allPaths 2 ss := List.mem_flatMap.mpr
    ⟨[a,b],(completeWords_mem 2 _).mpr (by simp [validWord,ha,hb]),hp⟩
  have hv := List.all_eq_true.mp hc p hm
  obtain ⟨hl,hv⟩ := validWord_iff _ _ |>.mp hv
  generalize heq : p.output=o at hl hv ⊢
  rcases o with _ | ⟨x,xs⟩
  · simp at hl
  rcases xs with _ | ⟨y,xs⟩
  · simp at hl
  rcases xs with _ | ⟨z,xs⟩
  · simp at hl
  have he : xs=[] := by simpa using hl
  subst xs
  exact ⟨x,y,z,rfl,hv x (by simp),hv y (by simp),hv z (by simp)⟩

def rBC : Path := route "BC" [("CAC",-1),("CAC",1)]
def lBC : Path := route "BC" [("BBC",0),("CAC",0)]
def rCA : Path := route "CA" [("BCA",0),("BBB",0)]

/-- The three small cases used in the backward argument, with histories. -/
theorem r_zero_first_C :
    (allPaths 2 rSteps).filter (fun p => p.degree==0 && p.output.take 1==word "C")=[rBC] := by decide
theorem l_zero_first_C :
    (allPaths 2 lSteps).filter (fun p => p.degree==0 && p.output.take 1==word "C")=[lBC] := by decide
theorem r_zero_BBB :
    (allPaths 2 rSteps).filter (fun p => p.degree==0 && p.output==word "BBB")=[rCA] := by decide

def Description (a b c d : Nat) (p : Path) : Prop :=
  ∃ (x y z i j k l m n : Nat) (q₁ q₂ q₃ : Path),
    q₁∈downPaths rSteps [b,c] ∧ q₁.output=[x,y,z] ∧
    q₂∈downPaths lSteps [z,d] ∧ q₂.output=[i,j,k] ∧
    q₃∈downPaths rSteps [y,i] ∧ q₃.output=[l,m,n] ∧
    (x<3 ∧ y<3 ∧ z<3 ∧ i<3 ∧ j<3 ∧ k<3) ∧
    p=join (join (frame [a] [d] q₁) (frame [a,x,y] [] q₂)) (frame [a,x] [j,k] q₃)

/-- Factor each actual six-step path into its three two-step local paths,
retaining the exact boundary order and all intermediate elementary edges. -/
theorem describe (a b c d : Nat) (hb : b<3) (hc : c<3) (hd : d<3)
    (p : Path) (hp : p∈downPaths middleSteps [a,b,c,d]) : Description a b c d p := by
  have he : middleSteps=(rSteps.map (shiftStep 2))++
      ((lSteps.map (shiftStep 3))++(rSteps.map (shiftStep 1))) := rfl
  rw [he] at hp
  obtain ⟨q,hq,q₃,h₃,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hp
  obtain ⟨q₁,h₁,q₂,h₂,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hq
  have hc₁ := downPaths_context rSteps [a] [b,c] [d] (fits_r b c hb hc)
  change q₁∈downPaths (rSteps.map (shiftStep 1)) ([a]++[b,c]++[d]) at h₁
  simp only [List.length_cons,List.length_nil] at hc₁
  rw [hc₁] at h₁
  obtain ⟨r₁,hr₁,rfl⟩ := List.mem_map.mp h₁
  obtain ⟨x,y,z,ho₁,hx,hy,hz⟩ := small_support rSteps (Or.inl rfl) b c hb hc r₁ hr₁
  have hc₂ := downPaths_context lSteps [a,x,y] [z,d] [] (fits_l z d hz hd)
  change q₂∈downPaths (lSteps.map (shiftStep 3)) (frame [a] [d] r₁).output at h₂
  simp only [frame,ho₁,List.cons_append,List.nil_append] at h₂
  change q₂∈downPaths (lSteps.map (shiftStep 3)) ([a,x,y]++[z,d]++[]) at h₂
  simp only [List.length_cons,List.length_nil] at hc₂
  rw [hc₂] at h₂
  obtain ⟨r₂,hr₂,rfl⟩ := List.mem_map.mp h₂
  obtain ⟨i,j,k,ho₂,hi,hj,hk⟩ := small_support lSteps (Or.inr rfl) z d hz hd r₂ hr₂
  have hc₃ := downPaths_context rSteps [a,x] [y,i] [j,k] (fits_r y i hy hi)
  change q₃∈downPaths (rSteps.map (shiftStep 2)) (frame [a,x,y] [] r₂).output at h₃
  simp only [frame,ho₂,List.cons_append,List.nil_append,List.append_nil] at h₃
  change q₃∈downPaths (rSteps.map (shiftStep 2)) ([a,x]++[y,i]++[j,k]) at h₃
  simp only [List.length_cons,List.length_nil] at hc₃
  rw [hc₃] at h₃
  obtain ⟨r₃,hr₃,rfl⟩ := List.mem_map.mp h₃
  obtain ⟨l,m,n,ho₃,_⟩ := small_support rSteps (Or.inl rfl) y i hy hi r₃ hr₃
  exact ⟨x,y,z,i,j,k,l,m,n,r₁,r₂,r₃,hr₁,ho₁,hr₂,ho₂,hr₃,ho₃,
    ⟨hx,hy,hz,hi,hj,hk⟩,rfl⟩

theorem member_small (ss : List Step) (a b : Nat) (ha : a<3) (hb : b<3)
    (p : Path) (hp : p∈downPaths ss [a,b]) : p∈allPaths 2 ss :=
  List.mem_flatMap.mpr ⟨[a,b],(completeWords_mem 2 _).mpr (by simp [validWord,ha,hb]),hp⟩

theorem middle_four_bound (a b c d : Nat) (hb : b<3) (hc : c<3) (hd : d<3)
    (p : Path) (hp : p∈downPaths middleSteps [a,b,c,d]) : p.degree≤0 := by
  obtain ⟨x,y,z,i,j,k,l,m,n,q₁,q₂,q₃,h₁,_,h₂,_,h₃,_,hv,rfl⟩ := describe a b c d hb hc hd p hp
  have d₁ := r_two_degree b c hb hc q₁ h₁
  have d₂ := l_two_degree z d hv.2.2.1 hd q₂ h₂
  have d₃ := r_two_degree y i hv.2.1 hv.2.2.2.1 q₃ h₃
  change q₁.degree+q₂.degree+q₃.degree≤0
  omega

theorem middle_four_forced (a b c d : Nat) (hb : b<3) (hc : c<3) (hd : d<3)
    (p : Path) (hp : p∈downPaths middleSteps [a,b,c,d])
    (hz : p.degree=0) (hout : p.output.take 3=word "ABC") : p=middleRoute := by
  obtain ⟨x,y,z,i,j,k,l,m,n,q₁,q₂,q₃,h₁,ho₁,h₂,ho₂,h₃,ho₃,hv,rfl⟩ :=
    describe a b c d hb hc hd p hp
  have d₁ := r_two_degree b c hb hc q₁ h₁
  have d₂ := l_two_degree z d hv.2.2.1 hd q₂ h₂
  have d₃ := r_two_degree y i hv.2.1 hv.2.2.2.1 q₃ h₃
  change q₁.degree+q₂.degree+q₃.degree=0 at hz
  have hz₁ : q₁.degree=0 := by omega
  have hz₂ : q₂.degree=0 := by omega
  have hz₃ : q₃.degree=0 := by omega
  have ht : a=0 ∧ x=1 ∧ l=2 := by simpa [join,frame,ho₃,word] using hout
  have hq₃ : q₃=rBC := by
    have hh : q₃∈(allPaths 2 rSteps).filter
        (fun p => p.degree==0 && p.output.take 1==word "C") := by
      refine List.mem_filter.mpr ⟨member_small rSteps y i hv.2.1 hv.2.2.2.1 q₃ h₃,?_⟩
      simp [hz₃,ho₃,ht.2.2,word]
    simpa [r_zero_first_C] using hh
  have hyi : y=1 ∧ i=2 := by
    have hh := paths_input rSteps.reverse [y,i] q₃ h₃
    rw [hq₃] at hh
    change [1,2]=[y,i] at hh
    simpa using hh.symm
  have hq₂ : q₂=lBC := by
    have hh : q₂∈(allPaths 2 lSteps).filter
        (fun p => p.degree==0 && p.output.take 1==word "C") := by
      refine List.mem_filter.mpr ⟨member_small lSteps z d hv.2.2.1 hd q₂ h₂,?_⟩
      simp [hz₂,ho₂,hyi.2,word]
    simpa [l_zero_first_C] using hh
  have hzd : z=1 ∧ d=2 := by
    have hh := paths_input lSteps.reverse [z,d] q₂ h₂
    rw [hq₂] at hh
    change [1,2]=[z,d] at hh
    simpa using hh.symm
  have hjk : j=0 ∧ k=2 := by
    rw [hq₂] at ho₂
    change [2,0,2]=[i,j,k] at ho₂
    simp only [List.cons.injEq] at ho₂
    exact ⟨ho₂.2.1.symm,ho₂.2.2.1.symm⟩
  have hq₁ : q₁=rCA := by
    have hh : q₁∈(allPaths 2 rSteps).filter
        (fun p => p.degree==0 && p.output==word "BBB") := by
      refine List.mem_filter.mpr ⟨member_small rSteps b c hb hc q₁ h₁,?_⟩
      simp [hz₁,ho₁,ht.2.1,hyi.1,hzd.1,word]
    simpa [r_zero_BBB] using hh
  rw [hq₁,hq₂,hq₃,ht.1,ht.2.1,hyi.1,hjk.1,hjk.2,hzd.2]
  rfl

theorem four_word_elim (P : Word → Prop)
    (h : ∀ a b c d, a<3 → b<3 → c<3 → d<3 → P [a,b,c,d])
    (u : Word) (hu : validWord 4 u=true) : P u := by
  obtain ⟨hlen,hv⟩ := validWord_iff _ _ |>.mp hu
  rcases u with _ | ⟨a,u⟩
  · simp at hlen
  rcases u with _ | ⟨b,u⟩
  · simp at hlen
  rcases u with _ | ⟨c,u⟩
  · simp at hlen
  rcases u with _ | ⟨d,u⟩
  · simp at hlen
  have he : u=[] := by simpa using hlen
  subst u
  exact h a b c d (hv _ (by simp)) (hv _ (by simp)) (hv _ (by simp)) (hv _ (by simp))

theorem middle_nonpositive_written :
    (allPaths 4 middleSteps).all (fun p => p.degree≤0)=true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp hp
  have hh : ∀ p∈downPaths middleSteps u, p.degree≤0 := by
    apply four_word_elim (fun u => ∀ p∈downPaths middleSteps u, p.degree≤0)
      (fun a b c d _ hb hc hd p hp => middle_four_bound a b c d hb hc hd p hp)
      u ((completeWords_mem 4 u).mp hu)
  exact decide_eq_true (hh p hp)

theorem middle_forced (p : Path) (hp : p∈allPaths 4 middleSteps)
    (hz : p.degree=0) (ho : p.output.take 3=word "ABC") : p=middleRoute := by
  obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp hp
  have hh : ∀ p∈downPaths middleSteps u, p.degree=0 → p.output.take 3=word "ABC" → p=middleRoute := by
    apply four_word_elim (fun u => ∀ p∈downPaths middleSteps u,
      p.degree=0 → p.output.take 3=word "ABC" → p=middleRoute)
      (fun a b c d _ hb hc hd p hp hz ho => middle_four_forced a b c d hb hc hd p hp hz ho)
      u ((completeWords_mem 4 u).mp hu)
  exact hh p hp hz ho

/-- The remaining check is storage uniqueness, not a degree or forced-path claim. -/
theorem middle_histories_nodup : (allPaths 4 middleSteps).Nodup := by native_decide

theorem filter_singleton_of_forced {α : Type} (xs : List α) (f : α → Bool) (a : α)
    (hn : xs.Nodup) (ha : a∈xs) (hfa : f a=true) (hf : ∀ x∈xs, f x=true → x=a) :
    xs.filter f=[a] := by
  have he : ∀ x∈xs, f x=true ↔ x=a := by
    intro x hx
    exact ⟨hf x hx,fun h => h ▸ hfa⟩
  have hh : ∀ x∈xs.filter f, x=a := by
    intro x hx
    obtain ⟨hm,hf⟩ := List.mem_filter.mp hx
    exact (he x hm).mp hf
  have hm : a∈xs.filter f := List.mem_filter.mpr ⟨ha,hfa⟩
  have hnd := hn.filter f
  generalize hg : xs.filter f=ys at hh hm hnd ⊢
  cases ys with
  | nil => simp at hm
  | cons b ys =>
    have hb := hh b (by simp)
    subst b
    have hy : ys=[] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro x hx
      have heq := hh x (by simp [hx])
      exact (List.nodup_cons.mp hnd).1 (heq ▸ hx))
    simp [hy]

theorem middle_unique_zero_ABC_written :
    (allPaths 4 middleSteps).filter (fun p => p.degree==0 && p.output.take 3==word "ABC")=
      [middleRoute] := by
  apply filter_singleton_of_forced _ _ _ middle_histories_nodup
  · exact List.mem_flatMap.mpr ⟨word "ACAC",(completeWords_mem 4 _).mpr (by decide),by decide⟩
  · decide
  · intro p hp hf
    simp only [Bool.and_eq_true,beq_iff_eq] at hf
    exact middle_forced p hp hf.1 hf.2

def rAA : Path := route "AA" [("ABA",0),("AAB",0)]
def rAANeg : Path := route "AA" [("BAA",-1),("BAA",0)]
def lBB : Path := route "BB" [("BAC",0),("ABC",0)]

theorem r_AA_paths : downPaths rSteps (word "AA")=[rAA,rAANeg] := by decide
theorem r_AA_zero : (downPaths rSteps (word "AA")).filter (fun p => p.degree==0)=[rAA] := by decide
theorem l_BB_zero : (downPaths lSteps (word "BB")).filter (fun p => p.degree==0)=[lBB] := by decide

theorem r_A_not_C : (allPaths 2 rSteps).all (fun p =>
    p.input.take 1 != word "A" || p.output.take 1 != word "C")=true := by decide

theorem aaa_middle_forced (p : Path) (hp : p∈downPaths middleSteps (word "AAAB"))
    (hz : p.degree=0) : p=aaaMiddleRoute := by
  obtain ⟨x,y,z,i,j,k,l,m,n,q₁,q₂,q₃,h₁,ho₁,h₂,ho₂,h₃,ho₃,hv,rfl⟩ :=
    describe 0 0 0 1 (by decide) (by decide) (by decide) p hp
  have d₁ := r_two_degree 0 0 (by decide) (by decide) q₁ h₁
  have d₂ := l_two_degree z 1 hv.2.2.1 (by decide) q₂ h₂
  have d₃ := r_two_degree y i hv.2.1 hv.2.2.2.1 q₃ h₃
  change q₁.degree+q₂.degree+q₃.degree=0 at hz
  have hz₁ : q₁.degree=0 := by omega
  have hz₂ : q₂.degree=0 := by omega
  have hz₃ : q₃.degree=0 := by omega
  have hq₁ : q₁=rAA := by
    have hh : q₁∈(downPaths rSteps (word "AA")).filter (fun p => p.degree==0) :=
      List.mem_filter.mpr ⟨h₁,by simp [hz₁]⟩
    simpa [r_AA_zero] using hh
  have hxyz : x=0 ∧ y=0 ∧ z=1 := by
    rw [hq₁] at ho₁
    change [0,0,1]=[x,y,z] at ho₁
    simpa using ho₁.symm
  have hq₂ : q₂=lBB := by
    have hh : q₂∈(downPaths lSteps (word "BB")).filter (fun p => p.degree==0) :=
      List.mem_filter.mpr ⟨by simpa [hxyz.2.2,word] using h₂,by simp [hz₂]⟩
    simpa [l_BB_zero] using hh
  have hijk : i=0 ∧ j=1 ∧ k=2 := by
    rw [hq₂] at ho₂
    change [0,1,2]=[i,j,k] at ho₂
    simpa using ho₂.symm
  have hq₃ : q₃=rAA := by
    have hh : q₃∈(downPaths rSteps (word "AA")).filter (fun p => p.degree==0) :=
      List.mem_filter.mpr ⟨by simpa [hxyz.2.1,hijk.1,word] using h₃,by simp [hz₃]⟩
    simpa [r_AA_zero] using hh
  rw [hq₁,hq₂,hq₃,hxyz.1,hxyz.2.1,hijk.2.1,hijk.2.2]
  rfl

theorem aaa_middle_constant_written :
    (downPaths middleSteps (word "AAAB")).filter (fun p => p.degree==0)=[aaaMiddleRoute] := by
  apply filter_singleton_of_forced _ _ _
  · exact (show (downPaths middleSteps (word "AAAB")).Nodup from by decide)
  · decide
  · decide
  · intro p hp hf
    exact aaa_middle_forced p hp (by simpa using hf)

theorem aaa_middle_no_ABC (p : Path) (hp : p∈downPaths middleSteps (word "AAAB")) :
    p.output.take 3 ≠ word "ABC" := by
  obtain ⟨x,y,z,i,j,k,l,m,n,q₁,q₂,q₃,h₁,ho₁,h₂,ho₂,h₃,ho₃,hv,rfl⟩ :=
    describe 0 0 0 1 (by decide) (by decide) (by decide) p hp
  intro he
  have hx : x=1 ∧ l=2 := by simpa [join,frame,ho₃,word] using he
  have hq₁ : q₁=rAANeg := by
    have hh : q₁=rAA ∨ q₁=rAANeg := by
      change q₁∈downPaths rSteps (word "AA") at h₁
      rw [r_AA_paths] at h₁
      simpa using h₁
    rcases hh with hh | hh
    · rw [hh] at ho₁
      have hhx : x=0 := by have := congrArg (fun w => w.take 1) ho₁; simpa [rAA,route,word,initial,extend] using this.symm
      omega
    · exact hh
  have hy : y=0 := by
    rw [hq₁] at ho₁
    change [1,0,0]=[x,y,z] at ho₁
    simp only [List.cons.injEq] at ho₁
    exact ho₁.2.1.symm
  have hh := List.all_eq_true.mp r_A_not_C q₃ (member_small rSteps y i hv.2.1 hv.2.2.2.1 q₃ h₃)
  have hin := paths_input rSteps.reverse [y,i] q₃ h₃
  simp [hin,hy,ho₃,hx.2,word] at hh

theorem baaa_middle_no_ABC (p : Path) (hp : p∈downPaths middleSteps (word "BAAA")) :
    p.output.take 3 ≠ word "ABC" := by
  obtain ⟨x,y,z,i,j,k,l,m,n,q₁,q₂,q₃,h₁,ho₁,h₂,ho₂,h₃,ho₃,hv,rfl⟩ :=
    describe 1 0 0 0 (by decide) (by decide) (by decide) p hp
  simp [join,frame,ho₃,word]

theorem aaa_no_second_positive_written :
    ((downPaths middleSteps (word "AAAB")) ++ (downPaths middleSteps (word "BAAA"))).all
      (fun p => p.output.take 3 != word "ABC")=true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain hp | hp := List.mem_append.mp hp
  · simpa using aaa_middle_no_ABC p hp
  · simpa using baaa_middle_no_ABC p hp

#print axioms middle_nonpositive_written
#print axioms middle_unique_zero_ABC_written
end WebMu.Revised.LocalPaths.Middle
