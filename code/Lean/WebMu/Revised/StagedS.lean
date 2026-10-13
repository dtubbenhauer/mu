import WebMu.Revised.StagedMiddle

/-! The positive S path is forced by the primitive H and y branches stated in
the manuscript, after the R nonpositivity argument. -/
namespace WebMu.Revised.LocalPaths.SDerivation
open Laurent Algebra Bar Elementary Middle
local instance : BEq Path := instBEqOfDecidableEq
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem h_right_A (a b : Nat) (ha : a<3) (hb : b<3) (e : Edge)
    (he : e∈branches (.h,0) [a,b]) (hout : e.output[1]?=some 0) :
    (a=0 ∧ b=0 ∧ e=⟨[0,0],0,1⟩) ∨
    (a=0 ∧ b=1 ∧ e=⟨[1,0],0,1⟩) ∨
    (a=1 ∧ b=1 ∧ e=⟨[2,0],0,1⟩) ∨
    (a=2 ∧ b=0 ∧ e=⟨[2,0],-1,1⟩) := by
  have hh : a=0 ∨ a=1 ∨ a=2 := by omega
  have hk : b=0 ∨ b=1 ∨ b=2 := by omega
  rcases hh with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
    simp [branches,GrowthBridge.transitions,arity,localTerms,one,monomial] at he <;>
    (first | subst e | rcases he with rfl | rfl) <;> simp_all

theorem y_zero_right_B (a : Nat) (ha : a<3) (e : Edge)
    (he : e∈branches (.y,0) [a]) (hd : e.degree=0) (hout : e.output[1]?=some 1) :
    a=0 ∧ e=⟨[0,1],0,1⟩ := by
  have hh : a=0 ∨ a=1 ∨ a=2 := by omega
  rcases hh with rfl | rfl | rfl <;>
    simp [branches,GrowthBridge.transitions,arity,localTerms,one,monomial] at he <;>
    rcases he with rfl | rfl <;> simp_all

theorem h_positive_exact (a b : Nat) (ha : a<3) (hb : b<3) (e : Edge)
    (he : e∈branches (.h,0) [a,b]) (hd : 0<e.degree) :
    a=0 ∧ b=2 ∧ e=⟨[0,2],1,1⟩ := by
  have hh : a=0 ∨ a=1 ∨ a=2 := by omega
  have hk : b=0 ∨ b=1 ∨ b=2 := by omega
  rcases hh with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
    simp [branches,GrowthBridge.transitions,arity,localTerms,one,monomial] at he <;>
    (first | subst e | rcases he with rfl | rfl) <;> simp_all

def rAB : Path := route "AB" [("ABB",0),("ACA",0)]

/-- In degree zero, the four H branches ending in A reduce to BB to CA:
the first two force the negative y branch and the fourth is itself negative. -/
theorem r_zero_right_A (a b : Nat) (ha : a<3) (hb : b<3) (p : Path)
    (hp : p∈downPaths rSteps [a,b]) (hd : p.degree=0)
    (hout : p.output[2]?=some 0) : p=rAB := by
  rw [downPaths, ← walk_initial] at hp
  change p∈walk [(.y,0),(.h,1)] (initial [a,b]) at hp
  simp only [walk,List.mem_flatMap,List.mem_singleton] at hp
  obtain ⟨e₁,he₁,e₂,he₂,rfl⟩ := hp
  dsimp only [initial,extend] at he₁ he₂ hd hout ⊢
  have hc₁ := branches_context .y [] [a] [b] rfl
  change e₁∈branches (.y,0) ([]++[a]++[b]) at he₁
  simp only [List.length_nil] at hc₁
  rw [hc₁] at he₁
  obtain ⟨f₁,hf₁,rfl⟩ := List.mem_map.mp he₁
  obtain ⟨x,y,ho₁,hx,hy,hy0,hyA,hyC,hyB⟩ := y_facts a ha f₁ hf₁
  have hc₂ := branches_context .h [x] [y,b] [] rfl
  simp only [List.length_cons,List.length_nil] at hc₂
  simp only [surround,ho₁,List.nil_append,List.cons_append] at he₂
  change e₂∈branches (.h,1) ([x]++[y,b]++[]) at he₂
  rw [hc₂] at he₂
  obtain ⟨f₂,hf₂,rfl⟩ := List.mem_map.mp he₂
  have ho₂ : f₂.output[1]?=some 0 := by simpa [surround] using hout
  have hd' : f₁.degree+f₂.degree=0 := by simpa [surround] using hd
  have hf := h_right_A y b hy hb f₂ hf₂ ho₂
  rcases hf with hf | hf | hf | hf
  · have hdY := hyA hf.1
    rw [hf.2.2] at hd'
    simp only at hd'
    omega
  · have hdY := hyA hf.1
    rw [hf.2.2] at hd'
    simp only at hd'
    omega
  · have hdY : f₁.degree=0 := by rw [hf.2.2] at hd'; simpa using hd'
    have hoY : f₁.output[1]?=some 1 := by simp [ho₁,hf.1]
    obtain ⟨ha₀,hf₁'⟩ := y_zero_right_B a ha f₁ hf₁ hdY hoY
    have hx₀ : x=0 := by
      rw [hf₁'] at ho₁
      have hh := (congrArg (fun w => w[0]?) ho₁).symm
      change some x=some 0 at hh
      exact Option.some.inj hh
    rw [hf₁',hf.2.2,ha₀,hf.2.1,hx₀]
    rfl
  · rw [hf.2.2] at hd'
    simp only at hd'
    omega

def positiveRoute : Path := route "ABC" [("ABBC",0),("ACAC",0),("ACAC",1)]

theorem s_three_positive (a b c : Nat) (ha : a<3) (hb : b<3) (hc : c<3)
    (p : Path) (hp : p∈downPaths sSteps [a,b,c]) (hpos : 0<p.degree) : p=positiveRoute := by
  have he : sSteps=[(.h,2)]++rSteps := rfl
  rw [he] at hp
  obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hp
  have hctx := downPaths_context rSteps [] [a,b] [c] (fits_r a b ha hb)
  change downPaths rSteps [a,b,c]=(downPaths rSteps [a,b]).map (frame [] [c]) at hctx
  rw [hctx] at hq
  obtain ⟨q,hqLocal,rfl⟩ := List.mem_map.mp hq
  obtain ⟨x,y,z,ho,hx,hy,hz⟩ := small_support rSteps (Or.inl rfl) a b ha hb q hqLocal
  have dq := r_two_degree a b ha hb q hqLocal
  rw [downPaths, ← walk_initial] at hr
  change r∈walk [(.h,2)] (initial (frame [] [c] q).output) at hr
  simp only [walk,List.mem_flatMap,List.mem_singleton] at hr
  obtain ⟨e,he,rfl⟩ := hr
  dsimp only [initial,extend,frame,join] at he hpos ⊢
  simp only [ho,List.nil_append,List.cons_append,List.nil_append] at he
  have hctxH := branches_context .h [x,y] [z,c] [] rfl
  simp only [List.length_cons,List.length_nil] at hctxH
  change e∈branches (.h,2) ([x,y]++[z,c]++[]) at he
  rw [hctxH] at he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  have hfp : 0<f.degree := by dsimp only [surround] at hpos; omega
  obtain ⟨hz₀,hc₂,hfexact⟩ := h_positive_exact z c hz hc f hf hfp
  have hqzero : q.degree=0 := by rw [hfexact] at hpos; dsimp only [surround] at hpos; omega
  have hqA : q.output[2]?=some 0 := by simp [ho,hz₀]
  have hqexact := r_zero_right_A a b ha hb q hqLocal hqzero hqA
  have hxy : x=0 ∧ y=2 := by
    rw [hqexact] at ho
    change [0,2,0]=[x,y,z] at ho
    simp only [List.cons.injEq] at ho
    exact ⟨ho.1.symm,ho.2.1.symm⟩
  rw [hqexact,hfexact,hc₂,hxy.1,hxy.2]
  rfl

theorem three_word_elim (P : Word → Prop)
    (h : ∀ a b c, a<3 → b<3 → c<3 → P [a,b,c])
    (u : Word) (hu : validWord 3 u=true) : P u := by
  obtain ⟨hlen,hv⟩ := validWord_iff _ _ |>.mp hu
  rcases u with _ | ⟨a,u⟩
  · simp at hlen
  rcases u with _ | ⟨b,u⟩
  · simp at hlen
  rcases u with _ | ⟨c,u⟩
  · simp at hlen
  have he : u=[] := by simpa using hlen
  subst u
  exact h a b c (hv _ (by simp)) (hv _ (by simp)) (hv _ (by simp))

theorem s_positive_forced (p : Path) (hp : p∈allPaths 3 sSteps) (hd : 0<p.degree) :
    p=positiveRoute := by
  obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp hp
  have hh : ∀ p∈downPaths sSteps u, 0<p.degree → p=positiveRoute := by
    apply three_word_elim (fun u => ∀ p∈downPaths sSteps u, 0<p.degree → p=positiveRoute)
      (fun a b c ha hb hc p hp hd => s_three_positive a b c ha hb hc p hp hd)
      u ((completeWords_mem 3 u).mp hu)
  exact hh p hp hd

theorem s_unique_positive_written :
    (allPaths 3 sSteps).filter (fun p => 0<p.degree)=[positiveRoute] := by
  apply filter_singleton_of_forced
  · decide
  · decide
  · decide
  · intro p hp hf
    exact s_positive_forced p hp (by simpa using hf)

theorem fits_s (u : Word) (hu : validWord 3 u=true) : fits sSteps.reverse u=true := by
  apply three_word_elim (fun u => fits sSteps.reverse u=true) ?_ u hu
  intro a b c ha hb hc
  exact (show ∀ a b c : Fin 3, fits sSteps.reverse [a,b,c]=true from by decide)
    ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩

theorem s_bound (u : Word) (hu : validWord 3 u=true) (p : Path)
    (hp : p∈downPaths sSteps u) : p.degree≤1 ∧ (0<p.degree → u=word "ABC") := by
  by_cases hd : 0<p.degree
  · have hm : p∈allPaths 3 sSteps := List.mem_flatMap.mpr ⟨u,(completeWords_mem 3 u).mpr hu,hp⟩
    have he := s_positive_forced p hm hd
    have hi := paths_input sSteps.reverse u p hp
    rw [he] at hi ⊢
    exact ⟨by decide,fun _ => hi.symm⟩
  · constructor
    · omega
    · intro h; exact False.elim (hd h)

theorem s_suffix (u post : Word) (hu : validWord 3 u=true) :
    downPaths sSteps (u++post)=(downPaths sSteps u).map (frame [] post) := by
  exact downPaths_context sSteps [] u post (fits_s u hu)

theorem second_s_table_written : (allPaths 7 sSteps).all (fun p =>
    p.degree ≤ 1 && (p.degree ≤ 0 || p.input.take 3 == word "ABC"))=true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp hp
  have hv := (completeWords_mem 7 u).mp hu
  obtain ⟨hl,ha⟩ := validWord_iff _ _ |>.mp hv
  have ht : validWord 3 (u.take 3)=true := validWord_iff _ _ |>.mpr
    ⟨by simp [List.length_take,hl],by intro a hm; exact ha a (List.mem_of_mem_take hm)⟩
  have he := s_suffix (u.take 3) (u.drop 3) ht
  rw [List.take_append_drop] at he
  rw [he] at hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hb := s_bound (u.take 3) ht q hq
  have hi := paths_input sSteps.reverse (u.take 3) q hq
  have hprefix : (frame [] (u.drop 3) q).input.take 3=u.take 3 := by
    simp [frame,hi,List.take_append,List.take_take,List.length_take,hl]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq]
  refine ⟨hb.1,?_⟩
  by_cases hd : q.degree≤0
  · exact Or.inl hd
  · right
    rw [hprefix]
    exact hb.2 (by omega)

theorem s_ABC_positive :
    (downPaths sSteps (word "ABC")).filter (fun p => 0<p.degree)=[positiveRoute] := by
  apply filter_singleton_of_forced
  · decide
  · decide
  · decide
  · intro p hp hf
    exact s_three_positive 0 1 2 (by decide) (by decide) (by decide) p hp (by simpa using hf)

/-- The positive S path with four spectators follows by the generic context
lemma, with no seven-letter enumeration. -/
theorem second_s_positive_written :
    (downPaths sSteps (word "ABCACAC")).filter (fun p => 0<p.degree)=
      [route "ABCACAC" [("ABBCACAC",0),("ACACACAC",0),("ACACACAC",1)]] := by
  have hc := s_suffix (word "ABC") (word "ACAC") (by decide)
  change downPaths sSteps (word "ABCACAC")=_ at hc
  rw [hc,List.filter_map]
  change ((downPaths sSteps (word "ABC")).filter (fun p => 0<p.degree)).map
    (frame [] (word "ACAC"))=_
  rw [s_ABC_positive]
  rfl

/-- This is the complete three-row path table actually displayed in the
manuscript, with its intermediate words and exponents, checked in the kernel. -/
theorem s_complete_ACAC_written :
    (allPaths 3 sSteps).filter (fun p => p.output == word "ACAC") =
      [route "ABC" [("ABBC",0),("ACAC",0),("ACAC",1)],
       route "ACB" [("ABCB",0),("ACBB",0),("ACAC",0)],
       route "BAC" [("ACAC",0),("ACAC",-1),("ACAC",1)]] := by decide

theorem s_AAA_complete_paths_written : downPaths sSteps (word "AAA") =
    [route "AAA" [("ABAA",0),("AABA",0),("AAAB",0)],
     route "AAA" [("BAAA",-1),("BAAA",0),("BAAA",0)]] := by decide

#print axioms s_unique_positive_written
#print axioms second_s_table_written
end WebMu.Revised.LocalPaths.SDerivation
