import WebMu.Revised.PathComposition

/-! Elementary table reasoning for the nonpositive and outer-degree lemmas.
Only the one-letter y table and two-letter H table are finite certificates.
Composite degree bounds below are deductions from those primitive facts. -/
namespace WebMu.Revised.LocalPaths.Elementary
open Laurent Algebra Bar GrowthBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def surround (pre post : Word) (e : Edge) : Edge :=
  ⟨pre ++ e.output ++ post,e.degree,e.multiplicity⟩

theorem branches_context (op : Op) (pre u post : Word) (hu : u.length = arity op) :
    branches (op,pre.length) (pre ++ u ++ post) =
      (branches (op,0) u).map (surround pre post) := by
  simp only [branches,transitions]
  have hb : pre.length + arity op ≤ (pre ++ u ++ post).length := by
    simp only [List.length_append,hu]; omega
  simp only [hb, ↓reduceIte, List.drop_append, List.drop_length, List.nil_append,
    Nat.sub_self, List.drop_zero, List.take_append, List.take_length, List.append_nil,
    Nat.zero_add, hu, Nat.le_refl, List.map_flatMap, List.flatMap_map]
  simp only [← hu,List.take_left,List.drop_left,List.take_append,List.take_length,
    Nat.sub_self,List.take_zero,List.append_nil,List.drop_append,List.drop_length,
    List.nil_append,Nat.add_sub_cancel_left,List.drop_zero]
  have hd : pre.drop (pre.length+u.length) = [] := List.drop_eq_nil_of_le (by omega)
  simp [surround,List.map_map,Function.comp_def,hd]

/-- Primitive y facts: each output has two letters; its degree is nonpositive.
A right A or a left C costs degree -1. In y(A), a left B also costs -1. -/
def YFacts (a : Nat) (e : Edge) : Prop :=
  ∃ p q, e.output = [p,q] ∧ p<3 ∧ q<3 ∧ e.degree ≤ 0 ∧
    (q=0 → e.degree = -1) ∧ (p=2 → e.degree = -1) ∧
    (a=0 → p=1 → e.degree = -1)

theorem y_facts (a : Nat) (ha : a<3) (e : Edge)
    (he : e ∈ branches (.y,0) [a]) : YFacts a e := by
  have hh : a=0 ∨ a=1 ∨ a=2 := by omega
  rcases hh with rfl | rfl | rfl <;>
    simp [branches,transitions,arity,localTerms,one,monomial] at he <;>
    rcases he with rfl | rfl <;>
    (refine ⟨_,_,rfl,?_⟩; decide)

/-- Primitive H facts: the only positive branch is AC to AC, of degree one. -/
def HFacts (a b : Nat) (e : Edge) : Prop :=
  ∃ p q, e.output = [p,q] ∧ p<3 ∧ q<3 ∧ e.degree ≤ 1 ∧
    (0 < e.degree → a=0 ∧ b=2 ∧ p=0 ∧ q=2 ∧ e.degree=1)

theorem h_facts (a b : Nat) (ha : a<3) (hb : b<3) (e : Edge)
    (he : e ∈ branches (.h,0) [a,b]) : HFacts a b e := by
  have hh : a=0 ∨ a=1 ∨ a=2 := by omega
  have hk : b=0 ∨ b=1 ∨ b=2 := by omega
  rcases hh with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
    simp [branches,transitions,arity,localTerms,one,monomial] at he <;>
    (first | subst e | rcases he with rfl | rfl) <;>
    (refine ⟨_,_,rfl,?_⟩; decide)

/-- The R cancellation: a positive H requires the right A of y. -/
theorem r_degree (a b p q r s : Nat) (dy dh : Int)
    (hy : YFacts a ⟨[p,q],dy,1⟩) (hh : HFacts q b ⟨[r,s],dh,1⟩) :
    dy + dh ≤ 0 := by
  obtain ⟨p',q',he,_,_,hy0,hyA,_,_⟩ := hy
  obtain ⟨r',s',hf,_,_,hh1,hhP⟩ := hh
  have hep : p'=p ∧ q'=q := by simpa using he.symm
  have hef : r'=r ∧ s'=s := by simpa using hf.symm
  rcases hep with ⟨hp,hq⟩
  rcases hef with ⟨hr,hs⟩
  subst p'; subst q'; subst r'; subst s'
  try dsimp only at *
  by_cases h : 0 < dh
  · have hp := hhP h
    have := hyA hp.1
    omega
  · omega

/-- The L cancellation: a positive H requires the left C of y. -/
theorem l_degree (a b p q r s : Nat) (dy dh : Int)
    (hy : YFacts b ⟨[p,q],dy,1⟩) (hh : HFacts a p ⟨[r,s],dh,1⟩) :
    dy + dh ≤ 0 := by
  obtain ⟨p',q',he,_,_,hy0,_,hyC,_⟩ := hy
  obtain ⟨r',s',hf,_,_,hh1,hhP⟩ := hh
  have hep : p'=p ∧ q'=q := by simpa using he.symm
  have hef : r'=r ∧ s'=s := by simpa using hf.symm
  rcases hep with ⟨hp,hq⟩
  rcases hef with ⟨hr,hs⟩
  subst p'; subst q'; subst r'; subst s'
  try dsimp only at *
  by_cases h : 0 < dh
  · have hp := hhP h
    have := hyC hp.2.1
    omega
  · omega

/-- The local outer piece, with spectator a. The height-one outputs split
exactly as in the printed proof: ABC/BAC require a left C at the last y;
ACB requires a left C at the first y, and the possible positive H then
requires the negative branch producing a left B in y(A). -/
theorem outer_local_degree (a b c p q r s u v : Nat) (da dh db : Int)
    (ha : a<3)
    (hy : YFacts b ⟨[p,q],da,1⟩)
    (hh : HFacts q c ⟨[r,s],dh,1⟩)
    (hz : YFacts r ⟨[u,v],db,1⟩) :
    da + dh + db + height (encode [a,p,u]) ≤ 0 := by
  have hR := r_degree b c p q r s da dh hy hh
  obtain ⟨p',q',he,hp,hq,ha0,haA,haC,haB⟩ := hy
  obtain ⟨r',s',hf,hr,hs,hh1,hhP⟩ := hh
  obtain ⟨u',v',hg,hu,hv,hb0,hbA,hbC,hbB⟩ := hz
  have hep : p'=p ∧ q'=q := by simpa using he.symm
  have hef : r'=r ∧ s'=s := by simpa using hf.symm
  have heg : u'=u ∧ v'=v := by simpa using hg.symm
  rcases hep with ⟨hp,hq⟩
  rcases hef with ⟨hr,hs⟩
  subst p'; subst q'; subst r'; subst s'
  try dsimp only at *
  rcases heg with ⟨hu,hv⟩
  subst u'; subst v'
  try dsimp only at *
  have height_cases : height (encode [a,p,u]) = 0 ∨
      (height (encode [a,p,u])=1 ∧
       ((a=0 ∧ p=1 ∧ u=2) ∨ (a=1 ∧ p=0 ∧ u=2) ∨ (a=0 ∧ p=2 ∧ u=1))) := by
    have h₁ : a=0 ∨ a=1 ∨ a=2 := by omega
    have h₂ : p=0 ∨ p=1 ∨ p=2 := by omega
    have h₃ : u=0 ∨ u=1 ∨ u=2 := by omega
    rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
      rcases h₃ with rfl | rfl | rfl <;> decide
  rcases height_cases with hz | ⟨hz,hcases⟩
  · rw [hz]; omega
  · rw [hz]
    rcases hcases with hABC | hBAC | hACB
    · have := hbC hABC.2.2; omega
    · have := hbC hBAC.2.2; omega
    · have hda := haC hACB.2.1
      by_cases hpos : 0 < dh
      · have hH := hhP hpos
        have hdb := hbB hH.2.2.1 hACB.2.2
        omega
      · omega

theorem y_context (pre post : Word) (a : Nat) (ha : a<3) (e : Edge)
    (he : e ∈ branches (.y,pre.length) (pre ++ [a] ++ post)) :
    ∃ p q, e.output = pre ++ [p,q] ++ post ∧
      YFacts a ⟨[p,q],e.degree,1⟩ := by
  rw [branches_context _ pre [a] post rfl] at he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  obtain ⟨p,q,hout,hfacts⟩ := y_facts a ha f hf
  refine ⟨p,q,by simp [surround,hout],p,q,rfl,?_⟩
  simpa [surround] using hfacts

theorem h_context (pre post : Word) (a b : Nat) (ha : a<3) (hb : b<3) (e : Edge)
    (he : e ∈ branches (.h,pre.length) (pre ++ [a,b] ++ post)) :
    ∃ p q, e.output = pre ++ [p,q] ++ post ∧
      HFacts a b ⟨[p,q],e.degree,1⟩ := by
  rw [branches_context _ pre [a,b] post rfl] at he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  obtain ⟨p,q,hout,hfacts⟩ := h_facts a b ha hb f hf
  refine ⟨p,q,by simp [surround,hout],p,q,rfl,?_⟩
  simpa [surround] using hfacts

theorem y_output_bounds (a p q : Nat) (d : Int) (h : YFacts a ⟨[p,q],d,1⟩) :
    p<3 ∧ q<3 ∧ d≤0 := by
  obtain ⟨p',q',he,hp,hq,hd,_⟩ := h
  have hh : p'=p ∧ q'=q := by simpa using he.symm
  simpa [hh.1,hh.2] using And.intro hp (And.intro hq hd)

theorem h_output_bounds (a b p q : Nat) (d : Int) (h : HFacts a b ⟨[p,q],d,1⟩) :
    p<3 ∧ q<3 := by
  obtain ⟨p',q',he,hp,hq,_⟩ := h
  have hh : p'=p ∧ q'=q := by simpa using he.symm
  simpa [hh.1,hh.2] using And.intro hp hq

/-- O consists of the local R,y calculation and two nonpositive y maps on
later tensor factors. Their unchanged first three letters are retained here. -/
theorem outer_eight_degree (a b c d e f g h : Nat)
    (ha : a<3) (hb : b<3) (hc : c<3) (hg : g<3) (hf : f<3)
    (p : Path) (hp : p ∈ downPaths cSteps [a,b,c,d,e,f,g,h]) :
    p.degree + height (encode (p.output.take 3)) ≤ 0 := by
  rw [downPaths, ← walk_initial] at hp
  change p ∈ walk [(.y,1),(.h,2),(.y,7),(.y,6),(.y,2)]
    (initial [a,b,c,d,e,f,g,h]) at hp
  simp only [walk,List.mem_flatMap,List.mem_singleton] at hp
  obtain ⟨e₁,he₁,e₂,he₂,e₃,he₃,e₄,he₄,e₅,he₅,rfl⟩ := hp
  dsimp only [initial,extend] at he₁ he₂ he₃ he₄ he₅ ⊢
  obtain ⟨x,y,ho₁,hY⟩ := y_context [a] [c,d,e,f,g,h] b hb e₁ (by simpa using he₁)
  have hxy := y_output_bounds b x y e₁.degree hY
  rw [ho₁] at he₂
  obtain ⟨r,s,ho₂,hH⟩ := h_context [a,x] [d,e,f,g,h] y c hxy.2.1 hc e₂
    (by simpa using he₂)
  have hrs := h_output_bounds y c r s e₂.degree hH
  rw [ho₂] at he₃
  obtain ⟨j,k,ho₃,h₃⟩ := y_context [a,x,r,s,d,e,f] [h] g hg e₃ (by simpa using he₃)
  have hd₃ := (y_output_bounds g j k e₃.degree h₃).2.2
  rw [ho₃] at he₄
  obtain ⟨l,m,ho₄,h₄⟩ := y_context [a,x,r,s,d,e] [j,k,h] f hf e₄ (by simpa using he₄)
  have hd₄ := (y_output_bounds f l m e₄.degree h₄).2.2
  rw [ho₄] at he₅
  obtain ⟨u,v,ho₅,hZ⟩ := y_context [a,x] [s,d,e,l,m,j,k,h] r hrs.1 e₅
    (by simpa using he₅)
  have hh := outer_local_degree a b c x y r s u v e₁.degree e₂.degree e₅.degree ha hY hH hZ
  simp only [ho₅,List.cons_append,List.nil_append,List.take_succ_cons,List.take_zero] at *
  omega

/-- Same pathwise conclusion as the old five-step exhaustive certificate,
now obtained by the printed primitive-table argument. -/
theorem outer_degree_written (u : Word) (hu : validWord 8 u=true)
    (p : Path) (hp : p ∈ downPaths cSteps u) :
    p.degree + height (encode (p.output.take 3)) ≤ 0 := by
  have hlen : u.length=8 := by
    have hh := hu
    simp only [validWord,Bool.and_eq_true,beq_iff_eq] at hh
    exact hh.1
  rcases u with _ | ⟨a,u⟩
  · simp at hlen
  rcases u with _ | ⟨b,u⟩
  · simp at hlen
  rcases u with _ | ⟨c,u⟩
  · simp at hlen
  rcases u with _ | ⟨d,u⟩
  · simp at hlen
  rcases u with _ | ⟨e,u⟩
  · simp at hlen
  rcases u with _ | ⟨f,u⟩
  · simp at hlen
  rcases u with _ | ⟨g,u⟩
  · simp at hlen
  rcases u with _ | ⟨h,u⟩
  · simp at hlen
  have he : u=[] := by simpa using hlen
  subst u
  simp only [validWord,List.length_cons,List.length_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true,decide_eq_true_eq] at hu
  exact outer_eight_degree a b c d e f g h hu.2.1 hu.2.2.1 hu.2.2.2.1
    hu.2.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.1 p hp

theorem outer_path_bound_written :
    (allPaths 8 cSteps).all (fun p => p.degree + height (encode (p.output.take 3)) ≤ 0) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp hp
  exact decide_eq_true (outer_degree_written u ((completeWords_mem 8 u).mp hu) p hp)

theorem r_two_degree (a b : Nat) (ha : a<3) (hb : b<3)
    (p : Path) (hp : p ∈ downPaths rSteps [a,b]) : p.degree ≤ 0 := by
  rw [downPaths, ← walk_initial] at hp
  change p ∈ walk [(.y,0),(.h,1)] (initial [a,b]) at hp
  simp only [walk,List.mem_flatMap,List.mem_singleton] at hp
  obtain ⟨e₁,he₁,e₂,he₂,rfl⟩ := hp
  dsimp only [initial,extend] at he₁ he₂ ⊢
  obtain ⟨x,y,ho₁,hY⟩ := y_context [] [b] a ha e₁ (by simpa using he₁)
  have hxy := y_output_bounds a x y e₁.degree hY
  rw [ho₁] at he₂
  obtain ⟨r,s,ho₂,hH⟩ := h_context [x] [] y b hxy.2.1 hb e₂ (by simpa using he₂)
  simpa using r_degree a b x y r s e₁.degree e₂.degree hY hH

theorem l_two_degree (a b : Nat) (ha : a<3) (hb : b<3)
    (p : Path) (hp : p ∈ downPaths lSteps [a,b]) : p.degree ≤ 0 := by
  rw [downPaths, ← walk_initial] at hp
  change p ∈ walk [(.y,1),(.h,0)] (initial [a,b]) at hp
  simp only [walk,List.mem_flatMap,List.mem_singleton] at hp
  obtain ⟨e₁,he₁,e₂,he₂,rfl⟩ := hp
  dsimp only [initial,extend] at he₁ he₂ ⊢
  obtain ⟨x,y,ho₁,hY⟩ := y_context [a] [] b hb e₁ (by simpa using he₁)
  have hxy := y_output_bounds b x y e₁.degree hY
  rw [ho₁] at he₂
  obtain ⟨r,s,ho₂,hH⟩ := h_context [] [y] a x ha hxy.1 e₂ (by simpa using he₂)
  simpa using l_degree a b x y r s e₁.degree e₂.degree hY hH

theorem two_letter_all (ss : List Step)
    (h : ∀ a b, a<3 → b<3 → ∀ p ∈ downPaths ss [a,b], p.degree≤0) :
    (allPaths 2 ss).all (fun p => p.degree≤0)=true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp hp
  have hv := (completeWords_mem 2 u).mp hu
  have hlen : u.length=2 := by
    have hh := hv
    simp only [validWord,Bool.and_eq_true,beq_iff_eq] at hh
    exact hh.1
  rcases u with _ | ⟨a,u⟩
  · simp at hlen
  rcases u with _ | ⟨b,u⟩
  · simp at hlen
  have he : u=[] := by simpa using hlen
  subst u
  have hv' : a<3 ∧ b<3 := by simpa [validWord] using hv
  exact decide_eq_true (h a b hv'.1 hv'.2 p hp)

/-- The printed nonpositivity argument for R and L, composed from the
primitive y/H cancellation. The one-step y and cup statements reduce directly
to their displayed elementary tables. -/
theorem elementary_nonpositive_written :
    (allPaths 1 [(.y,0)]).all (fun p => p.degree ≤ 0) = true ∧
    (downPaths [(.cup,0)] []).all (fun p => p.degree ≤ 0) = true ∧
    (allPaths 2 rSteps).all (fun p => p.degree ≤ 0) = true ∧
    (allPaths 2 lSteps).all (fun p => p.degree ≤ 0) = true := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · exact two_letter_all rSteps r_two_degree
  · exact two_letter_all lSteps l_two_degree

#print axioms outer_path_bound_written
#print axioms elementary_nonpositive_written
end WebMu.Revised.LocalPaths.Elementary
