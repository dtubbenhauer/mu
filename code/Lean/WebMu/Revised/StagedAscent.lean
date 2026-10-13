import WebMu.Revised.AscentPrefixes
import WebMu.Revised.PathComposition
import WebMu.Revised.LocalPathConsequences

/-! The ascent proof by separate prefixes and attached small maps. -/
namespace WebMu.Revised.StagedAscent
open Laurent Algebra Bar LocalPaths LocalDegreeProof
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rise (a b : Nat) : Int := if a<b then 1 else 0
def epsilon (a b : Nat) : Int := if a<b then 1 else -1

def lambda2E1 : List Step := [(.lam,0),(.y,0),(.lam,1)]
def lambda1E2 : List Step := [(.lam,1),(.y,1),(.lam,0)]
def datum (p : Path) : Word × Int × Int := (p.output,p.degree,p.multiplicity)

def lambda2E1Data (a b c : Nat) : List (Word × Int × Int) :=
  if a=b then [] else
    (if b=c then [] else [([a,b+c-1],epsilon a b+rise b c,1)]) ++
    (if a=c then [] else [([b,a+c-1],rise a c,1)])

def lambda1E2Data (a b c : Nat) : List (Word × Int × Int) :=
  if b=c then [] else
    (if a=b then [] else [([a+b-1,c],rise a b+epsilon b c,1)]) ++
    (if a=c then [] else [([a+c-1,b],rise a c,1)])

/-- Exact outputs, multiplicities and the two degrees printed in the proof.
Only the 27 elementary input triples are enumerated. -/
theorem lambda2E1_formula : ∀ a b c : Fin 3,
    ((paths lambda2E1 [a.val,b.val,c.val]).map datum).Perm
      (lambda2E1Data a.val b.val c.val) := by native_decide

theorem lambda1E2_formula : ∀ a b c : Fin 3,
    ((paths lambda1E2 [a.val,b.val,c.val]).map datum).Perm
      (lambda1E2Data a.val b.val c.val) := by native_decide


theorem rise_nonnegative (a b : Nat) : 0≤rise a b := by unfold rise; split <;> omega
theorem epsilon_le_rise (a b : Nat) : epsilon a b≤rise a b := by
  unfold epsilon rise
  split <;> omega

theorem nonadjacent_rise (a b c : Nat) : rise a c≤rise a b+rise b c := by
  unfold rise
  split <;> split <;> split <;> omega

theorem lambda2E1Data_degree (a b c : Nat) (q : Word × Int × Int)
    (hq : q ∈ lambda2E1Data a b c) : q.2.1≤rise a b+rise b c := by
  unfold lambda2E1Data at hq
  split at hq
  · simp at hq
  · simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · split at hq
      · simp at hq
      · simp only [List.mem_singleton] at hq
        subst q
        have := epsilon_le_rise a b
        dsimp
        omega
    · split at hq
      · simp at hq
      · simp only [List.mem_singleton] at hq
        subst q
        exact nonadjacent_rise a b c

theorem lambda1E2Data_degree (a b c : Nat) (q : Word × Int × Int)
    (hq : q ∈ lambda1E2Data a b c) : q.2.1≤rise a b+rise b c := by
  unfold lambda1E2Data at hq
  split at hq
  · simp at hq
  · simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · split at hq
      · simp at hq
      · simp only [List.mem_singleton] at hq
        subst q
        have := epsilon_le_rise b c
        dsimp
        omega
    · split at hq
      · simp at hq
      · simp only [List.mem_singleton] at hq
        subst q
        exact nonadjacent_rise a b c

theorem lambda2E1_degree (a b c : Fin 3) (p : Path)
    (hp : p ∈ paths lambda2E1 [a.val,b.val,c.val]) :
    p.degree≤ascWord [a.val,b.val,c.val] := by
  have hm : datum p ∈ lambda2E1Data a.val b.val c.val :=
    (lambda2E1_formula a b c).mem_iff.mp (List.mem_map.mpr ⟨p,hp,rfl⟩)
  exact lambda2E1Data_degree a.val b.val c.val (datum p) hm

theorem lambda1E2_degree (a b c : Fin 3) (p : Path)
    (hp : p ∈ paths lambda1E2 [a.val,b.val,c.val]) :
    p.degree≤ascWord [a.val,b.val,c.val] := by
  have hm : datum p ∈ lambda1E2Data a.val b.val c.val :=
    (lambda1E2_formula a b c).mem_iff.mp (List.mem_map.mpr ⟨p,hp,rfl⟩)
  exact lambda1E2Data_degree a.val b.val c.val (datum p) hm

def lambda1Data (a b c : Nat) : List (Word × Int × Int) :=
  if a=b then [] else [([a+b-1,c],rise a b,1)]
def lambda2Data (a b c : Nat) : List (Word × Int × Int) :=
  if b=c then [] else [([a,b+c-1],rise b c,1)]

theorem lambda1_formula : ∀ a b c : Fin 3,
    ((paths [(.lam,0)] [a.val,b.val,c.val]).map datum)=
      lambda1Data a.val b.val c.val := by decide

theorem lambda2_formula : ∀ a b c : Fin 3,
    ((paths [(.lam,1)] [a.val,b.val,c.val]).map datum)=
      lambda2Data a.val b.val c.val := by decide

theorem lambda1_degree (a b c : Fin 3) (p : Path)
    (hp : p ∈ paths [(.lam,0)] [a.val,b.val,c.val]) :
    p.degree≤ascWord [a.val,b.val,c.val] := by
  have hm : datum p ∈ lambda1Data a.val b.val c.val := by
    rw [← lambda1_formula a b c]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  unfold lambda1Data at hm
  split at hm
  · simp at hm
  · simp only [List.mem_singleton] at hm
    have hd := congrArg (fun q : Word × Int × Int => q.2.1) hm
    change p.degree=rise a.val b.val at hd
    change p.degree≤rise a.val b.val+rise b.val c.val
    have := rise_nonnegative b.val c.val
    omega

theorem lambda2_degree (a b c : Fin 3) (p : Path)
    (hp : p ∈ paths [(.lam,1)] [a.val,b.val,c.val]) :
    p.degree≤ascWord [a.val,b.val,c.val] := by
  have hm : datum p ∈ lambda2Data a.val b.val c.val := by
    rw [← lambda2_formula a b c]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  unfold lambda2Data at hm
  split at hm
  · simp at hm
  · simp only [List.mem_singleton] at hm
    have hd := congrArg (fun q : Word × Int × Int => q.2.1) hm
    change p.degree=rise b.val c.val at hd
    change p.degree≤rise a.val b.val+rise b.val c.val
    have := rise_nonnegative a.val b.val
    omega

/-- The only five attached maps in the D_0 and H tables. -/
inductive SmallMap where
  | identity | lambda1 | lambda2 | lambda2E1 | lambda1E2
  deriving DecidableEq, BEq, Repr

def SmallMap.steps : SmallMap → List Step
  | .identity => []
  | .lambda1 => [(.lam,0)]
  | .lambda2 => [(.lam,1)]
  | .lambda2E1 => StagedAscent.lambda2E1
  | .lambda1E2 => StagedAscent.lambda1E2

def SmallMap.outputLength : SmallMap → Nat
  | .identity => 3
  | _ => 2

theorem small_degree (m : SmallMap) (j : Fin 27) (p : Path)
    (hp : p ∈ paths m.steps (triple j)) : p.degree≤ascWord (triple j) := by
  let a : Fin 3 := ⟨j.val/9,by have := j.isLt; omega⟩
  let b : Fin 3 := ⟨j.val/3%3,Nat.mod_lt _ (by decide)⟩
  let c : Fin 3 := ⟨j.val%3,Nat.mod_lt _ (by decide)⟩
  change p ∈ paths m.steps [a.val,b.val,c.val] at hp
  change p.degree≤ascWord [a.val,b.val,c.val]
  cases m with
  | identity =>
    have he : p=initial [a.val,b.val,c.val] := by simpa [SmallMap.steps,paths] using hp
    rw [he]
    change 0≤rise a.val b.val+rise b.val c.val
    have := rise_nonnegative a.val b.val
    have := rise_nonnegative b.val c.val
    omega
  | lambda1 => exact lambda1_degree a b c p hp
  | lambda2 => exact lambda2_degree a b c p hp
  | lambda2E1 => exact lambda2E1_degree a b c p hp
  | lambda1E2 => exact lambda1E2_degree a b c p hp

/-- Only typing is checked here; the degree bounds above are derived from
 the displayed two-degree formulas and the adjacent-ascent inequalities. -/
theorem small_output_types : ∀ m : SmallMap, ∀ j : Fin 27,
    (paths m.steps (triple j)).all
      (fun p => validWord m.outputLength p.output)=true := by
  intro m
  cases m <;> native_decide


instance : Inhabited SmallMap := ⟨.identity⟩

def dSmall : Fin 7 → SmallMap := fun j =>
  [.identity,.identity,.lambda2,.lambda2E1,.lambda2,.lambda2E1,.lambda1][j.val]!
def hSmall : Fin 11 → SmallMap := fun j =>
  [.identity,.identity,.lambda2,.lambda2E1,.lambda2,.identity,.lambda1E2,
    .identity,.lambda1,.lambda2,.lambda1][j.val]!

theorem d_small_steps : ∀ j : Fin 7, correctionSteps[j.val]!.2=(dSmall j).steps := by decide
theorem h_small_steps : ∀ j : Fin 11, hSteps[j.val]!.2=(hSmall j).steps := by decide
theorem d_small_length : ∀ j : Fin 7, dInputLengths[j.val]! = (dSmall j).outputLength := by decide
theorem h_small_length : ∀ j : Fin 11, hInputLengths[j.val]! = (hSmall j).outputLength := by decide

theorem ordinary_d_prefix (j : Fin 7) (hj : j.val≠0) (u : Word)
    (hu : validWord (dSmall j).outputLength u=true) (p : Path)
    (hp : p ∈ downPaths correctionSteps[j.val]!.1 u) : p.degree≤0 := by
  apply AscentPrefixes.ordinary_d_degree j hj u _ p hp
  rw [d_small_length]
  exact hu

theorem ordinary_h_prefix (j : Fin 11) (hj : j.val≠5) (u : Word)
    (hu : validWord (hSmall j).outputLength u=true) (p : Path)
    (hp : p ∈ downPaths hSteps[j.val]!.1 u) : p.degree≤0 := by
  apply AscentPrefixes.ordinary_h_degree j hj u _ p hp
  rw [h_small_length]
  exact hu

/-- The exceptional prefixes carry no small map, and their possible positive
path starts at ABC. This is exactly the separate first paragraph of the proof. -/
theorem exceptional_ascent (j : Fin 27) :
    (if triple j==word "ABC" then (1 : Int) else 0)≤ascWord (triple j) := by
  by_cases he : triple j=word "ABC"
  · have ha : ascWord (word "ABC")=2 := by decide
    simp [he,ha]
  · simp only [beq_iff_eq,he,if_false]
    change 0≤rise (j.val/9) (j.val/3%3)+rise (j.val/3%3) (j.val%3)
    have := rise_nonnegative (j.val/9) (j.val/3%3)
    have := rise_nonnegative (j.val/3%3) (j.val%3)
    omega

theorem d_exceptional (j : Fin 27) (p : Path)
    (hp : p ∈ downPaths correctionSteps[0]!.1 (triple j)) :
    p.degree≤ascWord (triple j) := by
  have hv : validWord 3 (triple j)=true :=
    (show ∀ j : Fin 27, validWord 3 (triple j)=true from by decide) j
  have hh := AscentPrefixes.exceptional_d_degree (triple j) hv p hp
  apply Int.le_trans hh
  simpa only [beq_iff_eq] using exceptional_ascent j

theorem h_exceptional (j : Fin 27) (p : Path)
    (hp : p ∈ downPaths hSteps[5]!.1 (triple j)) :
    p.degree≤ascWord (triple j) := by
  have hv : validWord 3 (triple j)=true :=
    (show ∀ j : Fin 27, validWord 3 (triple j)=true from by decide) j
  have hh := AscentPrefixes.exceptional_h_degree (triple j) hv p hp
  apply Int.le_trans hh
  simpa only [beq_iff_eq] using exceptional_ascent j

/-- Composition of the small-map bound and the nonpositive prefix; every
intermediate output is proved to have the required input type. -/
theorem d_summand_paths (k : Fin 7) (j : Fin 27) (p : Path)
    (hp : p ∈ summandPaths correctionSteps[k.val]! (triple j)) :
    p.degree≤ascWord (triple j) := by
  by_cases hk : k.val=0
  · have he : correctionSteps[k.val]!.2=[] := by rw [hk]; rfl
    unfold summandPaths at hp
    rw [he,List.reverse_nil,List.append_nil,hk] at hp
    exact d_exceptional j p hp
  · obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append _ _ (triple j) p).mp hp
    rw [d_small_steps] at hq
    have hq' : q ∈ paths (dSmall k).steps (triple j) := by
      simpa only [downPaths,List.reverse_reverse] using hq
    have hs := small_degree (dSmall k) j q hq'
    have ht := List.all_eq_true.mp (small_output_types (dSmall k) j) q hq'
    have hr' := ordinary_d_prefix k hk q.output ht r hr
    change q.degree+r.degree≤_
    omega

theorem h_summand_paths (k : Fin 11) (j : Fin 27) (p : Path)
    (hp : p ∈ summandPaths hSteps[k.val]! (triple j)) :
    p.degree≤ascWord (triple j) := by
  by_cases hk : k.val=5
  · have he : hSteps[k.val]!.2=[] := by rw [hk]; rfl
    unfold summandPaths at hp
    rw [he,List.reverse_nil,List.append_nil,hk] at hp
    exact h_exceptional j p hp
  · obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append _ _ (triple j) p).mp hp
    rw [h_small_steps] at hq
    have hq' : q ∈ paths (hSmall k).steps (triple j) := by
      simpa only [downPaths,List.reverse_reverse] using hq
    have hs := small_degree (hSmall k) j q hq'
    have ht := List.all_eq_true.mp (small_output_types (hSmall k) j) q hq'
    have hr' := ordinary_h_prefix k hk q.output ht r hr
    change q.degree+r.degree≤_
    omega

theorem d_summand_degree (k : Fin 7) (j : Fin 27) (w : Word) :
    DegreeLE ((summand correctionSteps[k.val]! j).getD w []) (ascWord (triple j)) := by
  rw [summand_as_expand]
  exact paths_degree_bound _ _ _ (d_summand_paths k j) w

theorem h_summand_degree (k : Fin 11) (j : Fin 27) (w : Word) :
    DegreeLE ((summand hSteps[k.val]! j).getD w []) (ascWord (triple j)) := by
  rw [summand_as_expand]
  exact paths_degree_bound _ _ _ (h_summand_paths k j) w

theorem d_piece_enumeration :
    (List.finRange 7).map (fun k => correctionSteps[k.val]!)=correctionSteps.take 7 := by decide

theorem h_piece_enumeration :
    (List.finRange 11).map (fun k => hSteps[k.val]!)=hSteps := by decide

/-- Summation is the last step, after bounding each P_i h_i by composition. -/
theorem d₀_ascent_degree (j : Fin 27) (w : Word) :
    DegreeLE ((rawD₀ j).getD w []) (ascWord (triple j)) := by
  apply sumTensor_degree
  intro x hx out
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
  rw [← d_piece_enumeration] at hs
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hs
  exact d_summand_degree k j out

theorem h_ascent_degree (j : Fin 27) (w : Word) :
    DegreeLE ((rawH j).getD w []) (ascWord (triple j)) := by
  apply sumTensor_degree
  intro x hx out
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
  rw [← h_piece_enumeration] at hs
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hs
  exact h_summand_degree k j out


/-- With only A,B,C available, two strict adjacent ascents force ABC. -/
theorem two_ascents (a b c : Fin 3) (hab : a.val<b.val) (hbc : b.val<c.val) :
    a.val=0 ∧ b.val=1 ∧ c.val=2 := by
  have := a.isLt
  have := b.isLt
  have := c.isLt
  omega

theorem ascent_le_height (j : Fin 27) : ascWord (triple j)≤1+height j := by
  let a : Fin 3 := ⟨j.val/9,by have := j.isLt; omega⟩
  let b : Fin 3 := ⟨j.val/3%3,Nat.mod_lt _ (by decide)⟩
  let c : Fin 3 := ⟨j.val%3,Nat.mod_lt _ (by decide)⟩
  by_cases hab : a.val<b.val
  · by_cases hbc : b.val<c.val
    · have ht := two_ascents a b c hab hbc
      have he : j.val=5 := by
        change j.val/9=0 ∧ j.val/3%3=1 ∧ j.val%3=2 at ht
        have := j.isLt
        omega
      simp [he,triple,ascWord,height]
    · change rise a.val b.val+rise b.val c.val≤1+height j
      simp only [rise,hab,hbc,if_pos,if_false,Int.add_zero]
      unfold height
      split <;> omega
  · change rise a.val b.val+rise b.val c.val≤1+height j
    simp only [rise,hab,if_false,Int.zero_add]
    unfold height
    split <;> split <;> omega

#print axioms lambda2E1_formula
#print axioms lambda1E2_formula
#print axioms d₀_ascent_degree
#print axioms h_ascent_degree
#print axioms ascent_le_height
end WebMu.Revised.StagedAscent
