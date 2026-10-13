import WebMu.Revised.PathContext

/-! The four successive constant branches in the outer AAA calculation.
Each stage is nonpositive; a negative branch cannot be recovered by later
stages. The separate output-height calculation then removes the height shift. -/
namespace WebMu.Revised.LocalPaths.AAAOuter
open Laurent Algebra Bar GrowthBridge TruncatedGrowth Elementary
local instance : BEq Path := instBEqOfDecidableEq
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem branch_bound (s : Step) (u : Word) (e : Edge) (he : e∈branches s u) :
    e.degree≤opBound s.1 := by
  obtain ⟨⟨w,q⟩,hq,he'⟩ := List.mem_flatMap.mp he
  obtain ⟨⟨d,c⟩,hd,rfl⟩ := List.mem_map.mp he'
  exact transitions_bounded s u (w,q) hq (d,c) hd

theorem walk_nonpositive (ss : List Step) (h : ∀ s∈ss, opBound s.1=0)
    (p q : Path) (hq : q∈walk ss p) : q.degree≤p.degree := by
  induction ss generalizing p with
  | nil =>
    have he : q=p := by simpa [walk] using hq
    rw [he]
    exact Int.le_refl _
  | cons s ss ih =>
    obtain ⟨e,he,hq⟩ := List.mem_flatMap.mp hq
    have hb := branch_bound s p.output e he
    rw [h s (by simp)] at hb
    have hh := ih (by intro t ht; exact h t (by simp [ht])) (extend p e) hq
    change q.degree≤p.degree+e.degree at hh
    omega

theorem nonpositive (ss : List Step) (h : ∀ s∈ss, opBound s.1=0)
    (u : Word) (p : Path) (hp : p∈downPaths ss u) : p.degree≤0 := by
  rw [downPaths,← walk_initial] at hp
  exact walk_nonpositive ss.reverse (by intro s hs; exact h s (List.mem_reverse.mp hs))
    (initial u) p hp

/-- Append a later nonpositive stage. Each constant route is checked at its
own input; the composite conclusion is obtained by adding the degrees. -/
theorem compose_zero (a b : List Step) (u : Word) (pa pb : Path)
    (ha : ∀ p∈downPaths b u, p.degree≤0)
    (hb : ∀ v p, p∈downPaths a v → p.degree≤0)
    (za : ∀ p∈downPaths b u, 0≤p.degree → p=pa)
    (zb : ∀ p∈downPaths a pa.output, 0≤p.degree → p=pb)
    (p : Path) (hp : p∈downPaths (a++b) u) (hz : 0≤p.degree) : p=join pa pb := by
  obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append _ _ _ _).mp hp
  have hq0 := ha q hq
  have hr0 := hb q.output r hr
  change 0≤q.degree+r.degree at hz
  have he := za q hq (by omega)
  have hf := zb r (by simpa only [he] using hr) (by omega)
  rw [he,hf]

def rRoute : Path := route "AAABABBC" [("AABABABBC",0),("AAABBABBC",0)]
def y7Route : Path := route "AAABBABBC" [("AAABBABACC",0)]
def y6Route : Path := route "AAABBABACC" [("AAABBAACACC",0)]
def y2Route : Path := route "AAABBAACACC" [("AAABBBAACACC",0)]

theorem r_at_AAA (p : Path) (hp : p∈downPaths [(.h,2),(.y,1)] (word "AAABABBC")) :
    p.degree≤0 ∧ (0≤p.degree → p=rRoute) := by
  have hc := downPaths_context rSteps (word "A") (word "AA") (word "BABBC") (by decide)
  change downPaths [(.h,2),(.y,1)] (word "AAABABBC") =
    (downPaths rSteps (word "AA")).map (frame (word "A") (word "BABBC")) at hc
  rw [hc] at hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hd := r_two_degree 0 0 (by decide) (by decide) q hq
  refine ⟨hd,?_⟩
  intro hz
  have he : q=route "AA" [("ABA",0),("AAB",0)] := by
    have hm : q∈(downPaths rSteps (word "AA")).filter (fun p => 0≤p.degree) :=
      List.mem_filter.mpr ⟨hq,by simpa using hz⟩
    have ht : (downPaths rSteps (word "AA")).filter (fun p => 0≤p.degree)=
      [route "AA" [("ABA",0),("AAB",0)]] := by decide
    simpa only [ht,List.mem_singleton] using hm
  rw [he]
  rfl

theorem y_constants :
    (∀ p∈downPaths [(.y,7)] rRoute.output, 0≤p.degree → p=y7Route) ∧
    (∀ p∈downPaths [(.y,6)] y7Route.output, 0≤p.degree → p=y6Route) ∧
    (∀ p∈downPaths [(.y,2)] y6Route.output, 0≤p.degree → p=y2Route) := by
  constructor
  · decide
  constructor <;> decide

theorem forced (p : Path) (hp : p∈downPaths cSteps (word "AAABABBC"))
    (hz : 0≤p.degree) : p=aaaOuterRoute := by
  have ydeg (i : Nat) (u : Word) (p : Path) (hp : p∈downPaths [(.y,i)] u) : p.degree≤0 :=
    nonpositive _ (by simp [opBound]) u p hp
  have h1 (p : Path) (hp : p∈downPaths [(.y,7),(.h,2),(.y,1)] (word "AAABABBC"))
      (hz : 0≤p.degree) : p=join rRoute y7Route :=
    compose_zero _ _ _ _ _ (fun p hp => (r_at_AAA p hp).1) (ydeg 7)
      (fun p hp => (r_at_AAA p hp).2) y_constants.1 p hp hz
  have h1d (p : Path) (hp : p∈downPaths [(.y,7),(.h,2),(.y,1)] (word "AAABABBC")) :
      p.degree≤0 := by
    obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append [(.y,7)] _ _ _).mp hp
    have := (r_at_AAA q hq).1
    have := ydeg 7 q.output r hr
    change q.degree+r.degree≤0
    omega
  have h2 (p : Path) (hp : p∈downPaths [(.y,6),(.y,7),(.h,2),(.y,1)] (word "AAABABBC"))
      (hz : 0≤p.degree) : p=join (join rRoute y7Route) y6Route :=
    compose_zero _ _ _ _ _ h1d (ydeg 6) h1 y_constants.2.1 p hp hz
  have h2d (p : Path) (hp : p∈downPaths [(.y,6),(.y,7),(.h,2),(.y,1)] (word "AAABABBC")) :
      p.degree≤0 := by
    obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append [(.y,6)] _ _ _).mp hp
    have := h1d q hq
    have := ydeg 6 q.output r hr
    change q.degree+r.degree≤0
    omega
  have he := compose_zero [(.y,2)] _ _ _ _ h2d (ydeg 2) h2 y_constants.2.2 p hp hz
  exact he

theorem shifted_forced (p : Path) (hp : p∈downPaths cSteps (word "AAABABBC"))
    (hz : 0≤p.degree+height (encode (p.output.take 3))) : p=aaaOuterRoute := by
  have hh := List.all_eq_true.mp aaa_outer_heights p hp
  simp only [Bool.or_eq_true,beq_iff_eq] at hh
  have hd : height (encode (p.output.take 3))=0 := by
    rcases hh with ((h | h) | h) | h <;> rw [h] <;> decide
  rw [hd,Int.add_zero] at hz
  exact forced p hp hz

end WebMu.Revised.LocalPaths.AAAOuter
