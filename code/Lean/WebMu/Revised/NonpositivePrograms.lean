import WebMu.Revised.PathContext

/-! Nonpositive strings are assembled from the printed y, cup, R and L pieces.
Only the local tables supply input/output typing. Every composite degree bound
is obtained by framing and concatenating those pieces. -/
namespace WebMu.Revised.LocalPaths.NonpositivePrograms
open Laurent Algebra Bar Elementary
set_option maxHeartbeats 0
set_option maxRecDepth 100000

inductive Kind where
  | y | cup | r | l
  deriving DecidableEq, BEq, Repr

def Kind.input : Kind → Nat | .y => 1 | .cup => 0 | .r | .l => 2
def Kind.output : Kind → Nat | .y => 2 | .cup => 2 | .r | .l => 3
def Kind.steps : Kind → List Step
  | .y => [(.y,0)] | .cup => [(.cup,0)] | .r => rSteps | .l => lSteps

def Piece := Kind × Nat
instance : Inhabited Piece := ⟨(.y,0)⟩
def Piece.steps (p : Piece) : List Step := p.1.steps.map (shiftStep p.2)

def program : List Piece → List Step
  | [] => []
  | p::ps => p.steps++program ps

def outputLength : List Piece → Nat → Option Nat
  | [], n => some n
  | p::ps, n => do
    let k ← outputLength ps n
    if p.2+p.1.input≤k then some (k-p.1.input+p.1.output) else none

theorem core_typing (k : Kind) :
    (completeWords k.input).all (fun u => fits k.steps.reverse u &&
      (downPaths k.steps u).all (fun p => validWord k.output p.output))=true := by
  cases k <;> decide

theorem core_nonpositive (k : Kind) :
    (allPaths k.input k.steps).all (fun p => p.degree≤0)=true := by
  cases k with
  | y => exact elementary_nonpositive_written.1
  | cup => decide
  | r => exact elementary_nonpositive_written.2.2.1
  | l => exact elementary_nonpositive_written.2.2.2

theorem core_facts (k : Kind) (u : Word) (hu : validWord k.input u=true) :
    fits k.steps.reverse u=true ∧
    ∀ p∈downPaths k.steps u, p.degree≤0 ∧ validWord k.output p.output=true := by
  have hm := (completeWords_mem k.input u).mpr hu
  have ht := List.all_eq_true.mp (core_typing k) u hm
  simp only [Bool.and_eq_true] at ht
  refine ⟨ht.1,?_⟩
  intro p hp
  have hd := List.all_eq_true.mp (core_nonpositive k) p
    (List.mem_flatMap.mpr ⟨u,hm,hp⟩)
  exact ⟨of_decide_eq_true hd,List.all_eq_true.mp ht.2 p hp⟩

theorem piece_facts (p : Piece) (n : Nat) (u : Word) (hu : validWord n u=true)
    (hi : p.2+p.1.input≤n) (q : Path) (hq : q∈downPaths p.steps u) :
    q.degree≤0 ∧ validWord (n-p.1.input+p.1.output) q.output=true := by
  obtain ⟨hlen,htern⟩ := validWord_iff n u |>.mp hu
  let pre := u.take p.2
  let mid := (u.drop p.2).take p.1.input
  let post := u.drop (p.2+p.1.input)
  have hpre : pre.length=p.2 := by simp [pre,hlen]; omega
  have hmid : validWord p.1.input mid=true := by
    apply (validWord_iff _ _).mpr
    constructor
    · simp [mid,hlen]; omega
    · intro x hx
      exact htern x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hsplit : pre++mid++post=u := by
    have hh := List.take_append_drop p.1.input (u.drop p.2)
    simp only [List.drop_drop] at hh
    change u.take p.2++(u.drop p.2).take p.1.input++u.drop (p.2+p.1.input)=u
    rw [List.append_assoc,hh,List.take_append_drop]
  have hc := core_facts p.1 mid hmid
  have hcontext := downPaths_context p.1.steps pre mid post hc.1
  rw [hpre,hsplit] at hcontext
  change q∈downPaths (p.1.steps.map (shiftStep p.2)) u at hq
  rw [hcontext] at hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  have hf := hc.2 r hr
  refine ⟨hf.1,?_⟩
  apply (validWord_iff _ _).mpr
  obtain ⟨hl,ht⟩ := validWord_iff _ _ |>.mp hf.2
  constructor
  · simp [frame,pre,post,hlen,hl]; omega
  · intro x hx
    change x∈pre++r.output++post at hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact htern x (List.mem_of_mem_take hx)
    · exact ht x hx
    · exact htern x (List.mem_of_mem_drop hx)

/-- General composition theorem, with the actual intermediate word and length
at every interface. This is not a finite enumeration of a whole prefix. -/
theorem program_facts (ps : List Piece) (n out : Nat) (ht : outputLength ps n=some out)
    (u : Word) (hu : validWord n u=true) (p : Path)
    (hp : p∈downPaths (program ps) u) : p.degree≤0 ∧ validWord out p.output=true := by
  induction ps generalizing n out u p with
  | nil =>
    have he : n=out := by simpa [outputLength] using ht
    have hp' : p=initial u := by simpa [program,downPaths,paths] using hp
    subst p
    exact ⟨Int.le_refl 0,he ▸ hu⟩
  | cons q qs ih =>
    simp only [outputLength] at ht
    cases hs : outputLength qs n with
    | none => simp [hs] at ht
    | some k =>
      simp only [hs,Bind.bind,Option.bind] at ht
      split at ht
      next hbound =>
        have he : k-q.1.input+q.1.output=out := Option.some.inj ht
        obtain ⟨r,hr,s,hs',rfl⟩ := (mem_downPaths_append q.steps (program qs) u p).mp hp
        have hrf := ih n k hs u hu r hr
        have hsf := piece_facts q k r.output hrf.2 hbound s hs'
        refine ⟨?_,?_⟩
        · change r.degree+s.degree≤0
          omega
        · exact he ▸ hsf.2
      next hbound => simp at ht

#print axioms program_facts
end WebMu.Revised.LocalPaths.NonpositivePrograms
