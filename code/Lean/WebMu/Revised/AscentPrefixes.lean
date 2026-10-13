import WebMu.Revised.NonpositivePrograms
import WebMu.Revised.StagedPathDerivations

/-! The precise y/cup/R factorizations of the D and H prefixes printed in the
ascent proof. Bounds are composed from elementary nonpositivity, not from a
whole-prefix degree enumeration. -/
namespace WebMu.Revised.LocalPaths.AscentPrefixes
open Laurent Algebra Bar NonpositivePrograms
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- D_1 is treated separately; the other seven-prefix table entries are literal. -/
def dPrograms : List (List Piece) := [
  [],
  [(.y,0),(.y,3),(.y,4),(.y,3),(.y,2),(.r,0)],
  [(.y,0),(.y,2),(.cup,2),(.y,2),(.r,0),(.y,1)],
  [(.y,0),(.y,1),(.y,2),(.y,1),(.y,2),(.r,0),(.y,1)],
  [(.y,0),(.y,1),(.y,0),(.y,1),(.y,2),(.y,1),(.y,1)],
  [(.y,0),(.cup,0),(.y,1),(.y,2),(.y,1),(.y,1)],
  [(.y,0),(.cup,0),(.y,0),(.cup,0),(.y,0)]]

def hPrograms : List (List Piece) := [
  [(.y,1),(.y,3),(.y,4),(.cup,4),(.r,1)],
  [(.y,1),(.y,3),(.y,4),(.y,3),(.y,2),(.y,1)],
  [(.y,1),(.y,2),(.cup,2),(.y,2),(.y,1),(.y,1)],
  [(.y,1),(.y,3),(.y,4),(.r,0),(.y,1),(.r,0),(.y,1)],
  [(.y,1),(.cup,1),(.y,1),(.y,2),(.y,1),(.y,1)],
  [],
  [(.y,0),(.y,2),(.cup,2),(.y,2),(.cup,2)],
  [(.y,0),(.y,2),(.cup,2),(.y,2),(.r,0)],
  [(.y,0),(.y,1),(.y,2),(.y,1),(.y,2),(.cup,2)],
  [(.y,0),(.y,1),(.y,2),(.y,1),(.y,2),(.r,0),(.y,1)],
  [(.y,0),(.y,1),(.y,2),(.y,1),(.y,1),(.cup,1)]]

/-- These checks concern only literal generator lists and their arities. -/
theorem d_factorizations : ∀ j : Fin 7, j.val≠0 →
    program dPrograms[j.val]! = correctionSteps[j.val]!.1 ∧
    outputLength dPrograms[j.val]! dInputLengths[j.val]! = some 9 := by decide

theorem h_factorizations : ∀ j : Fin 11, j.val≠5 →
    program hPrograms[j.val]! = hSteps[j.val]!.1 ∧
    outputLength hPrograms[j.val]! hInputLengths[j.val]! = some 9 := by decide

theorem ordinary_d_degree (j : Fin 7) (hj : j.val≠0)
    (u : Word) (hu : validWord dInputLengths[j.val]! u=true)
    (p : Path) (hp : p∈downPaths correctionSteps[j.val]!.1 u) : p.degree≤0 := by
  have h := d_factorizations j hj
  rw [← h.1] at hp
  exact (program_facts _ _ _ h.2 u hu p hp).1

theorem ordinary_h_degree (j : Fin 11) (hj : j.val≠5)
    (u : Word) (hu : validWord hInputLengths[j.val]! u=true)
    (p : Path) (hp : p∈downPaths hSteps[j.val]!.1 u) : p.degree≤0 := by
  have h := h_factorizations j hj
  rw [← h.1] at hp
  exact (program_facts _ _ _ h.2 u hu p hp).1

def dExceptional : List Piece := [(.y,0),(.y,3),(.y,4),(.cup,4)]
def hExceptional : List Piece := [(.y,0),(.y,3),(.y,4),(.y,3),(.y,3)]

theorem exceptional_degree (ps : List Piece) (ht : outputLength ps 4=some 9)
    (u : Word) (hu : validWord 3 u=true) (p : Path)
    (hp : p∈downPaths (program ps++sSteps) u) :
    p.degree≤if u=word "ABC" then 1 else 0 := by
  obtain ⟨q,hq,r,hr,rfl⟩ := (mem_downPaths_append _ _ u p).mp hp
  have hs := Staged.first_s_bound u hu q hq
  have hv := List.all_eq_true.mp Staged.first_s_support q
    (Staged.member_allPaths 3 sSteps u hu q hq)
  have hrest := (program_facts ps 4 9 ht q.output hv r hr).1
  change q.degree+r.degree≤_
  omega

theorem exceptional_d_degree (u : Word) (hu : validWord 3 u=true)
    (p : Path) (hp : p∈downPaths correctionSteps[0]!.1 u) :
    p.degree≤if u=word "ABC" then 1 else 0 :=
  exceptional_degree dExceptional (by decide) u hu p hp

theorem exceptional_h_degree (u : Word) (hu : validWord 3 u=true)
    (p : Path) (hp : p∈downPaths hSteps[5]!.1 u) :
    p.degree≤if u=word "ABC" then 1 else 0 :=
  exceptional_degree hExceptional (by decide) u hu p hp

#print axioms ordinary_d_degree
#print axioms ordinary_h_degree
#print axioms exceptional_d_degree
#print axioms exceptional_h_degree
end WebMu.Revised.LocalPaths.AscentPrefixes
