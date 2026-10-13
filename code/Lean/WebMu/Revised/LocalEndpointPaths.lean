import WebMu.Revised.LocalPathEnds

/-! Exact monomial histories for the selected prefix, tail, and terminal tree. -/
namespace WebMu.Revised.LocalPaths
open Laurent Algebra Bar LocalDegreeProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rawPrefixExpected (j : Nat) : Laurent :=
  if j=5 then monomial 1 else if j=7 ∨ j=11 then one else []
def rawTailExpected (j : Nat) : Laurent :=
  if j=5 then monomial (-2) else if j=7 ∨ j=11 then monomial (-3) else []

def prefixSelectedPaths (j : Nat) : List Path :=
  if j=5 then [route "ABC" [("ABBC",0),("ACAC",0),("ACAC",1),("ACABC",0),("ABCABC",0)]]
  else if j=7 then [route "ACB" [("ABCB",0),("ACBB",0),("ACAC",0),("ACABC",0),("ABCABC",0)]]
  else if j=11 then [route "BAC" [("ACAC",0),("ACAC",-1),("ACAC",1),("ACABC",0),("ABCABC",0)]]
  else []

def tailSelectedPaths (j : Nat) : List Path :=
  if j=5 then [route "" [("AC",0),("ABC",0),("ACAC",-1),("ACABC",0),("ABCABC",0),("ABBCABC",0),("ABBBCABC",0),("ABCABCABC",-1)]]
  else if j=7 then [route "" [("AC",0),("ABC",0),("ACAC",-1),("ACABC",0),("ACBABC",-1),("ACACABC",0),("ACABCABC",0),("ACBABCABC",-1)]]
  else if j=11 then [route "" [("AC",0),("BAC",-1),("BBAC",-1),("BBABC",0),("BACABC",0),("BABCABC",0),("BABBCABC",0),("BACABCABC",-1)]]
  else []

theorem prefix_selected_paths : ∀ j : Fin 27,
    (downPaths shortPrefixSteps (triple j)).filter (fun p => p.output == wordEnd) = prefixSelectedPaths j := by
  native_decide

theorem tail_selected_paths : ∀ j : Fin 27,
    (downPaths tailSteps []).filter (fun p => p.output == triple j++wordEnd) = tailSelectedPaths j := by
  native_decide

def pathSum (ps : List Path) : Laurent :=
  Laurent.sum (ps.map fun p => monomial p.degree p.multiplicity)

theorem paths_poly_filtered (ss : List Step) (u w : Word) :
    ofList ((expand ss (singleton u)).getD w []) =
      ofList (pathSum ((downPaths ss u).filter (fun p => p.output == w))) := by
  rw [downPaths_poly,pathSum,ofList_total]
  have hf (ps : List Path) :
      total ps (fun p => if p.output == w then pathValue p else 0) =
        total (ps.filter (fun p => p.output == w)) pathValue := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      by_cases h : p.output == w <;>
        simp only [List.filter_cons,total_cons,h,Bool.false_eq_true,↓reduceIte,ih,poly_zero_add]
  exact hf _

/-- Monomial arithmetic on the three displayed histories. -/
theorem end_path_values : ∀ j : Fin 27,
    pathSum (prefixSelectedPaths j)=rawPrefixExpected j ∧
    pathSum (tailSelectedPaths j)=rawTailExpected j := by native_decide

theorem raw_selected_prefix (j : Fin 27) :
    ofList ((shortPrefix j).getD wordEnd [])=ofList (rawPrefixExpected j) := by
  simp only [shortPrefix,if_pos j.isLt]
  rw [paths_poly_filtered,prefix_selected_paths,(end_path_values j).1]

theorem raw_selected_tail (j : Fin 27) :
    ofList (rawQ.getD (triple j++wordEnd) [])=ofList (rawTailExpected j) := by
  rw [rawQ,paths_poly_filtered,tail_selected_paths,(end_path_values j).2]

def treeSelectedPath : Path := route ""
  [("AC",0),("ABC",0),("ACAC",-1),("ACABC",0),("ABCABC",0)]
def twoTripodSelectedPath : Path := route ""
  [("AC",0),("ABC",0),("ACABC",0),("ABCABC",0)]

theorem scalar_selected_paths :
    (downPaths [(.y,1),(.y,2),(.y,1),(.y,0),(.cup,0)] []).filter (fun p => p.output == wordEnd) =
      [treeSelectedPath] ∧
    (downPaths twoTripodString []).filter (fun p => p.output == wordEnd) = [twoTripodSelectedPath] := by
  native_decide

theorem tree_selected_coordinate : ofList (tailTree.getD wordEnd [])=ofList (monomial (-1)) := by
  rw [tailTree,paths_poly_filtered,scalar_selected_paths.1]
  exact congrArg ofList (show pathSum [treeSelectedPath]=monomial (-1) from by native_decide)

theorem tau2_selected_coordinate : ofList (tau2.getD wordEnd [])=ofList one := by
  rw [← sameEntries_getD _ _ tripod_strings.2.1,paths_poly_filtered,scalar_selected_paths.2]
  exact congrArg ofList (show pathSum [twoTripodSelectedPath]=one from by native_decide)


end WebMu.Revised.LocalPaths
