import WebMu.Revised.AtlasClosedData
import WebMu.Revised.ClosedChecks

namespace WebMu.Revised.Atlas
open Laurent
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def closedNodeValid (i : Nat) : Bool :=
  let n := closedNodes[i]!
  n.children.all (fun j => i < j && j < closedNodes.size) &&
  if n.rule == 0 then
    n.children.isEmpty && n.graph.edges.isEmpty && n.graph.rotations.isEmpty
  else if n.rule == 1 then
    n.face.vertices.length == 4 && n.children.length == 2 &&
    resolvedTo n.graph n.face [(0,1),(2,3)] closedNodes[n.children[0]!]!.graph &&
    resolvedTo n.graph n.face [(1,2),(3,0)] closedNodes[n.children[1]!]!.graph
  else if n.rule == 2 then
    n.children.length == 1 &&
    (match closedDigon n.graph n.face with
    | none => false
    | some g => sameGraph g closedNodes[n.children[0]!]!.graph)
  else false

def closedExpansion : Nat → Nat → Laurent
  | 0,_ => []
  | fuel+1,i =>
    let n := closedNodes[i]!
    if n.rule == 0 then pow e n.graph.circles else
      let x := n.children.foldl (fun p j => add p (closedExpansion fuel j)) []
      if n.rule == 2 then mul d x else x

def closedTargets : List Laurent :=
  let h := add (pow d 2) (monomial 0 2)
  [mul (mul (pow d 7) e) (pow h 2),
   shiftScale (mul (mul (pow d 7) e) h) 0 2,
   mul (mul (pow d 8) e) h,
   mul (pow d 5) e,
   mul (pow d 5) e,
   mul (mul (pow d 3) e) (pow h 2),
   shiftScale (mul (mul (pow d 3) e) h) 0 2,
   mul (mul (pow d 2) e) h,
   shiftScale (mul (pow d 2) e) 0 2]

theorem closed_graphs_wellformed :
    closedNodes.all (fun n => closedGraphValid n.graph n.signs) = true := by native_decide

theorem closed_graphs_planar :
    closedNodes.all (fun n => closedPlanar n.graph) = true := by native_decide

theorem complete_closed_reductions :
    (List.range closedNodes.size).all closedNodeValid = true := by native_decide

theorem closed_forest : closedNodes.size = 209 ∧
    ((closedRoots ++ closedNodes.toList.flatMap (fun n => n.children)).mergeSort (· ≤ ·)) =
      List.range closedNodes.size := by native_decide

/-- All nine evaluations come from exhaustive circle/digon/square trees. -/
theorem closed_scalar_values : closedRoots.map (closedExpansion 210) = closedTargets := by
  native_decide

theorem closed_source_graphs :
    (List.range 3).all (fun i =>
      match closeTripods atlasNodes[([0,1,23] : List Nat)[i]!]!.graph 12 with
      | none => false
      | some g => sameGraph g closedNodes[closedRoots[i]!]!.graph) = true ∧
    (match constructClosedShortPrefix with
      | none => false
      | some g => sameGraph g closedNodes[closedRoots[3]!]!.graph) = true ∧
    (match constructClosedTail with
      | none => false
      | some g => sameGraph g closedNodes[closedRoots[4]!]!.graph) = true := by native_decide

def chainValid (g : Graph) : List (Graph × Face) → Graph → Bool
  | [],terminal => sameGraph g terminal
  | (h,f)::rest,terminal => sameGraph g h &&
      match closedDigon h f with
      | none => false
      | some h' => chainValid h' rest terminal

def coreTargetValid (b : CoreBranch) : Bool :=
  if b.target < 4 then closedBijectionValid b.terminal closedCores[b.target]! b.iso
  else b.target == 4 && b.terminal.edges.isEmpty && b.terminal.rotations.isEmpty &&
    b.terminal.circles == 1

def coreBranchValid (g : Graph) (b : CoreBranch) : Bool :=
  chainValid g b.chain b.terminal && coreTargetValid b

theorem closure_to_cores :
    (List.range 3).all (fun i =>
      coreBranchValid closedNodes[closedRoots[i]!]!.graph closureBranches[i]! &&
      closureBranches[i]!.target == i) = true ∧
    closureBranches.toList.map (fun b => b.chain.length) = [4,4,6] := by native_decide

theorem four_core_square_relations :
    (List.range 4).all (fun i =>
      (List.range 2).all (fun j =>
        match resolve closedCores[i]! coreFaces[i]!
            (if j == 0 then [(0,1),(2,3)] else [(1,2),(3,0)]) with
        | none => false
        | some g => coreBranchValid g coreBranches[2*i+j]!)) = true ∧
    coreBranches.toList.map (fun b => (b.chain.length,b.target)) =
      [(0,1),(3,2),(1,2),(1,2),(4,4),(0,3),(2,4),(2,4)] := by native_decide

def extendColor (g : Graph) (ss : List (String × Bool)) : List (String × Bool) :=
  g.edges.foldl (fun out (_,a,b) =>
    match lookup out a,lookup out b with
    | some s,none => (b,!s)::out
    | none,some s => (a,!s)::out
    | _,_ => out) ss

def graphColor (g : Graph) : List (String × Bool) :=
  g.rotations.foldl (fun out (v,_) =>
    if (lookup out v).isSome then out else
      (List.range g.rotations.length).foldl (fun ss _ => extendColor g ss) ((v,true)::out)) []

theorem all_core_chain_graphs_valid :
    (closureBranches.toList ++ coreBranches.toList).all (fun b =>
      (b.terminal :: b.chain.map Prod.fst).all (fun g =>
        closedGraphValid g (graphColor g) && closedPlanar g)) = true := by native_decide

end WebMu.Revised.Atlas
