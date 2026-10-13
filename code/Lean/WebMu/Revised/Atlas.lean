import WebMu.Revised.AtlasData
import WebMu.Revised.AtlasGrowth
import WebMu.Revised.AtlasPlanarity

namespace WebMu.Revised.Atlas
open Laurent
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def resolvedTo (g : Graph) (f : Face) (pairs : List (Nat × Nat)) (target : Graph) : Bool :=
  match resolve g f pairs with
  | none => false
  | some h => sameGraph h target

def nodeValid (i : Nat) : Bool :=
  let n := atlasNodes[i]!
  n.children.all (fun j => i < j && j < atlasNodes.size) &&
  if n.rule == 0 then
    n.children.isEmpty && n.leaf < 19 && bijectionValid n.graph atlasSummands[n.leaf]! n.iso
  else if n.rule == 1 then
    n.face.vertices.length == 4 && n.children.length == 2 &&
    resolvedTo n.graph n.face [(0,1),(2,3)] atlasNodes[n.children[0]!]!.graph &&
    resolvedTo n.graph n.face [(1,2),(3,0)] atlasNodes[n.children[1]!]!.graph
  else if n.rule == 2 then
    n.face.vertices.length == 2 && n.children.length == 1 &&
    resolvedTo n.graph n.face [(0,1)] atlasNodes[n.children[0]!]!.graph
  else false

theorem all_graphs_valid : atlasNodes.all (fun n => graphValid n.graph n.signs) = true := by
  native_decide

theorem all_summands_valid : (List.range 19).all (fun i =>
    graphValid atlasSummands[i]! summandSigns[i]!) = true := by native_decide

theorem all_disc_embeddings : atlasNodes.all (fun n => discValid n.graph) = true ∧
    atlasSummands.all discValid = true := by native_decide

theorem complete_atlas_rules : (List.range atlasNodes.size).all nodeValid = true := by
  native_decide

theorem atlas_growth_strings : atlasGrowth = (correctionSteps ++ hSteps).map Prod.fst := by
  decide

theorem terminal_growth_graphs : (List.range 19).all (fun i =>
    let (gs,sm) := (correctionSteps ++ hSteps)[i]!
    match constructSummand gs sm with
    | none => false
    | some g => sameGraph g atlasSummands[i]!) = true := by native_decide

theorem initial_graph_is_capped_block :
    (match constructRoot with
    | none => false
    | some g => bijectionValid g atlasNodes[0]!.graph rootBijection) = true := by native_decide

theorem atlas_tree : atlasNodes.size = 38 ∧
    (atlasNodes.toList.filter (fun n => n.rule == 0)).length = 19 ∧
    (atlasNodes.toList.filter (fun n => n.rule == 1)).length = 18 ∧
    (atlasNodes.toList.filter (fun n => n.rule == 2)).length = 1 ∧
    ((atlasNodes.toList.flatMap (fun n => n.children)).mergeSort (· ≤ ·)) = List.range' 1 37 := by
  native_decide

def expansion : Nat → Nat → List (Nat × Laurent)
  | 0,_ => []
  | fuel+1,i =>
    let n := atlasNodes[i]!
    if n.rule == 0 then [(n.leaf,one)] else
      let terms := n.children.flatMap (expansion fuel)
      if n.rule == 2 then terms.map (fun (j,p) => (j,mul d p)) else terms

theorem complete_coefficients :
    (expansion 38 0).mergeSort (fun a b => a.1 ≤ b.1) =
      (List.range 19).map (fun i => (i,if i < 8 then d else one)) := by native_decide

end WebMu.Revised.Atlas
