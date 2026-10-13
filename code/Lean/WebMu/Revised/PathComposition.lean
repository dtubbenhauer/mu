import WebMu.Revised.LocalPathDerivations

/-! Composition of uncollected elementary paths. These lemmas allow the local
proof to use its printed intermediate stages without re-enumerating the final
composite bound. -/
namespace WebMu.Revised.LocalPaths
open Laurent Algebra Bar

def join (p q : Path) : Path :=
  ⟨p.input,q.output,p.edges++q.edges,p.degree+q.degree,p.multiplicity*q.multiplicity⟩

theorem join_initial (p : Path) : join p (initial p.output)=p := by
  cases p
  simp [join,initial]

theorem join_extend (p q : Path) (e : Edge) :
    join p (extend q e)=extend (join p q) e := by
  simp [join,extend,List.append_assoc,Int.add_assoc,Int.mul_assoc]

def walk : List Step → Path → List Path
  | [], p => [p]
  | s::ss, p => (branches s p.output).flatMap fun e => walk ss (extend p e)

theorem fold_walk (ss : List Step) (ps : List Path) :
    ss.foldl (fun ps s => advance s ps) ps=ps.flatMap (walk ss) := by
  induction ss generalizing ps with
  | nil => simp [walk]
  | cons s ss ih =>
    change ss.foldl (fun ps s => advance s ps) (advance s ps)=_
    rw [ih]
    simp [advance,walk,List.flatMap_assoc,List.flatMap_map,Function.comp_def]

theorem walk_join (ss : List Step) (p q : Path) :
    walk ss (join p q)=(walk ss q).map (join p) := by
  induction ss generalizing q with
  | nil => rfl
  | cons s ss ih =>
    simp only [walk,← join_extend,List.map_flatMap]
    change (branches s q.output).flatMap (fun e => walk ss (join p (extend q e))) = _
    simp only [ih]

theorem walk_initial (ss : List Step) (u : Word) : walk ss (initial u)=paths ss u := by
  simp [paths,fold_walk]

theorem walk_from (ss : List Step) (p : Path) :
    walk ss p=(paths ss p.output).map (join p) := by
  rw [← walk_initial,← walk_join,join_initial]

theorem paths_append (a b : List Step) (u : Word) :
    paths (a++b) u=(paths a u).flatMap fun p => (paths b p.output).map (join p) := by
  rw [show paths (a++b) u=b.foldl (fun ps s => advance s ps) (paths a u) by
    simp only [paths,List.foldl_append]]
  rw [fold_walk]
  congr 1
  funext p
  exact walk_from b p

theorem downPaths_append (a b : List Step) (u : Word) :
    downPaths (a++b) u=(downPaths b u).flatMap fun p =>
      (downPaths a p.output).map (join p) := by
  simp only [downPaths,List.reverse_append,paths_append]

theorem mem_downPaths_append (a b : List Step) (u : Word) (p : Path) :
    p ∈ downPaths (a++b) u ↔ ∃ q ∈ downPaths b u,
      ∃ r ∈ downPaths a q.output, p=join q r := by
  rw [downPaths_append]
  simp only [List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨q,hq,r,hr,he⟩; exact ⟨q,hq,r,hr,he.symm⟩
  · rintro ⟨q,hq,r,hr,he⟩; exact ⟨q,hq,r,hr,he.symm⟩

theorem join_assoc (p q r : Path) : join (join p q) r=join p (join q r) := by
  simp [join,List.append_assoc,Int.add_assoc,Int.mul_assoc]

end WebMu.Revised.LocalPaths
