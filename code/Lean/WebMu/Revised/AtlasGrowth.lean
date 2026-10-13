import WebMu.Revised.AtlasTypes

/-! Combinatorial growth with explicit trivalent ports and circular boundary.
At a downward merge the input ports are 0,2 and the output is 1; a downward
split has input 0 and outputs 1,2. These conventions fix every cyclic order. -/
namespace WebMu.Revised.Atlas

def vacant : Nat := 1000000
abbrev Port := String × Nat
structure Build where
  graph : Graph
  active : List Port
  signs : List Bool
  deriving Repr, Inhabited

def start (names : List String) : Build :=
  ⟨⟨[],names.map (fun v => (v,[vacant])),0,0⟩,
    names.map (fun v => (v,0)),List.replicate names.length true⟩

def vertex (s : Build) : String × Build :=
  let v := s!"u{s.graph.rotations.length}"
  (v,{s with graph := {s.graph with rotations := s.graph.rotations ++ [(v,[vacant,vacant,vacant])]}})

def setPort (rs : List (String × List Nat)) (v : String) (i e : Nat) :
    List (String × List Nat) := rs.map fun (w,r) => (w,if w == v then r.set i e else r)

def connect (s : Build) (a b : Port) : Option Build := do
  let ra ← lookup s.graph.rotations a.1
  let rb ← lookup s.graph.rotations b.1
  if a.1 == b.1 || ra[a.2]? != some vacant || rb[b.2]? != some vacant then none else
    let e := s.graph.nextEdge
    some {s with graph :=
      ⟨s.graph.edges ++ [(e,a.1,b.1)],setPort (setPort s.graph.rotations a.1 a.2 e) b.1 b.2 e,e+1,0⟩}

def merge (s : Build) (i : Nat) : Option Build := do
  let a ← s.active[i]?
  let b ← s.active[i+1]?
  let sa ← s.signs[i]?
  let sb ← s.signs[i+1]?
  if sa != sb then none else do
    let (v,s) := vertex s
    let s ← connect s a (v,0)
    let s ← connect s b (v,2)
    return {s with
      active := s.active.take i ++ [(v,1)] ++ s.active.drop (i+2)
      signs := s.signs.take i ++ [!sa] ++ s.signs.drop (i+2)}

def split (s : Build) (i : Nat) : Option Build := do
  let a ← s.active[i]?
  let sa ← s.signs[i]?
  let (v,s) := vertex s
  let s ← connect s a (v,0)
  return {s with
    active := s.active.take i ++ [(v,1),(v,2)] ++ s.active.drop (i+1)
    signs := s.signs.take i ++ [!sa,!sa] ++ s.signs.drop (i+1)}

def arc (s : Build) (i : Nat) : Option Build := do
  let a ← s.active[i]?
  let b ← s.active[i+1]?
  let sa ← s.signs[i]?
  let sb ← s.signs[i+1]?
  if sa == sb then none else do
    let s ← connect s a b
    return {s with
      active := s.active.take i ++ s.active.drop (i+2)
      signs := s.signs.take i ++ s.signs.drop (i+2)}

def growthStep (s : Build) (step : Step) : Option Build :=
  match step with
  | (.y,i) => merge s i
  | (.h,i) => do let s ← split s (i+1); merge s i
  | (.cup,i) => arc s i
  | _ => none

def smallStep (s : Build) (step : Step) : Option Build :=
  match step with
  | (.lam,i) => split s i
  | (.y,i) => merge s i
  | _ => none

def attachInputs (s : Build) : Option Graph := do
  if s.active.length != 3 || s.signs != [true,true,true] then none else do
    let s ← (List.range 3).foldlM (fun s i => do
      let p ← s.active[i]?
      let v := s!"b{12-i}"
      let s := {s with graph := {s.graph with rotations := s.graph.rotations ++ [(v,[vacant])]}}
      connect s p (v,0)) s
    return s.graph

def constructSummand (growth small : List Step) : Option Graph := do
  let s ← growth.foldlM growthStep (start ((List.range 9).map fun i => s!"b{i+1}"))
  let s ← if small == [(.lam,0),(.sigma,0)] then
    if s.active != [] then none else
      let (v,s) := vertex s
      some {s with active := [(v,0),(v,1),(v,2)],signs := [true,true,true]}
    else small.reverse.foldlM smallStep s
  attachInputs s

/-- The capped block has top b1,...,b9, bottom b12,b11,b10.
The cap rotation follows the three removed top endpoints in their fixed linear order. -/
def constructRoot : Option Graph := do
  let names := ["o0","o1","o2"] ++ (List.range 9).map (fun i => s!"b{i+1}")
  let s ← blockSteps.foldlM growthStep (start names)
  let g ← attachInputs s
  let e0 ← (rot g "o0")[0]?
  let e1 ← (rot g "o1")[0]?
  let e2 ← (rot g "o2")[0]?
  let capped := ["o0","o1","o2"]
  let rename := fun v => if capped.contains v then "eta" else v
  return {g with
    edges := g.edges.map (fun (e,a,b) => (e,rename a,rename b)),
    rotations := (g.rotations.filter (fun (v,_) => !(capped.contains v))) ++ [("eta",[e0,e1,e2])]}

end WebMu.Revised.Atlas
