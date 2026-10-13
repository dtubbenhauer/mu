import WebMu.Revised.AtlasTypes

/-! A finite rotation-system check after adjoining the fixed boundary rim.
`discValid` checks connectedness, every face orbit, and Euler characteristic 2.
The interpretation of these conditions as a planar disc embedding is the
standard rotation-system classification, separate from the computation. -/
namespace WebMu.Revised.Atlas

abbrev Dart := Nat × String
def darts (g : Graph) : List Dart := g.edges.flatMap (fun (e,a,b) => [(e,a),(e,b)])

def rim (g : Graph) : Graph :=
  let newEdges := (List.range 12).map fun i =>
    (g.nextEdge+i,boundary[i]!,boundary[(i+1)%12]!)
  let rs := g.rotations.map fun (v,r) =>
    if boundary.contains v then
      let i := boundary.idxOf v
      (v,r ++ [g.nextEdge+i,g.nextEdge+(i+11)%12])
    else (v,r)
  ⟨g.edges ++ newEdges,rs,g.nextEdge+12,g.circles⟩

def nextDart (g : Graph) (d : Dart) : Option Dart := do
  let w ← other g d.1 d.2
  let r := rot g w
  let i := r.idxOf d.1
  if i >= r.length then none else
    some (r[(i+r.length-1)%r.length]!,w)

def orbit (g : Graph) (first : Dart) : Nat → Dart → List Dart → Option (List Dart)
  | 0,_,_ => none
  | fuel+1,current,seen => do
    if seen.contains current then none else do
      let next ← nextDart g current
      let seen := seen ++ [current]
      if next == first then some seen else orbit g first fuel next seen

def reachable (g : Graph) : Nat → List String → List String
  | 0,vs => vs
  | fuel+1,vs =>
    let ws := g.edges.foldl (fun out (_,a,b) =>
      if vs.contains a || vs.contains b then (a::b::out).eraseDups else out) vs
    reachable g fuel ws

def discValid (g : Graph) : Bool :=
  let g := rim g
  let ds := darts g
  let walks := ds.map (fun d => orbit g d (ds.length+1) d [])
  let faces := (List.range ds.length).filter fun i =>
    match walks[i]! with
    | none => false
    | some ws => ws.all (fun d => i ≤ ds.idxOf d)
  let reached := reachable g g.rotations.length ["b1"]
  g.rotations.all (fun (v,_) => reached.contains v) &&
  walks.all (fun o => match o with
    | none => false
    | some ws => decide ws.Nodup && ws.all ds.contains) &&
  g.rotations.length + faces.length == g.edges.length + 2

end WebMu.Revised.Atlas
