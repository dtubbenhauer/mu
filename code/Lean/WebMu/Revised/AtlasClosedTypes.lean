import WebMu.Revised.Atlas

/-! Closed ribbon reductions. Parallel exterior edges in a digon form a
theta component; its reduction records one disjoint circle. No drawing
coordinates are used by any check. -/
namespace WebMu.Revised.Atlas

def closedGraphValid (g : Graph) (signs : List (String × Bool)) : Bool :=
  decide ((g.edges.map Prod.fst).Nodup) &&
  decide ((g.rotations.map Prod.fst).Nodup) &&
  decide ((signs.map Prod.fst).Nodup) &&
  signs.length == g.rotations.length &&
  g.edges.all (fun (e,a,b) => e < g.nextEdge && a != b &&
    (lookup g.rotations a).isSome && (lookup g.rotations b).isSome &&
    match lookup signs a,lookup signs b with
    | some sa,some sb => sa != sb
    | _,_ => false) &&
  g.rotations.all (fun (v,r) => !boundary.contains v &&
    decide r.Nodup && r.length == 3 &&
    r.all (fun e => (other g e v).isSome) &&
    (g.edges.filter (fun (_,a,b) => a == v || b == v)).length == 3)

/-- Euler characteristic is checked separately for every connected component. -/
def closedPlanar (g : Graph) : Bool :=
  let ds := darts g
  let walks := ds.map (fun d => orbit g d (ds.length+1) d [])
  let faces := (List.range ds.length).filter fun i =>
    match walks[i]! with
    | none => false
    | some ws => ws.all (fun d => i ≤ ds.idxOf d)
  walks.all (fun o => match o with
    | none => false
    | some ws => decide ws.Nodup && ws.all ds.contains) &&
  g.rotations.all (fun (v,_) =>
    let vs := reachable g g.rotations.length [v]
    let es := g.edges.filter (fun (_,a,_) => vs.contains a)
    let fs := faces.filter (fun i => vs.contains ds[i]!.2)
    vs.length + fs.length == es.length + 2)

def closedDigon (g : Graph) (f : Face) : Option Graph := do
  if f.vertices.length != 2 || !faceValid g f then none else do
    let ext ← exterior g f
    let (a,av) ← ext[0]?
    let (b,bv) ← ext[1]?
    if a != b then resolve g f [(0,1)] else
      if av != f.vertices[1]! || bv != f.vertices[0]! then none else
        some ⟨g.edges.filter (fun (e,_) => !(f.edges ++ [a]).contains e),
          g.rotations.filter (fun (v,_) => !f.vertices.contains v),
          g.nextEdge,g.circles+1⟩

def closedBijectionValid (g h : Graph) (b : Bijection) : Bool :=
  g.circles == h.circles &&
  b.vertices.length == g.rotations.length && b.vertices.length == h.rotations.length &&
  b.edges.length == g.edges.length && b.edges.length == h.edges.length &&
  decide (b.vertices.map Prod.fst).Nodup && decide (b.vertices.map Prod.snd).Nodup &&
  decide (b.edges.map Prod.fst).Nodup && decide (b.edges.map Prod.snd).Nodup &&
  g.edges.all (fun (e,a,c) => match lookup b.edges e,lookup b.vertices a,lookup b.vertices c with
    | some e',some a',some c' => match edge h e' with
      | some (u,v) => (u == a' && v == c') || (u == c' && v == a')
      | none => false
    | _,_,_ => false) &&
  g.rotations.all (fun (v,r) => match lookup b.vertices v with
    | some v' => match r.mapM (lookup b.edges),lookup h.rotations v' with
      | some rs,some rs' => cyclicEqual rs rs'
      | _,_ => false
    | none => false)

/-- Boundary labels are grouped in their prescribed circular order. -/
def closeTripods (g : Graph) (width : Nat) : Option Graph :=
  (List.range (width/3)).foldlM (fun g i => do
    let names := (List.range 3).map fun j => s!"b{3*i+j+1}"
    let ports ← names.mapM fun v => do
      let r ← lookup g.rotations v
      if r.length != 1 then none else r[0]?
    let v := s!"closed_tripod_{3*i}"
    if (lookup g.rotations v).isSome then none else
      let rename := fun w => if names.contains w then v else w
      some {g with
        edges := g.edges.map (fun (e,a,b) => (e,rename a,rename b)),
        rotations := g.rotations.filter (fun (w,_) => !names.contains w) ++ [(v,ports)]}) g

def constructClosedShortPrefix : Option Graph := do
  let s ← shortPrefixSteps.foldlM growthStep
    (start ((List.range 6).map fun i => s!"b{i+1}"))
  if s.active.length != 3 || s.signs != [true,true,true] then none else do
    let s ← (List.range 3).foldlM (fun s i => do
      let p ← s.active[i]?
      let v := s!"b{9-i}"
      let s := {s with graph := {s.graph with rotations :=
        s.graph.rotations ++ [(v,[vacant])]}}
      connect s p (v,0)) s
    closeTripods s.graph 9

def constructClosedTail : Option Graph := do
  let s ← tailSteps.foldlM growthStep
    (start ((List.range 9).map fun i => s!"b{i+1}"))
  if !s.active.isEmpty || !s.signs.isEmpty then none else
    closeTripods s.graph 9

structure ClosedNode where
  graph : Graph
  face : Face
  rule : Nat -- 0=circles only, 1=square, 2=digon
  children : List Nat
  signs : List (String × Bool)
  deriving Repr,BEq,DecidableEq,Inhabited

/-- A square followed by a digon chain on each branch; terminal cores are
identified by explicit orientation-preserving ribbon isomorphisms. -/
structure CoreBranch where
  chain : List (Graph × Face)
  terminal : Graph
  target : Nat -- 0=G22,1=G18,2=G12,3=G8,4=one circle
  iso : Bijection
  deriving Repr,BEq,DecidableEq,Inhabited

end WebMu.Revised.Atlas
