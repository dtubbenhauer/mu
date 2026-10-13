import WebMu.RevisedLocal

namespace WebMu.Revised.Atlas

abbrev Edge := Nat × String × String
structure Graph where
  edges : List Edge
  rotations : List (String × List Nat)
  nextEdge : Nat
  circles : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

structure Face where
  vertices : List String
  edges : List Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure Bijection where
  vertices : List (String × String)
  edges : List (Nat × Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Node where
  graph : Graph
  face : Face
  rule : Nat -- 0=leaf, 1=square, 2=digon
  children : List Nat
  leaf : Nat -- D1,...,D8,H1,...,H11 = 0,...,18
  iso : Bijection
  signs : List (String × Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

def lookup [BEq α] (xs : List (α × β)) (k : α) : Option β :=
  (xs.find? (fun x => x.1 == k)).map Prod.snd

def boundary : List String := (List.range 12).map fun i => s!"b{i+1}"
def rot (g : Graph) (v : String) : List Nat := (lookup g.rotations v).getD []
def edge (g : Graph) (e : Nat) : Option (String × String) := lookup g.edges e
def other (g : Graph) (e : Nat) (v : String) : Option String := do
  let (a,b) ← edge g e
  if v == a then some b else if v == b then some a else none

def cyclicEqual [BEq α] (xs ys : List α) : Bool :=
  xs.length == ys.length &&
    (if ys.isEmpty then xs.isEmpty else (List.range ys.length).any fun i =>
      xs == ys.drop i ++ ys.take i)

def sameGraph (g h : Graph) : Bool :=
  g.circles == h.circles && g.nextEdge == h.nextEdge &&
  g.edges.length == h.edges.length && g.rotations.length == h.rotations.length &&
  g.edges.all (fun (e,a,b) => match edge h e with
    | some (c,d) => (a == c && b == d) || (a == d && b == c)
    | none => false) &&
  g.rotations.all (fun (v,r) => lookup h.rotations v == some r)

def graphValid (g : Graph) (signs : List (String × Bool)) : Bool :=
  g.circles == 0 &&
  decide ((g.edges.map Prod.fst).Nodup) &&
  decide ((g.rotations.map Prod.fst).Nodup) &&
  decide ((signs.map Prod.fst).Nodup) &&
  signs.length == g.rotations.length &&
  g.edges.all (fun (e,a,b) => e < g.nextEdge && a != b &&
    (g.rotations.any (fun p => p.1 == a)) && (g.rotations.any (fun p => p.1 == b)) &&
    match lookup signs a, lookup signs b with
      | some sa, some sb => sa != sb
      | _, _ => false) &&
  g.rotations.all (fun (v,r) =>
    decide r.Nodup && r.length == (if boundary.contains v then 1 else 3) &&
    r.all (fun e => (other g e v).isSome) &&
    (g.edges.filter (fun (_,a,b) => a == v || b == v)).length == r.length) &&
  (List.range 12).all (fun i =>
    let v := s!"b{i+1}"
    (lookup g.rotations v).isSome && lookup signs v == some (decide (i < 9)))

def faceValid (g : Graph) (f : Face) : Bool :=
  (f.vertices.length == 2 || f.vertices.length == 4) &&
  f.edges.length == f.vertices.length && decide f.vertices.Nodup && decide f.edges.Nodup &&
  f.vertices.all (fun v => !(boundary.contains v)) &&
  (List.range f.vertices.length).all (fun i =>
    let v := f.vertices[i]!
    let next := f.vertices[(i+1)%f.vertices.length]!
    let e := f.edges[i]!
    let nextEdge := f.edges[(i+1)%f.edges.length]!
    other g e v == some next &&
    let r := rot g next
    let pos := r.idxOf e
    pos < r.length && r[(pos+r.length-1)%r.length]! == nextEdge)

def exterior (g : Graph) (f : Face) : Option (List (Nat × String)) :=
  f.vertices.mapM fun v => do
    let es := (rot g v).filter (fun e => !(f.edges.contains e))
    if es.length != 1 then none else do
      let e := es[0]!
      let w ← other g e v
      return (e,w)

def replaceEdge (rs : List (String × List Nat)) (v : String) (old new : Nat) :
    List (String × List Nat) := rs.map fun (w,r) =>
  (w,if w == v then r.map (fun e => if e == old then new else e) else r)

def resolve (g : Graph) (f : Face) (pairs : List (Nat × Nat)) : Option Graph := do
  if !faceValid g f then none else do
    let ext ← exterior g f
    if !decide (ext.map Prod.fst).Nodup then none else do
      let removed := f.edges ++ ext.map Prod.fst
      let init : Graph := ⟨g.edges.filter (fun (e,_) => !(removed.contains e)),
        g.rotations.filter (fun (v,_) => !(f.vertices.contains v)),g.nextEdge,g.circles⟩
      pairs.foldlM (fun out (i,j) => do
        let (ei,vi) ← ext[i]?
        let (ej,vj) ← ext[j]?
        if vi == vj then none else
          some ⟨out.edges ++ [(out.nextEdge,vi,vj)],
            replaceEdge (replaceEdge out.rotations vi ei out.nextEdge) vj ej out.nextEdge,
            out.nextEdge+1,out.circles⟩) init

def bijectionValid (g h : Graph) (b : Bijection) : Bool :=
  b.vertices.length == g.rotations.length && b.vertices.length == h.rotations.length &&
  b.edges.length == g.edges.length && b.edges.length == h.edges.length &&
  decide (b.vertices.map Prod.fst).Nodup && decide (b.vertices.map Prod.snd).Nodup &&
  decide (b.edges.map Prod.fst).Nodup && decide (b.edges.map Prod.snd).Nodup &&
  boundary.all (fun v => lookup b.vertices v == some v) &&
  g.edges.all (fun (e,a,c) => match lookup b.edges e,lookup b.vertices a,lookup b.vertices c with
    | some e',some a',some c' => match edge h e' with
      | some (u,v) => (u == a' && v == c') || (u == c' && v == a')
      | none => false
    | _,_,_ => false) &&
  g.rotations.all (fun (v,r) => match lookup b.vertices v with
    | some v' => match r.mapM (lookup b.edges), lookup h.rotations v' with
      | some rs,some rs' => cyclicEqual rs rs'
      | _,_ => false
    | none => false)

end WebMu.Revised.Atlas
