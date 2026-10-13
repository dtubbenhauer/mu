import WebMu.Revised.AtlasBindings
import WebMu.Revised.M2Data

namespace WebMu.Revised.TripodGraphs
open Atlas
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- All-positive boundary growth; every port must be consumed. -/
def growthGraph (width : Nat) (steps : List Step) : Option Graph := do
  let s ← steps.foldlM growthStep (start ((List.range width).map (fun i => s!"b{i+1}")))
  if s.active.isEmpty && s.signs.isEmpty then some s.graph else none

def boundaryNames (width : Nat) := (List.range width).map (fun i => s!"b{i+1}")

def extendBoundaryColor (g : Graph) : Nat → List (String × Bool) → List (String × Bool)
  | 0,ss => ss
  | fuel+1,ss =>
    let tt := extendColor g ss
    if tt.length == ss.length then tt else extendBoundaryColor g fuel tt

def boundaryColor (width : Nat) (g : Graph) : List (String × Bool) :=
  extendBoundaryColor g g.rotations.length ((boundaryNames width).map (fun v => (v,true)))

def allPositiveGraphValid (width : Nat) (g : Graph) : Bool :=
  let bs := boundaryNames width
  let ss := boundaryColor width g
  g.circles == 0 && decide (g.edges.map Prod.fst).Nodup &&
  decide (g.rotations.map Prod.fst).Nodup &&
  decide (ss.map Prod.fst).Nodup && ss.length == g.rotations.length &&
  g.edges.all (fun (e,a,b) => e < g.nextEdge && a != b &&
    (lookup g.rotations a).isSome && (lookup g.rotations b).isSome &&
    match lookup ss a,lookup ss b with
    | some sa,some sb => sa != sb
    | _,_ => false) &&
  g.rotations.all (fun (v,r) => decide r.Nodup &&
    r.length == (if bs.contains v then 1 else 3) &&
    r.all (fun e => (other g e v).isSome) &&
    (g.edges.filter (fun (_,a,b) => a == v || b == v)).length == r.length) &&
  bs.all (fun v => (lookup g.rotations v).isSome && lookup ss v == some true)

def rimN (width : Nat) (g : Graph) : Graph :=
  let bs := boundaryNames width
  let newEdges := (List.range width).map (fun i =>
    (g.nextEdge+i,bs[i]!,bs[(i+1)%width]!))
  let rs := g.rotations.map (fun (v,r) => if bs.contains v then
    let i := bs.idxOf v
    (v,r ++ [g.nextEdge+i,g.nextEdge+(i+width-1)%width]) else (v,r))
  ⟨g.edges ++ newEdges,rs,g.nextEdge+width,g.circles⟩

/-- Reachability by bounded breadth-first expansion. Membership is tested
before insertion, so every intermediate vertex list is duplicate-free. -/
def reachableN (g : Graph) : Nat → List String → List String
  | 0,vs => vs
  | fuel+1,vs =>
    let ws := g.edges.foldl (fun out (_,a,b) =>
      if vs.contains a || vs.contains b then
        let out := if out.contains a then out else a::out
        if out.contains b then out else b::out
      else out) vs
    if ws.length == vs.length then ws else reachableN g fuel ws

/-- Fixed boundary order, all face orbits and Euler characteristic checked. -/
def discValidN (width : Nat) (g : Graph) : Bool :=
  let g := rimN width g
  let ds := darts g
  let walks := ds.map (fun d => orbit g d (ds.length+1) d [])
  let faces := (List.range ds.length).filter (fun i =>
    match walks[i]! with | none => false | some ws => ws.all (fun d => i ≤ ds.idxOf d))
  let reached := reachableN g g.rotations.length ["b1"]
  g.rotations.all (fun (v,_) => reached.contains v) &&
  walks.all (fun o => match o with
    | none => false
    | some ws => decide ws.Nodup && ws.all ds.contains) &&
  g.rotations.length + faces.length == g.edges.length + 2

/-- Remove precisely the isolated positive tripod on boundary outputs 7--9.
Its cyclic order is that of the elementary positive tripod: 7,9,8.
Remaining output names shift left by three after output 6. -/
def deleteTripod (g : Graph) : Option Graph := do
  let e7 ← (rot g "b7")[0]?
  let e8 ← (rot g "b8")[0]?
  let e9 ← (rot g "b9")[0]?
  let c ← other g e7 "b7"
  if (boundaryNames 33).contains c || other g e8 "b8" != some c ||
      other g e9 "b9" != some c || !cyclicEqual (rot g c) [e7,e9,e8] then none else
    let removed := ["b7","b8","b9",c]
    let rename := fun v =>
      (lookup ((List.range 24).map (fun i => (s!"b{i+10}",s!"b{i+7}"))) v).getD v
    some {g with
      edges := (g.edges.filter (fun (_,a,b) => !(removed.contains a || removed.contains b))).map
        (fun (e,a,b) => (e,rename a,rename b)),
      rotations := (g.rotations.filter (fun (v,_) => !removed.contains v)).map
        (fun (v,r) => (rename v,r))}

structure TripodEntry where
  paddedWord : Word
  paddedSteps : List Step
  iso : Bijection
  deriving Inhabited, Repr

def shortenedWords : Array Word := #[M2Data.target] ++ M2Data.entries.map M2Flow.Entry.word
def shortenedSteps : Array (List Step) := #[M2Data.targetSteps] ++ M2Data.entries.map M2Flow.Entry.steps

def tripodEntryValid (i : Nat) (e : TripodEntry) : Bool :=
  e.paddedWord.length == 33 && (e.paddedWord.drop 6).take 3 == [0,1,2] &&
  e.paddedWord.take 6 ++ e.paddedWord.drop 9 == shortenedWords[i]! &&
  M2Flow.validGrowth e.paddedWord e.paddedSteps &&
  match growthGraph 33 e.paddedSteps,growthGraph 30 shortenedSteps[i]! with
  | some padded,some shortened =>
    allPositiveGraphValid 33 padded && allPositiveGraphValid 30 shortened &&
    discValidN 33 padded && discValidN 30 shortened &&
    match deleteTripod padded with
    | none => false
    | some deleted => allPositiveGraphValid 30 deleted && discValidN 30 deleted &&
      closedBijectionValid deleted shortened e.iso &&
      (boundaryNames 30).all (fun v => lookup e.iso.vertices v == some v)
  | _,_ => false

end WebMu.Revised.TripodGraphs
