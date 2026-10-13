import WebMu.Revised.AtlasBindings
import WebMu.Revised.GrowthPairing
import WebMu.Revised.Bar

/-! Declarative elementary ribbon attachments.  The predicates in this file
do not call the graph-growth compiler.  They specify the entire incidence
and rotation lists before and after a single local operation.  Certificates
for the finite source constructions are checked against these predicates.

The active ports occur in left-to-right order at the lower boundary.  A
vacant rotation slot is an open edge end, rather than an omitted tensor
factor.  Merge ports are (0,2;1), split ports are (0;1,2), exactly as in the
drawn trivalent vertices. -/
namespace WebMu.Revised.AtlasSurgery
open Atlas Laurent Algebra GrowthBridge GrowthPairing M2Flow
set_option maxHeartbeats 0
set_option maxRecDepth 100000

instance : BEq Build where
  beq s t := s.graph == t.graph && s.active == t.active && s.signs == t.signs

instance : DecidableEq Build := fun s t =>
  match s,t with
  | ⟨g,a,ss⟩,⟨h,b,ts⟩ => by
    by_cases hg : g=h
    · by_cases ha : a=b
      · by_cases hs : ss=ts
        · exact isTrue (by cases hg; cases ha; cases hs; rfl)
        · exact isFalse (fun he => hs (Build.mk.inj he).2.2)
      · exact isFalse (fun he => ha (Build.mk.inj he).2.1)
    · exact isFalse (fun he => hg (Build.mk.inj he).1)

inductive Atom where
  | merge (i : Nat)
  | split (i : Nat)
  | arc (i : Nat)
  | cap
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Simultaneously plug a finite list of old open ports.  This is a
declarative update of every old rotation slot, with no search or growth. -/
def plugged (rs : List (String × List Nat)) (ps : List (Port × Nat)) :=
  rs.map fun (v,r) => (v,r.zipIdx |>.map fun (e,i) =>
    ((ps.find? (fun (z : Port × Nat) => z.1 == (v,i))).map Prod.snd).getD e)

def freshVertex (s : Build) (v : String) : Bool :=
  !(s.graph.rotations.any fun z => z.1 == v)

def openPort (s : Build) (p : Port) : Bool :=
  (rot s.graph p.1)[p.2]? == some vacant

/-- One downward merge: two adjacent equal signs meet ports 0 and 2;
port 1 is the surviving input.  No graph incidence is left unchecked. -/
def mergeRelation (s t : Build) (i : Nat) : Bool :=
  match s.active[i]?,s.active[i+1]?,s.signs[i]?,s.signs[i+1]?,t.active[i]? with
  | some a,some b,some sa,some sb,some p =>
    let v := p.1
    let e := s.graph.nextEdge
    a != b && openPort s a && openPort s b && freshVertex s v && sa == sb &&
    s.active.length == s.signs.length &&
    t.active == s.active.take i ++ [(v,1)] ++ s.active.drop (i+2) &&
    t.signs == s.signs.take i ++ [!sa] ++ s.signs.drop (i+2) &&
    t.graph == ⟨s.graph.edges ++ [(e,a.1,v),(e+1,b.1,v)],
      plugged s.graph.rotations [(a,e),(b,e+1)] ++ [(v,[e,vacant,e+1])],e+2,0⟩ &&
    s.graph.circles == 0
  | _,_,_,_,_ => false

/-- One downward split: the old open edge meets port 0; ports 1,2 become
adjacent ordered inputs. -/
def splitRelation (s t : Build) (i : Nat) : Bool :=
  match s.active[i]?,s.signs[i]?,t.active[i]? with
  | some a,some sa,some p =>
    let v := p.1
    let e := s.graph.nextEdge
    openPort s a && freshVertex s v && s.active.length == s.signs.length &&
    t.active == s.active.take i ++ [(v,1),(v,2)] ++ s.active.drop (i+1) &&
    t.signs == s.signs.take i ++ [!sa,!sa] ++ s.signs.drop (i+1) &&
    t.graph == ⟨s.graph.edges ++ [(e,a.1,v)],
      plugged s.graph.rotations [(a,e)] ++ [(v,[e,vacant,vacant])],e+1,0⟩ &&
    s.graph.circles == 0
  | _,_,_ => false

/-- Join two adjacent opposite-sign open ends, with no trivalent vertex. -/
def arcRelation (s t : Build) (i : Nat) : Bool :=
  match s.active[i]?,s.active[i+1]?,s.signs[i]?,s.signs[i+1]? with
  | some a,some b,some sa,some sb =>
    let e := s.graph.nextEdge
    a.1 != b.1 && openPort s a && openPort s b && sa != sb &&
    s.active.length == s.signs.length &&
    t.active == s.active.take i ++ s.active.drop (i+2) &&
    t.signs == s.signs.take i ++ s.signs.drop (i+2) &&
    t.graph == ⟨s.graph.edges ++ [(e,a.1,b.1)],
      plugged s.graph.rotations [(a,e),(b,e)],e+1,0⟩ && s.graph.circles == 0
  | _,_,_,_ => false

/-- A disjoint trivalent cap with all three inputs positive. Its circular
ports are 0,1,2; the active input order is 0,1,2. -/
def capRelation (s t : Build) : Bool :=
  match t.active with
  | [(v,0),(w,1),(z,2)] =>
    v == w && v == z && freshVertex s v && s.active.isEmpty && s.signs.isEmpty &&
    t.signs == [true,true,true] &&
    t.graph == ⟨s.graph.edges,s.graph.rotations ++ [(v,[vacant,vacant,vacant])],
      s.graph.nextEdge,s.graph.circles⟩
  | _ => false

def relation (s t : Build) : Atom → Bool
  | .merge i => mergeRelation s t i
  | .split i => splitRelation s t i
  | .arc i => arcRelation s t i
  | .cap => capRelation s t

def startRelation (names : List String) (s : Build) : Prop :=
  names.Nodup ∧ s.graph = ⟨[],names.map (fun v => (v,[vacant])),0,0⟩ ∧
    s.active = names.map (fun v => (v,0)) ∧ s.signs = List.replicate names.length true

/-- A planar presentation records only literal local ribbon attachments,
not successful execution of the growth program. -/
inductive Presented (names : List String) : Build → Prop
  | start (s) : startRelation names s → Presented names s
  | step (s t a) : Presented names s → relation s t a = true → Presented names t

def runAtom (s : Build) : Atom → Option Build
  | .merge i => Atlas.merge s i
  | .split i => Atlas.split s i
  | .arc i => Atlas.arc s i
  | .cap =>
    if s.active != [] || s.signs != [] then none else
      let (v,s) := vertex s
      some {s with active := [(v,0),(v,1),(v,2)],signs := [true,true,true]}

def expandGrowth : Step → List Atom
  | (.y,i) => [.merge i]
  | (.h,i) => [.split (i+1),.merge i]
  | (.cup,i) => [.arc i]
  | _ => []

def expandSmall : Step → List Atom
  | (.y,i) => [.merge i]
  | (.lam,i) => [.split i]
  | _ => []

def sourceAtoms (growth small : List Step) : List Atom :=
  growth.flatMap expandGrowth ++
    if small == [(.lam,0),(.sigma,0)] then [.cap] else small.reverse.flatMap expandSmall

def atomDownSteps : Atom → List Step
  | .merge i => [(.y,i)]
  | .split i => [(.lam,i)]
  | .arc i => [(.cup,i)]
  | .cap => [(.sigma,0),(.lam,0)]

def downSteps (atoms : List Atom) := atoms.flatMap atomDownSteps

def atomUpSteps (a : Atom) : List Step := (atomDownSteps a).reverse

def AtomTyped (s t : Build) : Atom → Prop
  | .arc i => [(.cup,i)].foldlM descendSigns s.signs = some t.signs
  | a => (atomUpSteps a).foldlM ascendSigns t.signs = some s.signs

instance (s t : Build) (a : Atom) : Decidable (AtomTyped s t a) :=
  match a with
  | .arc _ => inferInstanceAs (Decidable (_ = _))
  | .merge _ => inferInstanceAs (Decidable (_ = _))
  | .split _ => inferInstanceAs (Decidable (_ = _))
  | .cap => inferInstanceAs (Decidable (_ = _))

def stepValid (s t : Build) (a : Atom) : Bool :=
  relation s t a && decide (AtomTyped s t a)

def trace : Build → List Atom → Option (List Build)
  | s,[] => some [s]
  | s,a::as => do
    let t ← runAtom s a
    let rest ← trace t as
    return s::rest

def traceValid : List Build → List Atom → Bool
  | [s],[] => true
  | s::t::ss,a::as => stepValid s t a && traceValid (t::ss) as
  | _,_ => false

theorem trace_presented (names : List String) (ss : List Build) (as : List Atom)
    (s : Build) (hs : ss.head? = some s) (hp : Presented names s)
    (hv : traceValid ss as = true) : Presented names (ss.getLast!) := by
  induction as generalizing ss s with
  | nil =>
    cases ss with
    | nil => simp at hs
    | cons t ts =>
      cases ts with
      | nil =>
        have ht : t=s := by simpa using hs
        simpa [ht] using hp
      | cons u us => simp [traceValid] at hv
  | cons a as ih =>
    cases ss with
    | nil => simp at hs
    | cons t ts =>
      cases ts with
      | nil => simp [traceValid] at hv
      | cons u us =>
        have ht : t=s := by simpa using hs
        subst t
        have hh : stepValid s u a=true ∧ traceValid (u::us) as=true := by
          simpa [traceValid] using hv
        have hr : relation s u a=true := by simpa [stepValid] using (show relation s u a=true ∧ decide (AtomTyped s u a)=true from by simpa [stepValid] using hh.1).1
        have hi := ih (u::us) u rfl (.step _ _ _ hp hr) hh.2
        simpa using hi

def outputNames (n : Nat) : List String := (List.range n).map (fun i => s!"b{i+1}")
def terminalAtoms (j : Nat) :=
  let (gs,sm) := (correctionSteps ++ hSteps)[j]!
  sourceAtoms gs sm
def terminalTrace (j : Nat) : List Build :=
  (trace (start (outputNames 9)) (terminalAtoms j)).getD []
def rootNames : List String := ["o0","o1","o2"] ++ outputNames 9
def rootAtoms := blockSteps.flatMap expandGrowth
def rootTrace : List Build := (trace (start rootNames) rootAtoms).getD []
def prefixAtoms := shortPrefixSteps.flatMap expandGrowth
def prefixTrace : List Build :=
  (trace (start (outputNames 6)) prefixAtoms).getD []
def tailAtoms := tailSteps.flatMap expandGrowth
def tailTrace : List Build := (trace (start (outputNames 9)) tailAtoms).getD []

theorem all_terminal_trace_checks : ∀ j : Fin 19,
    traceValid (terminalTrace j.val) (terminalAtoms j.val)=true ∧
    (terminalTrace j.val).head?=some (start (outputNames 9)) := by native_decide

theorem other_trace_checks :
    traceValid rootTrace rootAtoms=true ∧ rootTrace.head?=some (start rootNames) ∧
    traceValid prefixTrace prefixAtoms=true ∧ prefixTrace.head?=some (start (outputNames 6)) ∧
    traceValid tailTrace tailAtoms=true ∧ tailTrace.head?=some (start (outputNames 9)) := by
  native_decide

theorem start_presented (names : List String) (hn : names.Nodup) : Presented names (start names) :=
  .start _ ⟨hn,rfl,rfl,rfl⟩

theorem terminal_presented (j : Fin 19) :
    Presented (outputNames 9) (terminalTrace j.val).getLast! :=
  trace_presented _ _ _ _ (all_terminal_trace_checks j).2
    (start_presented _ (by decide)) (all_terminal_trace_checks j).1

theorem root_presented : Presented rootNames rootTrace.getLast! :=
  trace_presented _ _ _ _ other_trace_checks.2.1
    (start_presented _ (by decide)) other_trace_checks.1

theorem prefix_presented : Presented (outputNames 6) prefixTrace.getLast! :=
  trace_presented _ _ _ _ other_trace_checks.2.2.2.1
    (start_presented _ (by decide)) other_trace_checks.2.2.1

theorem tail_presented : Presented (outputNames 9) tailTrace.getLast! :=
  trace_presented _ _ _ _ other_trace_checks.2.2.2.2.2
    (start_presented _ (by decide)) other_trace_checks.2.2.2.2.1

/-- A typed elementary presentation.  It carries both the declarative
local-incidence certificate and the independently checked signed typing. -/
inductive Path : Build → Build → Type
  | refl (s) : Path s s
  | step {s u t} (a : Atom) (hr : relation s u a=true)
      (ht : AtomTyped s u a) (rest : Path u t) : Path s t

def atomCircuit (s t : Build) (a : Atom) (h : AtomTyped s t a) : Bar.Circuit t.signs s.signs :=
  match a with
  | .arc i => .down _ _ [(.cup,i)] h
  | .merge i => .up _ _ [(.y,i)] h
  | .split i => .up _ _ [(.lam,i)] h
  | .cap => .up _ _ [(.lam,0),(.sigma,0)] h

def Path.circuit {s t : Build} : Path s t → Bar.Circuit t.signs s.signs
  | .refl s => .identity s.signs
  | .step a _ ht rest => .compose rest.circuit (atomCircuit _ _ a ht)

def pathOfTrace : (as : List Atom) → (ss : List Build) → (s : Build) →
    ss.head?=some s → traceValid ss as=true → Path s ss.getLast!
  | [],[],_,hs,_ => by simp at hs
  | [],[t],s,hs,_ => by
      have ht : t=s := by simpa using hs
      subst t
      exact .refl s
  | [],_::_::_,_,_,hv => by simp [traceValid] at hv
  | _::_,[],_,hs,_ => by simp at hs
  | _::_,[_],_,_,hv => by simp [traceValid] at hv
  | a::as,t::u::us,s,hs,hv => by
      have ht : t=s := by simpa using hs
      subst t
      have hh : (relation s u a=true ∧ AtomTyped s u a) ∧ traceValid (u::us) as=true := by
        simpa [traceValid,stepValid] using hv
      exact .step a hh.1.1 hh.1.2 (pathOfTrace as (u::us) u rfl hh.2)

def terminalPath (j : Fin 19) := pathOfTrace (terminalAtoms j.val) (terminalTrace j.val)
  (start (outputNames 9)) (all_terminal_trace_checks j).2 (all_terminal_trace_checks j).1

def rootPath := pathOfTrace rootAtoms rootTrace (start rootNames)
  other_trace_checks.2.1 other_trace_checks.1

def prefixPath := pathOfTrace prefixAtoms prefixTrace (start (outputNames 6))
  other_trace_checks.2.2.2.1 other_trace_checks.2.2.1

def tailPath := pathOfTrace tailAtoms tailTrace (start (outputNames 9))
  other_trace_checks.2.2.2.2.2 other_trace_checks.2.2.2.2.1

theorem source_input_signs :
    (∀ j : Fin 19, (terminalTrace j.val).getLast!.signs=Bar.positive 3) ∧
    rootTrace.getLast!.signs=Bar.positive 3 ∧
    prefixTrace.getLast!.signs=Bar.positive 3 ∧
    tailTrace.getLast!.signs=[] := by native_decide

def terminalCircuit (j : Fin 19) : Bar.Circuit (Bar.positive 3) (Bar.positive 9) :=
  (terminalPath j).circuit.cast (source_input_signs.1 j) rfl

def rootCircuit : Bar.Circuit (Bar.positive 3) (Bar.positive 12) :=
  rootPath.circuit.cast source_input_signs.2.1 rfl

def prefixCircuit : Bar.Circuit (Bar.positive 3) (Bar.positive 6) :=
  prefixPath.circuit.cast source_input_signs.2.2.1 rfl

def tailCircuit : Bar.Circuit [] (Bar.positive 9) :=
  tailPath.circuit.cast source_input_signs.2.2.2 rfl

theorem terminal_tensor_checks : ∀ j : Fin 19, ∀ i : Fin 27,
    sameEntries (Bar.evalSparse (terminalCircuit j) (triple i.val))
      (summand (correctionSteps ++ hSteps)[j.val]! i.val) = true := by native_decide

theorem other_tensor_checks :
    (∀ i : Fin 27, sameEntries (Bar.evalSparse rootCircuit (triple i.val)) (rawB i.val)=true) ∧
    (∀ i : Fin 27, sameEntries (Bar.evalSparse prefixCircuit (triple i.val)) (shortPrefix i.val)=true) ∧
    sameEntries (Bar.evalSparse tailCircuit []) rawQ=true := by native_decide

theorem terminal_tensor (j : Fin 19) (i : Fin 27) (w : Word) :
    (Bar.evalSparse (terminalCircuit j) (triple i)).getD w [] =
      (summand (correctionSteps ++ hSteps)[j.val]! i).getD w [] :=
  sameEntries_getD _ _ (terminal_tensor_checks j i) w

theorem root_tensor (i : Fin 27) (w : Word) :
    (Bar.evalSparse rootCircuit (triple i)).getD w []=(rawB i).getD w [] :=
  sameEntries_getD _ _ (other_tensor_checks.1 i) w

theorem prefix_tensor (i : Fin 27) (w : Word) :
    (Bar.evalSparse prefixCircuit (triple i)).getD w []=(shortPrefix i).getD w [] :=
  sameEntries_getD _ _ (other_tensor_checks.2.1 i) w

theorem tail_tensor (w : Word) : (Bar.evalSparse tailCircuit []).getD w []=rawQ.getD w [] :=
  sameEntries_getD _ _ other_tensor_checks.2.2 w

end WebMu.Revised.AtlasSurgery
