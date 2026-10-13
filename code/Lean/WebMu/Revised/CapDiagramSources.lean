import WebMu.Revised.CapDiagramData

/-! Primitive ribbon presentations of C, Q, the tripod products, and the
six-boundary tree. These retain the original ordered tensor factors.
Every attachment is checked against the declarative single-vertex and
single-arc relations; no source compiler is assumed. -/
namespace WebMu.Revised.CapDiagram
open Atlas AtlasSurgery AtlasRealization Bar
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sourceWidth : Fin 5 → Nat
  | 0 => 12 | 1 => 9 | 2 => 9 | _ => 6

def sourceNames : Fin 5 → List String
  | 0 => ["o0","o1","o2"] ++ outputNames 9
  | 1 => ["o0","o1","o2"] ++ outputNames 6
  | 2 => outputNames 9
  | _ => outputNames 6

def sourceAtoms : Fin 5 → List Atom
  | 0 => cSteps.flatMap expandGrowth ++ [.arc 0,.arc 0,.arc 0,.arc 0]
  | 1 => tailSteps.flatMap expandGrowth
  | 2 => [.merge 0,.arc 0,.merge 0,.arc 0,.merge 0,.arc 0]
  | 3 => [.merge 0,.arc 0,.merge 0,.arc 0]
  | _ => [.merge 1,.merge 2,.merge 1,.merge 0,.arc 0]

def sourceTrace (j : Fin 5) := (trace (start (sourceNames j)) (sourceAtoms j)).getD []
def sourceGraph (j : Fin 5) := (sourceTrace j).getLast!.graph

theorem source_certificates : ∀ j : Fin 5,
    traceValid (sourceTrace j) (sourceAtoms j)=true ∧
    (sourceTrace j).head?=some (start (sourceNames j)) ∧
    (sourceTrace j).getLast!.signs=[] ∧
    completionRelation (sourceTrace j).getLast! (sourceGraph j) []=true ∧
    (sourceNames j).Nodup ∧ (sourceNames j).length=sourceWidth j := by native_decide

def sourcePath (j : Fin 5) := pathOfTrace (sourceAtoms j) (sourceTrace j)
  (start (sourceNames j)) (source_certificates j).2.1 (source_certificates j).1

theorem source_presented (j : Fin 5) : Presented (sourceNames j) (sourceTrace j).getLast! :=
  trace_presented _ _ _ _ (source_certificates j).2.1
    (start_presented _ (source_certificates j).2.2.2.2.1) (source_certificates j).1

def sourceCircuit (j : Fin 5) : Circuit [] (positive (sourceWidth j)) :=
  (sourcePath j).circuit.cast (source_certificates j).2.2.1
    (congrArg positive (source_certificates j).2.2.2.2.2)

theorem source_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (j : Fin 5) (x : R.Space []) :
    F.graph [] (sourceNames j) [] (positive (sourceWidth j)) (sourceGraph j) x =
      R.interpret (sourceCircuit j) x := by
  have h := completed_path_interpretation R F (sourceNames j) []
    (source_certificates j).2.2.2.2.1 (sourceGraph j) (sourcePath j) (source_presented j)
    (source_certificates j).2.2.2.1 (source_certificates j).2.2.1 x
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> exact h

theorem source_diagram (j : Fin 5) :
    Diagram (sourceGraph j) [] (sourceNames j) [] (positive (sourceWidth j)) := by
  have h := diagram_input_cast (source_certificates j).2.2.1
    (Diagram.completion (sourceNames j) [] (sourceTrace j).getLast! (sourceGraph j)
      (source_presented j) (source_certificates j).2.2.2.1)
  simpa only [(source_certificates j).2.2.2.2.2] using h

theorem root_closures :
    trivalentClosureRelation (sourceGraph 0) cRoot ["o0","o1","o2"] "eta"=true ∧
    trivalentClosureRelation (sourceGraph 1) qRoot ["o0","o1","o2"] "eta"=true := by
  native_decide

def cCappedCircuit : Circuit [] (positive 9) :=
  .compose (sourceCircuit 0) (capPrimitive (positive 9))
def qCappedCircuit : Circuit [] (positive 6) :=
  .compose (sourceCircuit 1) (capPrimitive (positive 6))

theorem c_root_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (x : R.Space []) :
    F.graph [] (outputNames 9) [] (positive 9) cRoot x =
      R.interpret cCappedCircuit x := by
  have h := F.capTop (g:=sourceGraph 0) (h:=cRoot) (ins:=[]) (outs:=outputNames 9)
    (s:=[]) (r:=positive 9) "o0" "o1" "o2" "eta" (source_diagram 0) root_closures.1 x
  change _ = R.interpret (capPrimitive (positive 9))
    (F.graph [] (sourceNames 0) [] (positive (sourceWidth 0)) (sourceGraph 0) x) at h
  rw [h,source_interpretation]
  rfl

theorem q_root_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (x : R.Space []) :
    F.graph [] (outputNames 6) [] (positive 6) qRoot x =
      R.interpret qCappedCircuit x := by
  have h := F.capTop (g:=sourceGraph 1) (h:=qRoot) (ins:=[]) (outs:=outputNames 6)
    (s:=[]) (r:=positive 6) "o0" "o1" "o2" "eta" (source_diagram 1) root_closures.2 x
  change _ = R.interpret (capPrimitive (positive 6))
    (F.graph [] (sourceNames 1) [] (positive (sourceWidth 1)) (sourceGraph 1) x) at h
  rw [h,source_interpretation]
  rfl

/-- Only source-to-circuit bindings are computed here. Neither cap identity
nor a scaled/summed target appears in these checks. -/
theorem source_tensor_checks :
    sameEntries (evalSparse (sourceCircuit 0) []) rawC=true ∧
    sameEntries (evalSparse (sourceCircuit 1) []) rawQ=true ∧
    sameEntries (evalSparse (sourceCircuit 2) []) tau3=true ∧
    sameEntries (evalSparse (sourceCircuit 3) []) tau2=true ∧
    sameEntries (evalSparse (sourceCircuit 4) []) tailTree=true ∧
    sameEntries (evalSparse cCappedCircuit []) (cap rawC)=true ∧
    sameEntries (evalSparse qCappedCircuit []) (cap rawQ)=true := by native_decide

end WebMu.Revised.CapDiagram
