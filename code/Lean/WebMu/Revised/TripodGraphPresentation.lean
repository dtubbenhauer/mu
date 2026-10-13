import WebMu.Revised.TripodGraphs
import WebMu.Revised.AtlasRealization

/-! Elementary presentations of all original and shortened two-block diagrams.
These finite certificates inspect every local incidence and signed port, not
merely equality of the output of a graph-growth algorithm. -/
namespace WebMu.Revised.TripodGraphPresentation
open Atlas AtlasSurgery AtlasRealization TripodGraphs Bar
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev Source := Bool × Fin 95

def width (p : Source) : Nat := if p.1 then 33 else 30

def steps (p : Source) : List Step :=
  if p.1 then tripodData[p.2.val]!.paddedSteps else shortenedSteps[p.2.val]!

def graph (p : Source) : Graph := (growthGraph (width p) (steps p)).getD default

def atoms (p : Source) : List Atom := (steps p).flatMap expandGrowth

def sourceTrace (p : Source) : List Build :=
  (trace (start (outputNames (width p))) (atoms p)).getD []

theorem source_checks : ∀ p : Source,
    traceValid (sourceTrace p) (atoms p)=true ∧
    (sourceTrace p).head?=some (start (outputNames (width p))) ∧
    (sourceTrace p).getLast!.signs=[] ∧
    completionRelation (sourceTrace p).getLast! (graph p) []=true := by
  intro ⟨b,i⟩
  cases b <;> revert i <;> native_decide

theorem names_nodup : ∀ p : Source, (outputNames (width p)).Nodup := by
  intro ⟨b,i⟩
  cases b <;> simp only [width, Bool.false_eq_true, if_false, if_true] <;> decide

def sourcePath (p : Source) : Path (start (outputNames (width p))) (sourceTrace p).getLast! :=
  pathOfTrace (atoms p) (sourceTrace p) _ (source_checks p).2.1 (source_checks p).1

theorem source_presented (p : Source) :
    Presented (outputNames (width p)) (sourceTrace p).getLast! :=
  trace_presented _ _ _ _ (source_checks p).2.1 (start_presented _ (names_nodup p))
    (source_checks p).1

def sourceCircuit (p : Source) : Circuit [] (positive (width p)) :=
  (sourcePath p).circuit.cast (source_checks p).2.2.1 (by simp [start,outputNames,positive])

theorem diagram_output_cast {g : Graph} {ins outs : List String} {s t t' : Signs}
    (h : t=t') (d : Diagram g ins outs s t) : Diagram g ins outs s t' := h ▸ d

theorem completed_path_output_cast (R : BarReferences) (F : RibbonFunctorReferences R)
    (names ins : List String) (hn : names.Nodup) {u : Build} (g : Graph)
    (p : Path (start names) u) (hp : Presented names u)
    (hc : completionRelation u g ins=true) {s t : Signs} (hs : u.signs=s)
    (ht : positive names.length=t) (x : R.Space s) :
    F.graph ins names s t g x = R.interpret (p.circuit.cast hs ht) x := by
  cases ht
  exact completed_path_interpretation R F names ins hn g p hp hc hs x

theorem source_diagram (p : Source) :
    Diagram (graph p) [] (outputNames (width p)) [] (positive (width p)) := by
  exact diagram_output_cast (by simp [start,outputNames,positive])
    (diagram_input_cast (source_checks p).2.2.1
      (Diagram.completion _ _ _ _ (source_presented p) (source_checks p).2.2.2))

theorem source_graph_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (p : Source) (x : R.Space []) :
    F.graph [] (outputNames (width p)) [] (positive (width p)) (graph p) x =
      R.interpret (sourceCircuit p) x := by
  exact completed_path_output_cast R F (outputNames (width p)) [] (names_nodup p)
    (graph p) (sourcePath p) (source_presented p) (source_checks p).2.2.2
    (source_checks p).2.2.1 (by simp [start,outputNames,positive]) x

end WebMu.Revised.TripodGraphPresentation
