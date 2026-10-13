import WebMu.Revised.AtlasCompletion
import WebMu.Revised.CircuitRealization

/-! From certified elementary ribbon attachments to the tensor realization.

The reference fields below are the spider functor's identity-wire,
single-vertex/cup, and local spider-relation laws.  They contain no call to
the graph compiler, evalSparse, expand, or a list of growth operations.
The actual finite growth programs are connected to this interface by the
proved declarative surgery certificates in AtlasSurgery and AtlasCompletion.
The tensor coordinate realization of their typed circuits is the structural
theorem AtomicCoordinates.circuit_matrix, not an assumption.
-/
namespace WebMu.Revised.AtlasRealization
open Atlas AtlasSurgery Bar Algebra Laurent
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def castSpace (R : BarReferences) {s t : Signs} (h : s=t) (x : R.Space s) : R.Space t := h ▸ x

theorem interpret_cast (R : BarReferences) {s t s' t' : Signs}
    (f : Circuit s t) (hs : s=s') (ht : t=t') (x : R.Space s') :
    R.interpret (f.cast hs ht) x =
      castSpace R ht (R.interpret f (castSpace R hs.symm x)) := by
  cases hs
  cases ht
  rfl

/-- A well-formed diagram may be certified by local presentation and literal
identity-edge completion, then by trivalent contractions at the declared
ordered boundary.  This is a proof relation, not a growth algorithm. -/
inductive Diagram : Graph → List String → List String → Signs → Signs → Prop
  | open {g : Graph} (admissible : OpenAdmissible g) :
      Diagram g inputNames (outputNames 9) (positive 3) (positive 9)
  | completion (names ins : List String) (s : Build) (g : Graph)
      (presented : Presented names s) (completed : completionRelation s g ins=true) :
      Diagram g ins names s.signs (positive names.length)
  | capTop {g h : Graph} {ins outs : List String} {s r : Signs}
      (a b c v : String) (old : Diagram g ins (a::b::c::outs) s (positive 3++r))
      (closed : trivalentClosureRelation g h [a,b,c] v=true) :
      Diagram h ins outs s r

/-- The usual oriented spider functor, formulated only on literal elementary
port attachments and graph operations.  The cap constructor is the one
trivalent cap λ followed by its evaluation edge; H is NOT a reference input.
All signs, input positions and cyclic ports are supplied by the checked
relations. -/
structure RibbonFunctorReferences (R : BarReferences) where
  port : (names : List String) → (s : Build) →
    R.Space s.signs → R.Space (positive names.length)
  graph : (ins outs : List String) → (s t : Signs) → Graph → R.Space s → R.Space t
  graph_intertwiner : ∀ ins outs s t g, Diagram g ins outs s t →
    R.IsIntertwiner (graph ins outs s t g)
  identity : ∀ names (hn : names.Nodup) x, port names (start names) x=x
  attachment : ∀ names s t a (hr : relation s t a=true) (ht : AtomTyped s t a),
    Presented names s → ∀ x,
    port names t x = port names s (R.interpret (atomCircuit s t a ht) x)
  completion : ∀ names ins s g, Presented names s → completionRelation s g ins=true →
    ∀ x, graph ins names s.signs (positive names.length) g x = port names s x
  capTop : ∀ {g h ins outs s r} (a b c v : String),
    Diagram g ins (a::b::c::outs) s (positive 3++r) →
    trivalentClosureRelation g h [a,b,c] v=true → ∀ x,
    graph ins outs s r h x =
      R.interpret (capPrimitive r) (graph ins (a::b::c::outs) s (positive 3++r) g x)
  /-- The three ordinary local relations on the fixed 9-output/3-input boundary. -/
  open_isotopy : ∀ g h iso, OpenAdmissible g → OpenAdmissible h →
    bijectionValid g h iso=true → ∀ x,
    graph inputNames (outputNames 9) (positive 3) (positive 9) g x =
      graph inputNames (outputNames 9) (positive 3) (positive 9) h x
  open_square : ∀ g f h k, OpenAdmissible g → OpenAdmissible h → OpenAdmissible k →
    f.vertices.length=4 → resolvedTo g f [(0,1),(2,3)] h=true →
    resolvedTo g f [(1,2),(3,0)] k=true → ∀ x,
    graph inputNames (outputNames 9) (positive 3) (positive 9) g x =
      R.add _ (graph inputNames (outputNames 9) (positive 3) (positive 9) h x)
        (graph inputNames (outputNames 9) (positive 3) (positive 9) k x)
  open_digon : ∀ g f h, OpenAdmissible g → OpenAdmissible h →
    f.vertices.length=2 → resolvedTo g f [(0,1)] h=true → ∀ x,
    graph inputNames (outputNames 9) (positive 3) (positive 9) g x =
      R.scaleD _ (graph inputNames (outputNames 9) (positive 3) (positive 9) h x)

theorem path_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (names : List String) {s t : Build} (p : Path s t) (hp : Presented names s)
    (x : R.Space t.signs) :
    F.port names t x = F.port names s (R.interpret p.circuit x) := by
  induction p with
  | refl => rfl
  | @step s u t a hr ht rest ih =>
    rw [ih (.step s u a hp hr),F.attachment names s u a hr ht hp]
    rfl

theorem start_path_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (names : List String) (hn : names.Nodup) {t : Build} (p : Path (start names) t)
    (x : R.Space t.signs) : F.port names t x=R.interpret p.circuit x := by
  rw [path_interpretation R F names p (start_presented names hn),F.identity names hn]

theorem graph_input_cast (R : BarReferences) (F : RibbonFunctorReferences R)
    (ins outs : List String) {s s' t : Signs} (h : s=s') (g : Graph) (x : R.Space s') :
    F.graph ins outs s' t g x=F.graph ins outs s t g (castSpace R h.symm x) := by
  cases h
  rfl

theorem completed_path_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (names ins : List String) (hn : names.Nodup) {u : Build} (g : Graph)
    (p : Path (start names) u) (hp : Presented names u)
    (hc : completionRelation u g ins=true) {s : Signs} (hs : u.signs=s)
    (x : R.Space s) :
    F.graph ins names s (positive names.length) g x =
      R.interpret (p.circuit.cast hs rfl) x := by
  rw [graph_input_cast R F _ _ hs, F.completion names ins u g hp hc,
    start_path_interpretation R F names hn p]
  exact (interpret_cast R p.circuit hs rfl x).symm

theorem terminal_graph_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (j : Fin 19) (x : R.Space (positive 3)) :
    F.graph inputNames (outputNames 9) (positive 3) (positive 9) (constructedSummand j.val) x =
      R.interpret (terminalCircuit j) x := by
  exact completed_path_interpretation R F (outputNames 9) inputNames (by decide)
    (constructedSummand j.val) (terminalPath j) (terminal_presented j)
    (terminal_completion_checks j) (source_input_signs.1 j) x

theorem uncapped_root_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (x : R.Space (positive 3)) :
    F.graph inputNames rootNames (positive 3) (positive 12) uncappedRoot x =
      R.interpret rootCircuit x := by
  exact completed_path_interpretation R F rootNames inputNames (by decide)
    uncappedRoot rootPath root_presented root_completion_check source_input_signs.2.1 x

theorem diagram_input_cast {g : Graph} {ins outs : List String} {s s' t : Signs}
    (h : s=s') (d : Diagram g ins outs s t) : Diagram g ins outs s' t := h ▸ d

theorem uncapped_root_diagram :
    Diagram uncappedRoot inputNames rootNames (positive 3) (positive 12) := by
  exact diagram_input_cast source_input_signs.2.1
    (Diagram.completion rootNames inputNames rootTrace.getLast! uncappedRoot
      root_presented root_completion_check)

theorem capped_root_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (x : R.Space (positive 3)) :
    F.graph inputNames (outputNames 9) (positive 3) (positive 9) constructedRoot x =
      R.interpret cappedRootCircuit x := by
  have hc := F.capTop (g:=uncappedRoot) (h:=constructedRoot) (ins:=inputNames)
    (outs:=outputNames 9) (s:=positive 3) (r:=positive 9)
    "o0" "o1" "o2" "eta" uncapped_root_diagram root_cap_check x
  change _ = R.interpret (capPrimitive (positive 9))
    (F.graph inputNames rootNames (positive 3) (positive 12) uncappedRoot x) at hc
  rw [hc,uncapped_root_interpretation]
  rfl

def coordinateEvaluation (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (i w : Word) (g : Graph) : Poly :=
  A.coord (positive 9)
    (F.graph inputNames (outputNames 9) (positive 3) (positive 9) g
      (A.basis (positive 3) i)) w

/-- The evaluator used by the atlas is now DEFINED to be the actual matrix
coordinate of the graph's spider morphism, in the fixed ordered basis. -/
def coordinateSpider (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (i w : Word) : OpenSpiderReferences where
  eval := coordinateEvaluation R A F i w
  isotopy g h iso hg hh hi := by
    unfold coordinateEvaluation
    rw [F.open_isotopy g h iso hg hh hi]
  square g f h k hg hh hk hn ha hb := by
    unfold coordinateEvaluation
    rw [F.open_square g f h k hg hh hk hn ha hb,A.coord_add]
  digon g f h hg hh hn hd := by
    unfold coordinateEvaluation
    rw [F.open_digon g f h hg hh hn hd,A.coord_scaleD,poly_mul_comm]

theorem root_coordinates (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (i : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    (coordinateSpider R A F (triple i) w).eval constructedRoot =
      ofList ((cap (rawB i)).getD w []) := by
  change coordinateEvaluation R A F (triple i) w constructedRoot = _
  unfold coordinateEvaluation
  rw [capped_root_interpretation]
  rw [(A.circuit_matrix cappedRootCircuit (triple i) (Bar.triple_valid i)).2 w hw,
    capped_root_tensor]

theorem terminal_coordinates (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (j : Fin 19) (i : Fin 27)
    (w : Word) (hw : validWord 9 w=true) :
    (coordinateSpider R A F (triple i) w).eval (constructedSummand j.val) =
      ofList ((summand (correctionSteps ++ hSteps)[j.val]! i).getD w []) := by
  change coordinateEvaluation R A F (triple i) w (constructedSummand j.val) = _
  unfold coordinateEvaluation
  rw [terminal_graph_interpretation]
  rw [(A.circuit_matrix (terminalCircuit j) (triple i) (Bar.triple_valid i)).2 w hw,
    terminal_tensor]

theorem sumTensor_coordinates (xs : List Tensor) (w : Word) :
    ofList ((sumTensor xs).getD w [])=total xs (fun x => ofList (x.getD w [])) :=
  sumMap_poly xs w

theorem rawD_coordinates (i : Fin 27) (w : Word) :
    ofList ((rawD i).getD w [])=total (List.range 8)
      (fun j => ofList ((summand (correctionSteps ++ hSteps)[j]! i).getD w [])) := by
  rw [rawD,sumTensor_coordinates,total_map]
  have h : correctionSteps=(List.range 8).map (fun j => (correctionSteps ++ hSteps)[j]!) := by decide
  exact (congrArg (fun xs => total xs (fun s => ofList ((summand s i).getD w []))) h).trans
    (total_map _ _ _)

theorem rawH_coordinates (i : Fin 27) (w : Word) :
    ofList ((rawH i).getD w [])=total (List.range' 8 11)
      (fun j => ofList ((summand (correctionSteps ++ hSteps)[j]! i).getD w [])) := by
  rw [rawH,sumTensor_coordinates,total_map]
  have h : hSteps=(List.range' 8 11).map (fun j => (correctionSteps ++ hSteps)[j]!) := by decide
  exact (congrArg (fun xs => total xs (fun s => ofList ((summand s i).getD w []))) h).trans
    (total_map _ _ _)

/-- The local graph reduction proves the actual tensor identity, with the
custom source compiler justified by its entire elementary presentation.
The separately computed cap_B/cap_B_check is not used by this proof. -/
theorem open_tensor_identity (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (i : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    ofList ((cap (rawB i)).getD w []) =
      ofList d * ofList ((rawD i).getD w []) + ofList ((rawH i).getD w []) := by
  have h := open_growth_identity (coordinateSpider R A F (triple i) w)
  rw [root_coordinates R A F i w hw] at h
  rw [rawD_coordinates,rawH_coordinates]
  have hD : total (List.range 8)
      (fun j => (coordinateSpider R A F (triple i) w).eval (constructedSummand j)) =
      total (List.range 8)
        (fun j => ofList ((summand (correctionSteps ++ hSteps)[j]! i).getD w [])) := by
    apply total_congr_mem
    intro j hj
    exact terminal_coordinates R A F ⟨j,by have := List.mem_range.mp hj; omega⟩ i w hw
  have hH : total (List.range' 8 11)
      (fun j => (coordinateSpider R A F (triple i) w).eval (constructedSummand j)) =
      total (List.range' 8 11)
        (fun j => ofList ((summand (correctionSteps ++ hSteps)[j]! i).getD w [])) := by
    apply total_congr_mem
    intro j hj
    exact terminal_coordinates R A F ⟨j,by have := List.mem_range'.mp hj; omega⟩ i w hw
  rw [hD,hH] at h
  exact h

#print axioms open_tensor_identity
end WebMu.Revised.AtlasRealization
