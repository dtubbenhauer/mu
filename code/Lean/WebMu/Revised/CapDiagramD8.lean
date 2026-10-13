import WebMu.Revised.CapDiagramCore

/-! The final correction D8 is the disjoint product of the input cap and
three output tripods. Each factor is removed with fixed ordered boundary. -/
namespace WebMu.Revised.CapDiagram
open Atlas AtlasSurgery AtlasRealization Bar TripodGraphRealization Algebra Laurent
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def d8Width (j : Fin 4) : Nat := [9,6,3,0][j.val]!
def d8Atoms (j : Fin 4) : List Atom :=
  (List.replicate (d8Width j/3) [.merge 0,.arc 0]).flatten ++ [.cap]
def d8Trace (j : Fin 4) := (trace (start (outputNames (d8Width j))) (d8Atoms j)).getD []
def d8Graph (j : Fin 4) : Graph := (attachInputs (d8Trace j).getLast!).getD default

theorem d8_source_checks : ∀ j : Fin 4,
    traceValid (d8Trace j) (d8Atoms j)=true ∧
    (d8Trace j).head?=some (start (outputNames (d8Width j))) ∧
    (d8Trace j).getLast!.signs=positive 3 ∧
    completionRelation (d8Trace j).getLast! (d8Graph j) inputNames=true := by native_decide

def d8Path (j : Fin 4) := pathOfTrace (d8Atoms j) (d8Trace j)
  (start (outputNames (d8Width j))) (d8_source_checks j).2.1 (d8_source_checks j).1

theorem d8_presented (j : Fin 4) : Presented (outputNames (d8Width j)) (d8Trace j).getLast! :=
  trace_presented _ _ _ _ (d8_source_checks j).2.1
    (start_presented _ (by revert j; decide)) (d8_source_checks j).1

def d8Circuit (j : Fin 4) : Circuit (positive 3) (positive (d8Width j)) :=
  (d8Path j).circuit.cast (d8_source_checks j).2.2.1
    (by simp [start,outputNames,positive])

theorem d8_diagram (j : Fin 4) :
    Diagram (d8Graph j) inputNames (outputNames (d8Width j)) (positive 3) (positive (d8Width j)) := by
  have h := diagram_input_cast (d8_source_checks j).2.2.1
    (Diagram.completion (outputNames (d8Width j)) inputNames (d8Trace j).getLast! (d8Graph j)
      (d8_presented j) (d8_source_checks j).2.2.2)
  simpa only [outputNames,List.length_map,List.length_range] using h

theorem d8_graph_interpretation (R : BarReferences) (F : RibbonFunctorReferences R)
    (j : Fin 4) (x : R.Space (positive 3)) :
    F.graph inputNames (outputNames (d8Width j)) (positive 3) (positive (d8Width j)) (d8Graph j) x =
      R.interpret (d8Circuit j) x := by
  have h := completed_path_interpretation R F (outputNames (d8Width j)) inputNames
    (by revert j; decide) (d8Graph j) (d8Path j) (d8_presented j)
    (d8_source_checks j).2.2.2 (d8_source_checks j).2.2.1 x
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hj with rfl | rfl | rfl | rfl <;> exact h

def d8Witness (j : Fin 3) : RemovalWitness :=
  ⟨d8Remainders[j.val]!,d8Centers[j.val]!,d8Edges[j.val]!,d8Rotations[j.val]!,d8Isos[j.val]!⟩

theorem d8_removals : ∀ j : Fin 3,
    removalRelation (d8Width ⟨j.val+1,by omega⟩) 0
      (d8Graph j.castSucc) (d8Graph ⟨j.val+1,by omega⟩) (d8Witness j)=true ∧
    inputNames.all (fun v => lookup (d8Witness j).iso.vertices v==some v)=true := by native_decide

def appendTripod (k : Nat) : Circuit (positive k) (positive k++positive 3) :=
  (Circuit.tensor (.identity (positive k)) tripodCircuit).cast (by simp) rfl

theorem d8_graph_steps (R : BarReferences) (F : RibbonFunctorReferences R)
    (G : BoundaryTripodReferences R F) (x : R.Space (positive 3)) :
    F.graph inputNames (outputNames 9) (positive 3) (positive 9) (d8Graph 0) x =
      R.interpret (appendTripod 6)
        (R.interpret (appendTripod 3)
          (R.interpret (appendTripod 0)
            (F.graph inputNames [] (positive 3) [] (d8Graph 3) x))) := by
  have h0 := G.disjoint_tripod 6 inputNames (positive 3) (d8Graph 0) (d8Graph 1)
    (d8Witness 0) (d8_diagram 0) (d8_diagram 1) (d8_removals 0).1 (d8_removals 0).2 x
  have h1 := G.disjoint_tripod 3 inputNames (positive 3) (d8Graph 1) (d8Graph 2)
    (d8Witness 1) (d8_diagram 1) (d8_diagram 2) (d8_removals 1).1 (d8_removals 1).2 x
  have h2 := G.disjoint_tripod 0 inputNames (positive 3) (d8Graph 2) (d8Graph 3)
    (d8Witness 2) (d8_diagram 2) (d8_diagram 3) (d8_removals 2).1 (d8_removals 2).2 x
  change _ = R.interpret (appendTripod 6) _ at h0
  change _ = R.interpret (appendTripod 3) _ at h1
  change _ = R.interpret (appendTripod 0) _ at h2
  exact h0.trans (congrArg (R.interpret (appendTripod 6))
    (h1.trans (congrArg (R.interpret (appendTripod 3)) h2)))

def d8TripodCircuit : Circuit [] (positive 9) :=
  .compose (appendTripod 0) (.compose (appendTripod 3) (appendTripod 6))

def d8FactorCircuit : Circuit (positive 3) (positive 9) :=
  .compose (d8Circuit 3) d8TripodCircuit

theorem d8_root_source : d8Graph 0=constructedSummand 7 := by native_decide

/-- Actual tensor-map factorization obtained by deleting three literal
disjoint components. The remaining source is the elementary input cap. -/
theorem D8_circuit_factorization (R : BarReferences) (F : RibbonFunctorReferences R)
    (G : BoundaryTripodReferences R F) (x : R.Space (positive 3)) :
    R.interpret (terminalCircuit 7) x=R.interpret d8FactorCircuit x := by
  have h := d8_graph_steps R F G x
  rw [d8_root_source] at h
  have hs := terminal_graph_interpretation R F (7 : Fin 19) x
  have he := d8_graph_interpretation R F 3 x
  change F.graph inputNames [] (positive 3) [] (d8Graph 3) x=R.interpret (d8Circuit 3) x at he
  rw [he] at h
  exact hs.symm.trans h

/-- The remaining component is literally the elementary cap. -/
theorem d8_cap_primitive (R : BarReferences) (x : R.Space (positive 3)) :
    R.interpret (d8Circuit 3) x=R.interpret (capPrimitive []) x := by rfl

/-- Separate elementary-factor coordinate bindings: the cap has 27 inputs;
the disjoint triple-tripod has one scalar input. D8 is absent from them. -/
theorem d8_factor_checks :
    (∀ j : Fin 27, (evalSparse (d8Circuit 3) (triple j)).getD [] []=eta j) ∧
    sameEntries (evalSparse d8TripodCircuit []) tau3=true := by native_decide

theorem d8_factor_coordinate (R : BarReferences) (A : AtomicCoordinates R)
    (j : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    A.coord (positive 9) (R.interpret d8FactorCircuit (A.basis (positive 3) (triple j))) w =
      ofList (tau3.getD w [])*ofList (eta j) := by
  change A.coord (positive 9) (R.interpret d8TripodCircuit
    (R.interpret (d8Circuit 3) (A.basis (positive 3) (triple j)))) w=_
  rw [A.linear_basis_coordinates (R.interpret d8TripodCircuit)
    (circuit_intertwiner R d8TripodCircuit) (completeWords 0)
    (completeWords_nodup 0) (completeWords_mem 0) _ w hw]
  change A.coord (positive 9) (R.interpret d8TripodCircuit (A.basis [] [])) w *
    A.coord [] (R.interpret (d8Circuit 3) (A.basis (positive 3) (triple j))) [] + 0 = _
  have hc := (A.circuit_matrix (d8Circuit 3) (triple j) (Bar.triple_valid j)).2 [] (by decide)
  change A.coord [] (R.interpret (d8Circuit 3) (A.basis (positive 3) (triple j))) [] = _ at hc
  rw [(A.circuit_matrix d8TripodCircuit [] (by decide)).2 w hw,hc,
    d8_factor_checks.1 j,sameEntries_getD _ _ d8_factor_checks.2 w,poly_add_zero]

/-- D8=tau³ eta from three diagrammatic disjoint-component factorizations
and the ordinary scalar intermediate tensor coordinate law. -/
theorem D8_coordinate (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : BoundaryTripodReferences R F)
    (j : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    ofList ((summand correctionSteps[7]! j).getD w [])=
      ofList (tau3.getD w [])*ofList (eta j) := by
  have h := congrArg (fun x => A.coord (positive 9) x w)
    (D8_circuit_factorization R F G (A.basis (positive 3) (triple j)))
  dsimp only at h
  have hs := (A.circuit_matrix (terminalCircuit 7) (triple j) (Bar.triple_valid j)).2 w hw
  have ht := congrArg ofList (terminal_tensor (7 : Fin 19) j w)
  exact (hs.trans ht).symm.trans (h.trans (d8_factor_coordinate R A j w hw))

#print axioms D8_circuit_factorization
#print axioms D8_coordinate
end WebMu.Revised.CapDiagram
