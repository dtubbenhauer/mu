import WebMu.Revised.LocalRowRaw
import WebMu.Revised.CapDiagramD8

/-! Simplification of literal gauge multiplication using the actual diagram
reductions, followed by the two selected constant rows. -/
namespace WebMu.Revised.LocalDegreeProof
open Laurent Algebra Bar AtlasRealization CapDiagram SelectedRowDerivation
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def V (e : Int) : Poly := ofList (monomial e)
def minusOne : Poly := ofList (monomial 0 (-1))

theorem d_representation : d=[(-1,1),(1,1)] := by native_decide

theorem lower_algebra (p h z : Poly) :
    (ofList d*(p+z)+h)*V (-1)+(p+z)*minusOne+
      (ofList d*(ofList d*z))*(V (-2)*minusOne)+z*(ofList d*V (-1)) =
    p*V (-2)+h*V (-1)+z*(V (-4)*minusOne) := by
  induction p using Quotient.inductionOn with | _ p =>
  induction h using Quotient.inductionOn with | _ h =>
  induction z using Quotient.inductionOn with | _ z =>
  apply poly_ext
  intro n
  change coeff _ n=coeff _ n
  simp only [coeff_add]
  have h2 : mul (monomial (-2)) (monomial 0 (-1))=monomial (-2) (-1) := by native_decide
  have h4 : mul (monomial (-4)) (monomial 0 (-1))=monomial (-4) (-1) := by native_decide
  have hd : mul d (monomial (-1))=[(-2,1),(0,1)] := by native_decide
  rw [h2,h4,hd,Algebra.mul_comm (add (mul d (add p z)) h) (monomial (-1)),
    Algebra.mul_comm (add p z) (monomial 0 (-1)),
    Algebra.mul_comm (mul d (mul d z)) (monomial (-2) (-1)),
    Algebra.mul_comm z [(-2,1),(0,1)],
    Algebra.mul_comm p (monomial (-2)),Algebra.mul_comm h (monomial (-1)),
    Algebra.mul_comm z (monomial (-4) (-1))]
  simp [d_representation,monomial,mul,coeff,coeff_add,coeff_shiftScale,
    Int.sub_eq_add_neg,Int.add_assoc,Int.add_comm,Int.add_left_comm]
  <;> omega

theorem rawD_split (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (B : BoundaryTripodReferences R F)
    (j : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    ofList ((rawD j).getD w [])=
      ofList ((rawD₀ j).getD w [])+ofList (tau3.getD w [])*ofList (eta j) := by
  have hs : correctionSteps=correctionSteps.take 7++[correctionSteps[7]!] := by decide
  rw [rawD,sumTensor_coordinates,total_map,hs,Bar.total_append]
  simp only [total_cons,total_nil,poly_add_zero]
  rw [D8_coordinate R A F B j w hw]
  rw [rawD₀,sumTensor_coordinates,total_map]

def lowerExpression (j : Nat) (w : Word) : Laurent :=
  shiftScale (add (add (shiftScale ((rawD₀ j).getD w []) (-2) 1)
    (shiftScale ((rawH j).getD w []) (-1) 1))
    (neg (shiftScale (mul (tau3.getD w []) (eta j)) (-4) 1))) (-height j) 1

theorem lower_formula (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (B : BoundaryTripodReferences R F) (j : Fin 27) (w : Word) (hw : validWord 9 w=true) :
    ofList ((blockHat j).getD (27,encode w) [])=ofList (lowerExpression j w) := by
  rw [lower_raw_formula j w hw]
  apply shift_congr
  rw [lowerRaw,sumTensor_coordinates]
  simp only [total_cons,total_nil,poly_add_zero,scaleTensor_coordinate]
  rw [open_tensor_identity R A F j w hw,cap_C_diagrammatic R A F G w hw,rawD_split R A F B j w hw]
  simp only [ofList_add,ofList_neg_factor,ofList_mul,ofList_shift]
  have h := lower_algebra (ofList ((rawD₀ j).getD w []))
    (ofList ((rawH j).getD w [])) (ofList (tau3.getD w [])*ofList (eta j))
  simpa only [V,minusOne,poly_add_assoc,poly_mul_assoc,poly_mul_comm,poly_mul_left_comm] using h

theorem lower_scalar_algebra (u : Poly) :
    (ofList d*(ofList d*u))*V (-1)+u*(ofList d*minusOne)=u*ofList d*V (-2) := by
  induction u using Quotient.inductionOn with | _ u =>
  apply poly_ext
  intro n
  change coeff _ n=coeff _ n
  simp only [coeff_add]
  have hd : mul d (monomial 0 (-1))=[(-1,-1),(1,-1)] := by native_decide
  rw [hd,Algebra.mul_comm (mul d (mul d u)) (monomial (-1)),
    Algebra.mul_comm u [(-1,-1),(1,-1)],
    Algebra.mul_comm (mul u d) (monomial (-2))]
  have hc (k : Int) : coeff (mul u [(-1,1),(1,1)]) k=coeff (mul [(-1,1),(1,1)] u) k :=
    Algebra.mul_comm _ _ k
  simp [hc,d_representation,monomial,mul,coeff,coeff_add,coeff_shiftScale,
    Int.sub_eq_add_neg,Int.add_assoc,Int.add_comm,Int.add_left_comm]
  <;> omega

theorem lower_scalar_formula (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (w : Word) (hw : validWord 9 w=true) :
    ofList ((blockHat 27).getD (27,encode w) [])=
      ofList (shiftScale (mul (tau3.getD w []) d) (-2) 1) := by
  rw [lower_scalar_raw_formula w hw,lowerScalarRaw,sumTensor_coordinates]
  simp only [total_cons,total_nil,poly_add_zero,scaleTensor_coordinate]
  rw [cap_C_diagrammatic R A F G w hw]
  simp only [ofList_neg_factor,ofList_shift,ofList_mul]
  exact lower_scalar_algebra _

theorem tail_scalar_algebra (u h : Poly) :
    (ofList d*u+h)*V (-1)+u*minusOne=u*V (-2)+h*V (-1) := by
  induction u using Quotient.inductionOn with | _ u =>
  induction h using Quotient.inductionOn with | _ h =>
  apply poly_ext
  intro n
  change coeff _ n=coeff _ n
  simp only [coeff_add]
  rw [Algebra.mul_comm (add (mul d u) h) (monomial (-1)),
    Algebra.mul_comm u (monomial 0 (-1)),
    Algebra.mul_comm u (monomial (-2)),Algebra.mul_comm h (monomial (-1))]
  simp [d_representation,monomial,mul,coeff,coeff_add,coeff_shiftScale,
    Int.sub_eq_add_neg,Int.add_assoc,Int.add_comm,Int.add_left_comm]
  <;> omega

theorem tail_scalar_formula (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (w : Word) (hw : validWord 6 w=true) :
    ofList (tailHat.getD (27,encode w) [])=
      ofList (add (shiftScale (tau2.getD w []) (-2) 1)
        (shiftScale (tailTree.getD w []) (-1) 1)) := by
  rw [tail_scalar_raw_formula w hw,tailScalarRaw,sumTensor_coordinates]
  simp only [total_cons,total_nil,poly_add_zero,scaleTensor_coordinate]
  rw [cap_Q_diagrammatic R A F G w hw]
  simp only [ofList_add,ofList_shift]
  exact tail_scalar_algebra _ _

/-- The main row lemma now depends on the diagrammatic cap reductions. -/
theorem selected_rows_from_diagrams (R : BarReferences) (A : AtomicCoordinates R)
    (F : RibbonFunctorReferences R) (G : PositiveRibbonReferences R A F)
    (B : BoundaryTripodReferences R F) (j : Fin 28) :
    coeff (selectedBlock 5 j) 0=(if j.val=27 then 1 else 0) ∧
    coeff (selectedBlock 27 j) 0=(if j.val=5 then 2 else 0) := by
  apply two_closed_rows
  · intro i
    exact upper_formula i 5 wordBlock (by decide)
  · exact upper_scalar_raw_formula 5 wordBlock (by decide)
  · intro i
    exact lower_formula R A F G B i wordBlock (by decide)
  · exact lower_scalar_formula R A F G wordBlock (by decide)

#print axioms lower_formula
#print axioms tail_scalar_formula
#print axioms selected_rows_from_diagrams
end WebMu.Revised.LocalDegreeProof
