import WebMu.Revised.InsertionIndices
import WebMu.Revised.CircuitRealization

/-! The actual after-six-factor insertion, with its tensor bar obtained from
ordinary coordinate realization rather than an assumed insertion-naturality
formula. -/
namespace WebMu.Revised.Insertion
open Laurent Algebra Bar ShorteningCanonical

set_option maxHeartbeats 0

/-- Extend coordinates off their finite standard basis only by zero. -/
def extend {n : Nat} (f : Index n → Poly) (w : Word) : Poly :=
  if h : validWord n w = true then f ⟨w,h⟩ else 0

@[simp] theorem extend_at {n : Nat} (f : Index n → Poly) (w : Index n) :
    extend f w.val = f w := by simp [extend,w.property]

def chart (R : BarReferences) (A : AtomicCoordinates R) (s : Signs) (n : Nat)
    (x : R.Space s) : Index n → Poly := fun w => A.coord s x w.val

def realize (R : BarReferences) (A : AtomicCoordinates R) (s : Signs) {n : Nat}
    (f : Index n → Poly) : R.Space s := A.realize s (extend f)

theorem chart_realize (R : BarReferences) (A : AtomicCoordinates R)
    (s : Signs) (n : Nat) (h : s.length=n) (f : Index n → Poly) :
    chart R A s n (realize R A s f) = f := by
  funext w
  unfold chart realize
  rw [A.coord_realize _ _ _ (by simpa [h] using w.property),extend_at]

theorem realize_chart (R : BarReferences) (A : AtomicCoordinates R)
    (s : Signs) (n : Nat) (h : s.length=n) (x : R.Space s) :
    realize R A s (chart R A s n x) = x := by
  apply A.coord_ext
  intro w hw
  unfold realize
  rw [A.coord_realize _ _ _ hw]
  have hn : validWord n w=true := by simpa [h] using hw
  simp [extend,hn,chart]

/-- This is the bar of the actual tensor space in its standard coordinate chart. -/
def chartBar (R : BarReferences) (A : AtomicCoordinates R) (s : Signs) (n : Nat)
    (f : Index n → Poly) : Index n → Poly :=
  chart R A s n (R.bar s (realize R A s f))

theorem chartBar_coordinates (R : BarReferences) (A : AtomicCoordinates R)
    (s : Signs) (n : Nat) (h : s.length=n) (x : R.Space s) :
    chartBar R A s n (chart R A s n x) = chart R A s n (R.bar s x) := by
  unfold chartBar
  rw [realize_chart R A s n h x]

/-- The cited canonical-basis characterization on arbitrary signed tensor
spaces. Its bar is defined from the actual R.bar and basis-coordinate inverse.
No insertion map, growth compiler or family assertion occurs in this input. -/
structure CanonicalTheory (R : BarReferences) (A : AtomicCoordinates R) where
  characterization : ∀ s, CanonicalCharacterization (Index s.length)
    (chartBar R A s s.length)

def CanonicalTheory.at (R : BarReferences) (A : AtomicCoordinates R)
    (C : CanonicalTheory R A) (s : Signs) (n : Nat) (h : s.length=n) :
    CanonicalCharacterization (Index n) (chartBar R A s n) := by
  cases h
  exact C.characterization s

def inputSigns (n : Nat) : Signs := positive 6 ++ positive n

def outputSigns (n : Nat) : Signs := (positive 6 ++ positive 3) ++ positive n

@[simp] theorem input_length (n : Nat) : (inputSigns n).length=6+n := by
  simp [inputSigns,positive]; omega

@[simp] theorem output_length (n : Nat) : (outputSigns n).length=(6+3)+n := by
  simp [outputSigns,positive]; omega

/-- id on the first six factors, followed by the actual three-leg tripod. -/
def prefixCircuit : Circuit (positive 6) (positive 6 ++ positive 3) :=
  Circuit.tensor (.identity (positive 6)) tripodCircuit

/-- id_6 tensor tau tensor id_n, with all ordered boundary lists retained. -/
def insertionCircuit (n : Nat) : Circuit (inputSigns n) (outputSigns n) :=
  .tensor prefixCircuit (.identity (positive n))

/-- Bar equivariance of this precise typed spider morphism is derived. -/
theorem insertion_bar (R : BarReferences) (n : Nat) (x : R.Space (inputSigns n)) :
    R.bar _ (R.interpret (insertionCircuit n) x) =
      R.interpret (insertionCircuit n) (R.bar _ x) :=
  circuit_natural R (insertionCircuit n) x

/-- Exact finite comparison with the manuscript's six-term tripod table. -/
theorem tripod_circuit_check : sameEntries (evalSparse tripodCircuit []) tripod=true := by
  native_decide

theorem tripod_atomic (R : BarReferences) (A : AtomicCoordinates R)
    (w : Word) (hw : validWord 3 w=true) :
    A.coord (positive 3) (R.interpret tripodCircuit R.vacuum) w = tripodCoordinate w := by
  rw [A.closed_circuit tripodCircuit w hw]
  rw [sameEntries_getD _ _ tripod_circuit_check w]
  rfl

/-- Matrix of the first six unchanged factors and the three new factors. -/
theorem prefix_matrix (R : BarReferences) (A : AtomicCoordinates R)
    (a u : Index 6) (v : TripodIndex) :
    A.coord (positive 6 ++ positive 3)
      (R.interpret prefixCircuit (A.basis (positive 6) a.val)) (u.val++v.val) =
      (if a.val=u.val then 1 else 0) * tripodCoordinate v.val := by
  have h := A.tensor_basis (id : R.Space (positive 6) → R.Space (positive 6))
    (R.interpret tripodCircuit) (R.identity_intertwiner _) (circuit_intertwiner R _)
    a.val [] u.val v.val a.property (by decide) u.property v.property
  simp only [List.append_nil, A.basis_vacuum] at h
  change A.coord _ (R.tensorMap id (R.interpret tripodCircuit) (A.basis _ a.val)) _ = _
  rw [h]
  simp only [id_eq]
  rw [A.coord_basis (positive 6) a.val u.val a.property u.property, tripod_atomic R A v.val v.property]

theorem decoded_total_delta (n : Nat) (u : Word) (hu : validWord n u=true) (p : Poly) :
    total (List.finRange (3^n)) (fun i => if decodeWord n i.val=u then p else 0) = p := by
  have h := total_delta (completeWords n) (completeWords_nodup n) u p
  rw [if_pos ((completeWords_mem n u).mpr hu)] at h
  simpa only [completeWords,total_map] using h

/-- The full action of the actual insertion on an arbitrary input tensor.
Both unchanged boundary segments retain their order. -/
theorem insertion_coordinate (R : BarReferences) (A : AtomicCoordinates R)
    (n : Nat) (x : R.Space (inputSigns n)) (b : OldIndex n) (v : TripodIndex) :
    A.coord (outputSigns n) (R.interpret (insertionCircuit n) x)
      (insertedIndex (b,v)).val =
      A.coord (inputSigns n) x b.val * tripodCoordinate v.val := by
  let u : Index 6 := (split b).1
  let z : Index n := (split b).2
  have hb : u.val++z.val=b.val := congrArg Subtype.val (join_split b)
  change A.coord ((positive 6++positive 3)++positive n)
    (R.tensorMap (R.interpret prefixCircuit) id x) ((u.val++v.val)++z.val) = _
  rw [A.tensor_identity_coordinates (R.interpret prefixCircuit)
    (circuit_intertwiner R prefixCircuit) (positive n) x (u.val++v.val) z.val
    (by simpa [positive] using validWord_append u.property v.property)
    (by simpa [positive] using z.property)]
  change total (List.finRange (3^6)) (fun i =>
    A.coord _ (R.interpret prefixCircuit (A.basis _ (decodeWord 6 i.val))) (u.val++v.val) *
    A.coord _ x (decodeWord 6 i.val++z.val)) = _
  calc
    _ = total (List.finRange (3^6)) (fun i => if decodeWord 6 i.val=u.val
          then A.coord (inputSigns n) x b.val * tripodCoordinate v.val else 0) := by
      apply total_congr_mem
      intro i _
      rw [prefix_matrix R A ⟨decodeWord 6 i.val,decoded_word_valid 6 i⟩ u v]
      by_cases hi : decodeWord 6 i.val=u.val
      · simp only [hi,ite_true,poly_one_mul,hb]
        exact poly_mul_comm _ _
      · simp only [hi,if_false,poly_zero_mul]
    _ = _ := decoded_total_delta 6 u.val u.property _

/-- Equality on every ordered standard basis coordinate. -/
theorem insertion_coordinates (R : BarReferences) (A : AtomicCoordinates R)
    (n : Nat) (x : R.Space (inputSigns n)) :
    chart R A (outputSigns n) ((6+3)+n) (R.interpret (insertionCircuit n) x) =
      insertCoordinates (chart R A (inputSigns n) (6+n) x) := by
  funext w
  obtain ⟨b,v,h⟩ : ∃ b v, w=insertedIndex (b,v) :=
    ⟨(removeIndex w).1,(removeIndex w).2,(inserted_remove w).symm⟩
  subst w
  simp only [insertCoordinates,remove_inserted,insertTyped,ShorteningCanonical.insert,chart]
  exact insertion_coordinate R A n x b v

/-- Naturality for the actual tensor bar, transported through proved inverse
standard-coordinate charts. This is a theorem, not a reference input. -/
theorem insertion_chartBar (R : BarReferences) (A : AtomicCoordinates R)
    (n : Nat) (f : OldIndex n → Poly) :
    chartBar R A (outputSigns n) ((6+3)+n) (insertCoordinates f) =
      insertCoordinates (chartBar R A (inputSigns n) (6+n) f) := by
  have hc := insertion_coordinates R A n (realize R A (inputSigns n) f)
  rw [chart_realize R A _ _ (input_length n)] at hc
  rw [← hc,chartBar_coordinates R A _ _ (output_length n),insertion_bar,
    insertion_coordinates]
  rfl

/-- The arbitrary-boundary canonical interface is derived with the actual
coordinate bar; its compatibility law is no longer an additional input. -/
def CanonicalTheory.webReferences (R : BarReferences) (A : AtomicCoordinates R)
    (C : CanonicalTheory R A) : WebCanonical.References R A.toCoordinateReferences where
  tensorBar := fun s => chartBar R A s s.length
  coordinate_bar := fun s x => chartBar_coordinates R A s s.length rfl x
  characterization := C.characterization

/-- The manuscript's iota(b_uz)=b_uABCz, for the literal after-six tensor map
and the canonical bases characterized by its actual tensor bars. -/
theorem insertion_canonical_actual (R : BarReferences) (A : AtomicCoordinates R)
    (C : CanonicalTheory R A) (n : Nat) (c : OldIndex n) :
    insertCoordinates ((C.at R A (inputSigns n) (6+n) (input_length n)).canonical c) =
      (C.at R A (outputSigns n) ((6+3)+n) (output_length n)).canonical
        (insertedIndex (c,tripodIndex)) := by
  apply (C.at R A (outputSigns n) ((6+3)+n) (output_length n)).unique
  · rw [insertion_chartBar,(C.at R A _ _ (input_length n)).fixed]
  · exact insertCoordinates_leading _ _ ((C.at R A _ _ (input_length n)).leading c)

/-- The canonicality statement as the coordinates of the actual spider
morphism applied to the actual input vector, rather than a free coordinate map. -/
theorem interpreted_insertion_canonical (R : BarReferences) (A : AtomicCoordinates R)
    (C : CanonicalTheory R A) (n : Nat) (c : OldIndex n) :
    chart R A (outputSigns n) ((6+3)+n)
      (R.interpret (insertionCircuit n)
        (realize R A (inputSigns n)
          ((C.at R A (inputSigns n) (6+n) (input_length n)).canonical c))) =
      (C.at R A (outputSigns n) ((6+3)+n) (output_length n)).canonical
        (insertedIndex (c,tripodIndex)) := by
  rw [insertion_coordinates,chart_realize R A _ _ (input_length n)]
  exact insertion_canonical_actual R A C n c

end WebMu.Revised.Insertion
