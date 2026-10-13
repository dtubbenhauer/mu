import WebMu.Revised.AtomicMain

/-! The manuscript's global proof, with its local conclusions explicit.
`Properties` is a bundle of proved local lemmas, not a prior-work input.
The concrete construction of this bundle must discharge every field using
the local degree, cap-diagram, leading-path and two-row proofs. No theorem
below calls the older full transformed-matrix lattice certificates. -/
namespace WebMu.Revised.WrittenProof
open Laurent Algebra Family Tableaux Bar

structure Properties : Prop where
  prefix_nonpositive : ∀ o i, Nonpositive (prefixCoordinate o i)
  block_nonpositive : ∀ e i j, Nonpositive (blockCoordinate e i j)
  tail_nonpositive : ∀ r i, Nonpositive (tailCoordinate r i)
  prefix_constant : ∀ o, coeff (prefixCoordinate o 0) 0 = if o=wordY then 1 else 0
  block_constant : ∀ e i, coeff (blockCoordinate e i 0) 0 =
    if i=0 then (if e=encode wordU then 1 else 0) else 0
  tail_constant : ∀ r i, coeff (tailCoordinate r i) 0 =
    if i=0 then (if r=encode wordV then 1 else 0) else 0
  selected_prefix_constant : ∀ i : Fin 28,
    coeff (selectedPrefix i.val) 0=if i=5 then 1 else 0
  selected_tail_constant : ∀ i : Fin 28, coeff (selectedTail i.val) 0=0
  selected_ABC_row : ∀ i : Fin 28,
    coeff (selectedBlock 5 i.val) 0=if i=27 then 1 else 0
  selected_scalar_row : ∀ i : Fin 28,
    coeff (selectedBlock 27 i.val) 0=if i=5 then 2 else 0
  selected_tail_ABC_first : coeff (selectedTail 5) (-1)=1
  selected_tail_scalar_first : coeff (selectedTail 27) (-1)=0

/-- Induction through every ordered exterior decoration, at every parameter. -/
theorem gauged_unique_leading (P : Properties) (o : Word) (es : List Nat) (r : Nat) :
    Nonpositive (gaugedTensor o es r) ∧ coeff (gaugedTensor o es r) 0 =
      if o=wordY ∧ es=List.replicate es.length (encode wordU) ∧ r=encode wordV then 1 else 0 := by
  exact tensor_unique_leading_state interfaceIndices interfaceIndices_nodup 0
    (interfaceIndices_mem 0) prefixCoordinate blockCoordinate tailCoordinate
    wordY (encode wordU) (encode wordV) P.prefix_nonpositive P.block_nonpositive
    P.tail_nonpositive P.prefix_constant P.block_constant P.tail_constant o es r

/-- Gauge cancellation transfers the derived lattice conclusion to the
original unchanged tensor. No bar compatibility of the gauge is assumed. -/
theorem original_integral (P : Properties) (m : Nat) (b : Boundary m)
    (d : Int) (hd : 0<d) : coefficient (tensorOriginal m b) d=0 := by
  rw [← tensor_coordinate_change]
  exact coeff_positive _ (gauged_unique_leading P _ _ _).1 d hd

theorem original_constant (P : Properties) (m : Nat) (b : Boundary m) :
    coefficient (tensorOriginal m b) 0=if b=leadingBoundary m then 1 else 0 := by
  classical
  rw [← tensor_coordinate_change]
  change coeff (gaugedTensor b.initial (b.blocks.map encode) (encode b.terminal)) 0 = _
  rw [(gauged_unique_leading P _ _ _).2,List.length_map]
  have hb : b.blocks.map encode=List.replicate b.blocks.length (encode wordU) ↔
      b.blocks=List.replicate b.blocks.length wordU :=
    map_encode_replicate_iff b.blocks wordU b.blocks_valid (by simp [Ternary,wordU])
  have ht : encode b.terminal=encode wordV ↔ b.terminal=wordV :=
    encode_eq_iff_fixed_length b.terminal wordV b.terminal_ternary (by simp [Ternary,wordV]) b.terminal_length
  have hi : b.initial=wordY ∧ b.blocks=List.replicate b.blocks.length wordU ∧
      b.terminal=wordV ↔ b=leadingBoundary m := by
    constructor
    · rintro ⟨h₁,h₂,h₃⟩
      apply Boundary.ext h₁ _ h₃
      simpa [leadingBoundary,b.blocks_length] using h₂
    · intro h; subst b; simp [leadingBoundary]
  simp only [hb,ht,hi]

/-- The selected coefficient uses the two closed ROWS and their K²=2I
recurrence. Other interface coordinates may be populated throughout. -/
theorem selected_coefficient_all (P : Properties) (m : Nat) :
    coeff (selectedGaugedCoefficient m) (-1)=
      if m%2=0 then (2:Int)^(m/2) else 0 := by
  apply selected_coefficient interfaceIndices interfaceIndices_nodup
    (fun i => selectedPrefix i.val) (fun i j => selectedBlock i.val j.val)
    (fun i => selectedTail i.val) 5 27 (interfaceIndices_mem 5) (interfaceIndices_mem 27)
  · exact P.prefix_nonpositive wordEnd
  · exact P.block_nonpositive (encode wordBlock)
  · exact P.tail_nonpositive (encode wordEnd)
  · exact P.selected_tail_constant
  · exact P.selected_prefix_constant
  · exact P.selected_ABC_row
  · exact P.selected_scalar_row
  · exact P.selected_tail_ABC_first
  · exact P.selected_tail_scalar_first

theorem original_source_even (P : Properties) (r : Nat) :
    coefficient (tensorOriginal (2*r) (sourceBoundary (2*r))) (-1)=(2:Int)^r := by
  rw [← tensor_coordinate_change]
  change coeff (gaugedTensor wordEnd ((List.replicate (2*r) wordBlock).map encode)
    (encode wordEnd)) (-1) = _
  rw [List.map_replicate,← selected_is_gaugedTensor,selected_coefficient_all P]
  have hm : (2*r)%2=0 := by omega
  have hd : (2*r)/2=r := by omega
  simp [hm,hd]

/-- Canonicality uses original tensor bar invariance and the locally proved
lattice/leading-state induction. -/
theorem canonicality (P : Properties) (R : BarReferences) (A : AtomicCoordinates R)
    (C : CanonicalReferences A.tensorBar) (m : Nat) :
    tensorOriginal m=C.canonical m (leadingBoundary m) := by
  exact C.unique m (leadingBoundary m) (tensorOriginal m)
    (tensorOriginal_fixed R A.toCoordinateReferences m)
    (original_integral P m) (original_constant P m)

/-- The dictionary and ordinary degree bound identify this exact tensor
coefficient with the claimed ordinary mu coefficient. -/
theorem ordinary_mu (P : Properties) (R : BarReferences) (A : AtomicCoordinates R)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (F : FKKReferences A.tensorBar C K) (r : Nat) :
    ordinaryMu K (xPermutation (2*r)) (yPermutation (2*r))=(2:Int)^r := by
  have hcan := canonicality P R A C (2*r)
  have hdict := F.dictionary (2*r) (sourceBoundary (2*r)) (leadingBoundary (2*r))
    (N (2*r)) (by simpa [Balanced] using content_a (2*r))
    (by simpa [Balanced] using content_c (2*r))
    (by simpa using dominant_c (2*r)) (by simpa using family_rank_order (2*r))
  have hvalue := original_source_even P r
  rw [hcan,hdict] at hvalue
  simp only [source_familyWord,leading_familyWord] at hvalue
  have hg := coxeter_length_gap (2*r)
  have hd : (coxeterLength (yPermutation (2*r)) : Int)-
      (coxeterLength (xPermutation (2*r)) : Int)=2*((17*r+5 : Nat):Int)+1 := by omega
  change coeff (substituteKL
    ((coxeterLength (yPermutation (2*r)) : Int)-(coxeterLength (xPermutation (2*r)) : Int))
    (K.parabolic (N (2*r)) (xPermutation (2*r)) (yPermutation (2*r)))) (-1)=_ at hvalue
  rw [substituteKL_coefficient _ _ _ hd] at hvalue
  rw [← ordinary_parabolic_top K r]
  exact hvalue

theorem family_conclusion (P : Properties) (R : BarReferences) (A : AtomicCoordinates R)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (F : FKKReferences A.tensorBar C K) (S : CellReferences) (r : Nat) :
    FamilyConclusion K S r := by
  have hgap := coxeter_length_gap (2*r)
  have hr := family_RSK S.insertion S.recording S.rowReading (2*r)
  refine ⟨?_,?_,family_strict_rank_order (2*r),by omega,ordinary_mu P R A C K F r,
    family_common_left_cell S.insertion S.recording S.sameLeftCell
      S.rowReading S.leftCellCriterion (2*r),?_,?_⟩
  · simpa [length_a,← Nat.mul_assoc] using permutation_perm_range (aWord (2*r))
  · simpa [length_c,← Nat.mul_assoc] using permutation_perm_range (cWord (2*r))
  · simpa [N,← Nat.mul_assoc] using hr.2.2.1
  · simpa [N,← Nat.mul_assoc] using hr.2.2.2

/-- Complete main conclusion, with the actual reduced-subword Bruhat order. -/
theorem main (P : Properties) (R : BarReferences) (A : AtomicCoordinates R)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (F : FKKReferences A.tensorBar C K) (S : CellReferences)
    (B : Bruhat.References) (r : Nat) : SubwordFamilyConclusion K S r := by
  have h := family_conclusion P R A C K F S r
  exact ⟨h,Bruhat.subword_of_rank B _ _ _ h.x_permutation h.y_permutation
    h.strict_bruhat_rank.1,h.strict_bruhat_rank.2⟩

theorem unbounded (P : Properties) (R : BarReferences) (A : AtomicCoordinates R)
    (C : CanonicalReferences A.tensorBar) (K : KLReferences)
    (F : FKKReferences A.tensorBar C K) (S : CellReferences) (bound : Nat) :
    ∃ r, (bound:Int)<ordinaryMu K (xPermutation (2*r)) (yPermutation (2*r)) ∧
      S.sameLeftCell (xPermutation (2*r)) (yPermutation (2*r)) := by
  refine ⟨bound,?_,(family_conclusion P R A C K F S bound).common_left_cell⟩
  rw [ordinary_mu P R A C K F bound]
  exact powers_two_grow bound

#print axioms original_integral
#print axioms original_constant
#print axioms original_source_even
#print axioms canonicality
#print axioms main
end WebMu.Revised.WrittenProof
