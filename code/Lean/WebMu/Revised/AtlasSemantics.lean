import WebMu.Revised.AtlasClosed
import WebMu.Revised.Gauge

/-! Semantic consequences of the ribbon certificates. The only reference
inputs are the uniform circle, digon, square and planar-isotopy relations.
`OpenAdmissible` and `ClosedAdmissible` include the checked oriented incidence
and rotation-system planarity conditions. Their interpretation as planar
webs is the standard rotation-system classification used by these inputs.
The evaluation may be any fixed boundary coordinate, so the open identity
holds coordinatewise without choosing or permuting boundary labels. -/
namespace WebMu.Revised.Atlas
open Laurent Algebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def OpenAdmissible (g : Graph) : Prop :=
  ∃ signs, graphValid g signs = true ∧ discValid g = true

def ClosedAdmissible (g : Graph) : Prop :=
  ∃ signs, closedGraphValid g signs = true ∧ closedPlanar g = true

/-- Kuperberg's oriented A₂ spider relations, in the checked ribbon encoding.
All fields are uniform in the graphs; no atlas or family identity is assumed. -/
structure OpenSpiderReferences where
  eval : Graph → Poly
  isotopy : ∀ g h iso, OpenAdmissible g → OpenAdmissible h →
    bijectionValid g h iso = true → eval g = eval h
  square : ∀ g f h k, OpenAdmissible g → OpenAdmissible h → OpenAdmissible k →
    f.vertices.length = 4 → resolvedTo g f [(0,1),(2,3)] h = true →
    resolvedTo g f [(1,2),(3,0)] k = true → eval g = eval h + eval k
  digon : ∀ g f h, OpenAdmissible g → OpenAdmissible h →
    f.vertices.length = 2 → resolvedTo g f [(0,1)] h = true →
    eval g = ofList d * eval h

structure ClosedSpiderReferences where
  eval : Graph → Poly
  isotopy : ∀ g h iso, ClosedAdmissible g → ClosedAdmissible h →
    closedBijectionValid g h iso = true → eval g = eval h
  square : ∀ g f h k, ClosedAdmissible g → ClosedAdmissible h → ClosedAdmissible k →
    f.vertices.length = 4 → resolvedTo g f [(0,1),(2,3)] h = true →
    resolvedTo g f [(1,2),(3,0)] k = true → eval g = eval h + eval k
  digon : ∀ g f h, ClosedAdmissible g → ClosedAdmissible h →
    (match closedDigon g f with | none => false | some k => sameGraph k h) = true →
    eval g = ofList d * eval h
  circles : ∀ g, ClosedAdmissible g → g.edges = [] → g.rotations = [] →
    eval g = ofList (pow e g.circles)

theorem open_node_admissible (i : Fin 38) : OpenAdmissible atlasNodes[i.val]!.graph := by
  have h : ∀ i : Fin 38, graphValid atlasNodes[i.val]!.graph atlasNodes[i.val]!.signs = true ∧
      discValid atlasNodes[i.val]!.graph = true := by native_decide
  exact ⟨_,h i⟩

theorem summand_admissible (i : Fin 19) : OpenAdmissible atlasSummands[i.val]! := by
  have h : ∀ i : Fin 19, graphValid atlasSummands[i.val]! summandSigns[i.val]! = true ∧
      discValid atlasSummands[i.val]! = true := by native_decide
  exact ⟨_,h i⟩

def openValue (R : OpenSpiderReferences) (i : Nat) := R.eval atlasNodes[i]!.graph
def summandValue (R : OpenSpiderReferences) (i : Nat) := R.eval atlasSummands[i]!

private theorem open_step_0 (R : OpenSpiderReferences) : openValue R 0 = openValue R 1 + openValue R 22 := by
  exact R.square _ atlasNodes[0]!.face _ _ (open_node_admissible 0)
    (open_node_admissible 1) (open_node_admissible 22) rfl (by native_decide) (by native_decide)

private theorem open_step_1 (R : OpenSpiderReferences) : openValue R 1 = openValue R 2 + openValue R 11 := by
  exact R.square _ atlasNodes[1]!.face _ _ (open_node_admissible 1)
    (open_node_admissible 2) (open_node_admissible 11) rfl (by native_decide) (by native_decide)

private theorem open_step_2 (R : OpenSpiderReferences) : openValue R 2 = openValue R 3 + openValue R 10 := by
  exact R.square _ atlasNodes[2]!.face _ _ (open_node_admissible 2)
    (open_node_admissible 3) (open_node_admissible 10) rfl (by native_decide) (by native_decide)

private theorem open_step_3 (R : OpenSpiderReferences) : openValue R 3 = openValue R 4 + openValue R 7 := by
  exact R.square _ atlasNodes[3]!.face _ _ (open_node_admissible 3)
    (open_node_admissible 4) (open_node_admissible 7) rfl (by native_decide) (by native_decide)

private theorem open_step_4 (R : OpenSpiderReferences) : openValue R 4 = openValue R 5 + openValue R 6 := by
  exact R.square _ atlasNodes[4]!.face _ _ (open_node_admissible 4)
    (open_node_admissible 5) (open_node_admissible 6) rfl (by native_decide) (by native_decide)

private theorem open_step_5 (R : OpenSpiderReferences) : openValue R 5 = summandValue R 10 := by
  exact R.isotopy _ _ atlasNodes[5]!.iso (open_node_admissible 5) (summand_admissible 10) (by native_decide)

private theorem open_step_6 (R : OpenSpiderReferences) : openValue R 6 = summandValue R 12 := by
  exact R.isotopy _ _ atlasNodes[6]!.iso (open_node_admissible 6) (summand_admissible 12) (by native_decide)

private theorem open_step_7 (R : OpenSpiderReferences) : openValue R 7 = openValue R 8 + openValue R 9 := by
  exact R.square _ atlasNodes[7]!.face _ _ (open_node_admissible 7)
    (open_node_admissible 8) (open_node_admissible 9) rfl (by native_decide) (by native_decide)

private theorem open_step_8 (R : OpenSpiderReferences) : openValue R 8 = summandValue R 9 := by
  exact R.isotopy _ _ atlasNodes[8]!.iso (open_node_admissible 8) (summand_admissible 9) (by native_decide)

private theorem open_step_9 (R : OpenSpiderReferences) : openValue R 9 = summandValue R 8 := by
  exact R.isotopy _ _ atlasNodes[9]!.iso (open_node_admissible 9) (summand_admissible 8) (by native_decide)

private theorem open_step_10 (R : OpenSpiderReferences) : openValue R 10 = summandValue R 11 := by
  exact R.isotopy _ _ atlasNodes[10]!.iso (open_node_admissible 10) (summand_admissible 11) (by native_decide)

private theorem open_step_11 (R : OpenSpiderReferences) : openValue R 11 = openValue R 12 + openValue R 17 := by
  exact R.square _ atlasNodes[11]!.face _ _ (open_node_admissible 11)
    (open_node_admissible 12) (open_node_admissible 17) rfl (by native_decide) (by native_decide)

private theorem open_step_12 (R : OpenSpiderReferences) : openValue R 12 = openValue R 13 + openValue R 16 := by
  exact R.square _ atlasNodes[12]!.face _ _ (open_node_admissible 12)
    (open_node_admissible 13) (open_node_admissible 16) rfl (by native_decide) (by native_decide)

private theorem open_step_13 (R : OpenSpiderReferences) : openValue R 13 = openValue R 14 + openValue R 15 := by
  exact R.square _ atlasNodes[13]!.face _ _ (open_node_admissible 13)
    (open_node_admissible 14) (open_node_admissible 15) rfl (by native_decide) (by native_decide)

private theorem open_step_14 (R : OpenSpiderReferences) : openValue R 14 = summandValue R 18 := by
  exact R.isotopy _ _ atlasNodes[14]!.iso (open_node_admissible 14) (summand_admissible 18) (by native_decide)

private theorem open_step_15 (R : OpenSpiderReferences) : openValue R 15 = summandValue R 16 := by
  exact R.isotopy _ _ atlasNodes[15]!.iso (open_node_admissible 15) (summand_admissible 16) (by native_decide)

private theorem open_step_16 (R : OpenSpiderReferences) : openValue R 16 = summandValue R 17 := by
  exact R.isotopy _ _ atlasNodes[16]!.iso (open_node_admissible 16) (summand_admissible 17) (by native_decide)

private theorem open_step_17 (R : OpenSpiderReferences) : openValue R 17 = openValue R 18 + openValue R 21 := by
  exact R.square _ atlasNodes[17]!.face _ _ (open_node_admissible 17)
    (open_node_admissible 18) (open_node_admissible 21) rfl (by native_decide) (by native_decide)

private theorem open_step_18 (R : OpenSpiderReferences) : openValue R 18 = openValue R 19 + openValue R 20 := by
  exact R.square _ atlasNodes[18]!.face _ _ (open_node_admissible 18)
    (open_node_admissible 19) (open_node_admissible 20) rfl (by native_decide) (by native_decide)

private theorem open_step_19 (R : OpenSpiderReferences) : openValue R 19 = summandValue R 14 := by
  exact R.isotopy _ _ atlasNodes[19]!.iso (open_node_admissible 19) (summand_admissible 14) (by native_decide)

private theorem open_step_20 (R : OpenSpiderReferences) : openValue R 20 = summandValue R 15 := by
  exact R.isotopy _ _ atlasNodes[20]!.iso (open_node_admissible 20) (summand_admissible 15) (by native_decide)

private theorem open_step_21 (R : OpenSpiderReferences) : openValue R 21 = summandValue R 13 := by
  exact R.isotopy _ _ atlasNodes[21]!.iso (open_node_admissible 21) (summand_admissible 13) (by native_decide)

private theorem open_step_22 (R : OpenSpiderReferences) : openValue R 22 = ofList d * openValue R 23 := by
  exact R.digon _ atlasNodes[22]!.face _ (open_node_admissible 22)
    (open_node_admissible 23) rfl (by native_decide)

private theorem open_step_23 (R : OpenSpiderReferences) : openValue R 23 = openValue R 24 + openValue R 31 := by
  exact R.square _ atlasNodes[23]!.face _ _ (open_node_admissible 23)
    (open_node_admissible 24) (open_node_admissible 31) rfl (by native_decide) (by native_decide)

private theorem open_step_24 (R : OpenSpiderReferences) : openValue R 24 = openValue R 25 + openValue R 30 := by
  exact R.square _ atlasNodes[24]!.face _ _ (open_node_admissible 24)
    (open_node_admissible 25) (open_node_admissible 30) rfl (by native_decide) (by native_decide)

private theorem open_step_25 (R : OpenSpiderReferences) : openValue R 25 = openValue R 26 + openValue R 29 := by
  exact R.square _ atlasNodes[25]!.face _ _ (open_node_admissible 25)
    (open_node_admissible 26) (open_node_admissible 29) rfl (by native_decide) (by native_decide)

private theorem open_step_26 (R : OpenSpiderReferences) : openValue R 26 = openValue R 27 + openValue R 28 := by
  exact R.square _ atlasNodes[26]!.face _ _ (open_node_admissible 26)
    (open_node_admissible 27) (open_node_admissible 28) rfl (by native_decide) (by native_decide)

private theorem open_step_27 (R : OpenSpiderReferences) : openValue R 27 = summandValue R 7 := by
  exact R.isotopy _ _ atlasNodes[27]!.iso (open_node_admissible 27) (summand_admissible 7) (by native_decide)

private theorem open_step_28 (R : OpenSpiderReferences) : openValue R 28 = summandValue R 6 := by
  exact R.isotopy _ _ atlasNodes[28]!.iso (open_node_admissible 28) (summand_admissible 6) (by native_decide)

private theorem open_step_29 (R : OpenSpiderReferences) : openValue R 29 = summandValue R 5 := by
  exact R.isotopy _ _ atlasNodes[29]!.iso (open_node_admissible 29) (summand_admissible 5) (by native_decide)

private theorem open_step_30 (R : OpenSpiderReferences) : openValue R 30 = summandValue R 3 := by
  exact R.isotopy _ _ atlasNodes[30]!.iso (open_node_admissible 30) (summand_admissible 3) (by native_decide)

private theorem open_step_31 (R : OpenSpiderReferences) : openValue R 31 = openValue R 32 + openValue R 35 := by
  exact R.square _ atlasNodes[31]!.face _ _ (open_node_admissible 31)
    (open_node_admissible 32) (open_node_admissible 35) rfl (by native_decide) (by native_decide)

private theorem open_step_32 (R : OpenSpiderReferences) : openValue R 32 = openValue R 33 + openValue R 34 := by
  exact R.square _ atlasNodes[32]!.face _ _ (open_node_admissible 32)
    (open_node_admissible 33) (open_node_admissible 34) rfl (by native_decide) (by native_decide)

private theorem open_step_33 (R : OpenSpiderReferences) : openValue R 33 = summandValue R 2 := by
  exact R.isotopy _ _ atlasNodes[33]!.iso (open_node_admissible 33) (summand_admissible 2) (by native_decide)

private theorem open_step_34 (R : OpenSpiderReferences) : openValue R 34 = summandValue R 4 := by
  exact R.isotopy _ _ atlasNodes[34]!.iso (open_node_admissible 34) (summand_admissible 4) (by native_decide)

private theorem open_step_35 (R : OpenSpiderReferences) : openValue R 35 = openValue R 36 + openValue R 37 := by
  exact R.square _ atlasNodes[35]!.face _ _ (open_node_admissible 35)
    (open_node_admissible 36) (open_node_admissible 37) rfl (by native_decide) (by native_decide)

private theorem open_step_36 (R : OpenSpiderReferences) : openValue R 36 = summandValue R 1 := by
  exact R.isotopy _ _ atlasNodes[36]!.iso (open_node_admissible 36) (summand_admissible 1) (by native_decide)

private theorem open_step_37 (R : OpenSpiderReferences) : openValue R 37 = summandValue R 0 := by
  exact R.isotopy _ _ atlasNodes[37]!.iso (open_node_admissible 37) (summand_admissible 0) (by native_decide)

/-- The complete open reduction, with all nineteen terminal growth graphs.
The first eight are D, and the final eleven are H. -/
theorem open_atlas_identity (R : OpenSpiderReferences) :
    openValue R 0 = ofList d * total (List.range 8) (summandValue R) +
      total (List.range' 8 11) (summandValue R) := by
  rw [open_step_0, open_step_1, open_step_2, open_step_3, open_step_4, open_step_5, open_step_6, open_step_7, open_step_8, open_step_9, open_step_10, open_step_11, open_step_12, open_step_13, open_step_14, open_step_15, open_step_16, open_step_17, open_step_18, open_step_19, open_step_20, open_step_21, open_step_22, open_step_23, open_step_24, open_step_25, open_step_26, open_step_27, open_step_28, open_step_29, open_step_30, open_step_31, open_step_32, open_step_33, open_step_34, open_step_35, open_step_36, open_step_37]
  change _ = ofList d * (summandValue R 0 + (summandValue R 1 + (summandValue R 2 + (summandValue R 3 + (summandValue R 4 + (summandValue R 5 + (summandValue R 6 + (summandValue R 7 + (0))))))))) + (summandValue R 8 + (summandValue R 9 + (summandValue R 10 + (summandValue R 11 + (summandValue R 12 + (summandValue R 13 + (summandValue R 14 + (summandValue R 15 + (summandValue R 16 + (summandValue R 17 + (summandValue R 18 + (0))))))))))))
  have hac (a b c : Poly) : a + (b + c) = b + (a + c) := by rw [← poly_add_assoc, poly_add_comm a b, poly_add_assoc]
  simp only [hac, poly_mul_add, poly_mul_zero, poly_add_zero, poly_zero_add, poly_add_assoc, poly_add_comm]

end WebMu.Revised.Atlas
