import WebMu.Revised.AtlasSemantics

/-! The complete closed reduction forest, interpreted by the uniform
spider reference relations. Generated proof applications are checked by Lean;
no closed-graph evaluation is supplied as a reference input. -/
namespace WebMu.Revised.Atlas
open Laurent Algebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def closedValue (i : Nat) := closedExpansion 210 i

def closedEvaluation (R : ClosedSpiderReferences) (i : Nat) :=
  R.eval closedNodes[i]!.graph

theorem closed_node_admissible (i : Fin 209) : ClosedAdmissible closedNodes[i.val]!.graph := by
  have h : ∀ i : Fin 209, closedGraphValid closedNodes[i.val]!.graph closedNodes[i.val]!.signs = true ∧
      closedPlanar closedNodes[i.val]!.graph = true := by native_decide
  exact ⟨_,h i⟩

private theorem closed_value_208 (R : ClosedSpiderReferences) :
    closedEvaluation R 208 = ofList (closedValue 208) := by
  have h := R.circles _ (closed_node_admissible 208) rfl rfl
  change closedEvaluation R 208 = ofList (pow e closedNodes[208]!.graph.circles) at h
  have hc : closedValue 208 = pow e closedNodes[208]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_207 (R : ClosedSpiderReferences) :
    closedEvaluation R 207 = ofList (closedValue 207) := by
  have h := R.digon _ closedNodes[207]!.face _ (closed_node_admissible 207)
    (closed_node_admissible 208) (by native_decide)
  change closedEvaluation R 207 = ofList d * closedEvaluation R 208 at h
  rw [closed_value_208] at h
  have hc : closedValue 207 = mul d (closedValue 208) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_206 (R : ClosedSpiderReferences) :
    closedEvaluation R 206 = ofList (closedValue 206) := by
  have h := R.digon _ closedNodes[206]!.face _ (closed_node_admissible 206)
    (closed_node_admissible 207) (by native_decide)
  change closedEvaluation R 206 = ofList d * closedEvaluation R 207 at h
  rw [closed_value_207] at h
  have hc : closedValue 206 = mul d (closedValue 207) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_205 (R : ClosedSpiderReferences) :
    closedEvaluation R 205 = ofList (closedValue 205) := by
  have h := R.circles _ (closed_node_admissible 205) rfl rfl
  change closedEvaluation R 205 = ofList (pow e closedNodes[205]!.graph.circles) at h
  have hc : closedValue 205 = pow e closedNodes[205]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_204 (R : ClosedSpiderReferences) :
    closedEvaluation R 204 = ofList (closedValue 204) := by
  have h := R.digon _ closedNodes[204]!.face _ (closed_node_admissible 204)
    (closed_node_admissible 205) (by native_decide)
  change closedEvaluation R 204 = ofList d * closedEvaluation R 205 at h
  rw [closed_value_205] at h
  have hc : closedValue 204 = mul d (closedValue 205) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_203 (R : ClosedSpiderReferences) :
    closedEvaluation R 203 = ofList (closedValue 203) := by
  have h := R.digon _ closedNodes[203]!.face _ (closed_node_admissible 203)
    (closed_node_admissible 204) (by native_decide)
  change closedEvaluation R 203 = ofList d * closedEvaluation R 204 at h
  rw [closed_value_204] at h
  have hc : closedValue 203 = mul d (closedValue 204) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_202 (R : ClosedSpiderReferences) :
    closedEvaluation R 202 = ofList (closedValue 202) := by
  have h := R.square _ closedNodes[202]!.face _ _ (closed_node_admissible 202)
    (closed_node_admissible 203) (closed_node_admissible 206) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 202 = closedEvaluation R 203 + closedEvaluation R 206 at h
  rw [closed_value_203,closed_value_206] at h
  have hc : closedValue 202 = add (closedValue 203) (closedValue 206) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_201 (R : ClosedSpiderReferences) :
    closedEvaluation R 201 = ofList (closedValue 201) := by
  have h := R.circles _ (closed_node_admissible 201) rfl rfl
  change closedEvaluation R 201 = ofList (pow e closedNodes[201]!.graph.circles) at h
  have hc : closedValue 201 = pow e closedNodes[201]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_200 (R : ClosedSpiderReferences) :
    closedEvaluation R 200 = ofList (closedValue 200) := by
  have h := R.digon _ closedNodes[200]!.face _ (closed_node_admissible 200)
    (closed_node_admissible 201) (by native_decide)
  change closedEvaluation R 200 = ofList d * closedEvaluation R 201 at h
  rw [closed_value_201] at h
  have hc : closedValue 200 = mul d (closedValue 201) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_199 (R : ClosedSpiderReferences) :
    closedEvaluation R 199 = ofList (closedValue 199) := by
  have h := R.digon _ closedNodes[199]!.face _ (closed_node_admissible 199)
    (closed_node_admissible 200) (by native_decide)
  change closedEvaluation R 199 = ofList d * closedEvaluation R 200 at h
  rw [closed_value_200] at h
  have hc : closedValue 199 = mul d (closedValue 200) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_198 (R : ClosedSpiderReferences) :
    closedEvaluation R 198 = ofList (closedValue 198) := by
  have h := R.circles _ (closed_node_admissible 198) rfl rfl
  change closedEvaluation R 198 = ofList (pow e closedNodes[198]!.graph.circles) at h
  have hc : closedValue 198 = pow e closedNodes[198]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_197 (R : ClosedSpiderReferences) :
    closedEvaluation R 197 = ofList (closedValue 197) := by
  have h := R.digon _ closedNodes[197]!.face _ (closed_node_admissible 197)
    (closed_node_admissible 198) (by native_decide)
  change closedEvaluation R 197 = ofList d * closedEvaluation R 198 at h
  rw [closed_value_198] at h
  have hc : closedValue 197 = mul d (closedValue 198) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_196 (R : ClosedSpiderReferences) :
    closedEvaluation R 196 = ofList (closedValue 196) := by
  have h := R.digon _ closedNodes[196]!.face _ (closed_node_admissible 196)
    (closed_node_admissible 197) (by native_decide)
  change closedEvaluation R 196 = ofList d * closedEvaluation R 197 at h
  rw [closed_value_197] at h
  have hc : closedValue 196 = mul d (closedValue 197) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_195 (R : ClosedSpiderReferences) :
    closedEvaluation R 195 = ofList (closedValue 195) := by
  have h := R.square _ closedNodes[195]!.face _ _ (closed_node_admissible 195)
    (closed_node_admissible 196) (closed_node_admissible 199) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 195 = closedEvaluation R 196 + closedEvaluation R 199 at h
  rw [closed_value_196,closed_value_199] at h
  have hc : closedValue 195 = add (closedValue 196) (closedValue 199) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_194 (R : ClosedSpiderReferences) :
    closedEvaluation R 194 = ofList (closedValue 194) := by
  have h := R.circles _ (closed_node_admissible 194) rfl rfl
  change closedEvaluation R 194 = ofList (pow e closedNodes[194]!.graph.circles) at h
  have hc : closedValue 194 = pow e closedNodes[194]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_193 (R : ClosedSpiderReferences) :
    closedEvaluation R 193 = ofList (closedValue 193) := by
  have h := R.digon _ closedNodes[193]!.face _ (closed_node_admissible 193)
    (closed_node_admissible 194) (by native_decide)
  change closedEvaluation R 193 = ofList d * closedEvaluation R 194 at h
  rw [closed_value_194] at h
  have hc : closedValue 193 = mul d (closedValue 194) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_192 (R : ClosedSpiderReferences) :
    closedEvaluation R 192 = ofList (closedValue 192) := by
  have h := R.digon _ closedNodes[192]!.face _ (closed_node_admissible 192)
    (closed_node_admissible 193) (by native_decide)
  change closedEvaluation R 192 = ofList d * closedEvaluation R 193 at h
  rw [closed_value_193] at h
  have hc : closedValue 192 = mul d (closedValue 193) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_191 (R : ClosedSpiderReferences) :
    closedEvaluation R 191 = ofList (closedValue 191) := by
  have h := R.digon _ closedNodes[191]!.face _ (closed_node_admissible 191)
    (closed_node_admissible 192) (by native_decide)
  change closedEvaluation R 191 = ofList d * closedEvaluation R 192 at h
  rw [closed_value_192] at h
  have hc : closedValue 191 = mul d (closedValue 192) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_190 (R : ClosedSpiderReferences) :
    closedEvaluation R 190 = ofList (closedValue 190) := by
  have h := R.digon _ closedNodes[190]!.face _ (closed_node_admissible 190)
    (closed_node_admissible 191) (by native_decide)
  change closedEvaluation R 190 = ofList d * closedEvaluation R 191 at h
  rw [closed_value_191] at h
  have hc : closedValue 190 = mul d (closedValue 191) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_189 (R : ClosedSpiderReferences) :
    closedEvaluation R 189 = ofList (closedValue 189) := by
  have h := R.square _ closedNodes[189]!.face _ _ (closed_node_admissible 189)
    (closed_node_admissible 190) (closed_node_admissible 195) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 189 = closedEvaluation R 190 + closedEvaluation R 195 at h
  rw [closed_value_190,closed_value_195] at h
  have hc : closedValue 189 = add (closedValue 190) (closedValue 195) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_188 (R : ClosedSpiderReferences) :
    closedEvaluation R 188 = ofList (closedValue 188) := by
  have h := R.circles _ (closed_node_admissible 188) rfl rfl
  change closedEvaluation R 188 = ofList (pow e closedNodes[188]!.graph.circles) at h
  have hc : closedValue 188 = pow e closedNodes[188]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_187 (R : ClosedSpiderReferences) :
    closedEvaluation R 187 = ofList (closedValue 187) := by
  have h := R.digon _ closedNodes[187]!.face _ (closed_node_admissible 187)
    (closed_node_admissible 188) (by native_decide)
  change closedEvaluation R 187 = ofList d * closedEvaluation R 188 at h
  rw [closed_value_188] at h
  have hc : closedValue 187 = mul d (closedValue 188) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_186 (R : ClosedSpiderReferences) :
    closedEvaluation R 186 = ofList (closedValue 186) := by
  have h := R.digon _ closedNodes[186]!.face _ (closed_node_admissible 186)
    (closed_node_admissible 187) (by native_decide)
  change closedEvaluation R 186 = ofList d * closedEvaluation R 187 at h
  rw [closed_value_187] at h
  have hc : closedValue 186 = mul d (closedValue 187) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_185 (R : ClosedSpiderReferences) :
    closedEvaluation R 185 = ofList (closedValue 185) := by
  have h := R.circles _ (closed_node_admissible 185) rfl rfl
  change closedEvaluation R 185 = ofList (pow e closedNodes[185]!.graph.circles) at h
  have hc : closedValue 185 = pow e closedNodes[185]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_184 (R : ClosedSpiderReferences) :
    closedEvaluation R 184 = ofList (closedValue 184) := by
  have h := R.digon _ closedNodes[184]!.face _ (closed_node_admissible 184)
    (closed_node_admissible 185) (by native_decide)
  change closedEvaluation R 184 = ofList d * closedEvaluation R 185 at h
  rw [closed_value_185] at h
  have hc : closedValue 184 = mul d (closedValue 185) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_183 (R : ClosedSpiderReferences) :
    closedEvaluation R 183 = ofList (closedValue 183) := by
  have h := R.digon _ closedNodes[183]!.face _ (closed_node_admissible 183)
    (closed_node_admissible 184) (by native_decide)
  change closedEvaluation R 183 = ofList d * closedEvaluation R 184 at h
  rw [closed_value_184] at h
  have hc : closedValue 183 = mul d (closedValue 184) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_182 (R : ClosedSpiderReferences) :
    closedEvaluation R 182 = ofList (closedValue 182) := by
  have h := R.square _ closedNodes[182]!.face _ _ (closed_node_admissible 182)
    (closed_node_admissible 183) (closed_node_admissible 186) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 182 = closedEvaluation R 183 + closedEvaluation R 186 at h
  rw [closed_value_183,closed_value_186] at h
  have hc : closedValue 182 = add (closedValue 183) (closedValue 186) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_181 (R : ClosedSpiderReferences) :
    closedEvaluation R 181 = ofList (closedValue 181) := by
  have h := R.circles _ (closed_node_admissible 181) rfl rfl
  change closedEvaluation R 181 = ofList (pow e closedNodes[181]!.graph.circles) at h
  have hc : closedValue 181 = pow e closedNodes[181]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_180 (R : ClosedSpiderReferences) :
    closedEvaluation R 180 = ofList (closedValue 180) := by
  have h := R.digon _ closedNodes[180]!.face _ (closed_node_admissible 180)
    (closed_node_admissible 181) (by native_decide)
  change closedEvaluation R 180 = ofList d * closedEvaluation R 181 at h
  rw [closed_value_181] at h
  have hc : closedValue 180 = mul d (closedValue 181) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_179 (R : ClosedSpiderReferences) :
    closedEvaluation R 179 = ofList (closedValue 179) := by
  have h := R.digon _ closedNodes[179]!.face _ (closed_node_admissible 179)
    (closed_node_admissible 180) (by native_decide)
  change closedEvaluation R 179 = ofList d * closedEvaluation R 180 at h
  rw [closed_value_180] at h
  have hc : closedValue 179 = mul d (closedValue 180) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_178 (R : ClosedSpiderReferences) :
    closedEvaluation R 178 = ofList (closedValue 178) := by
  have h := R.digon _ closedNodes[178]!.face _ (closed_node_admissible 178)
    (closed_node_admissible 179) (by native_decide)
  change closedEvaluation R 178 = ofList d * closedEvaluation R 179 at h
  rw [closed_value_179] at h
  have hc : closedValue 178 = mul d (closedValue 179) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_177 (R : ClosedSpiderReferences) :
    closedEvaluation R 177 = ofList (closedValue 177) := by
  have h := R.digon _ closedNodes[177]!.face _ (closed_node_admissible 177)
    (closed_node_admissible 178) (by native_decide)
  change closedEvaluation R 177 = ofList d * closedEvaluation R 178 at h
  rw [closed_value_178] at h
  have hc : closedValue 177 = mul d (closedValue 178) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_176 (R : ClosedSpiderReferences) :
    closedEvaluation R 176 = ofList (closedValue 176) := by
  have h := R.square _ closedNodes[176]!.face _ _ (closed_node_admissible 176)
    (closed_node_admissible 177) (closed_node_admissible 182) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 176 = closedEvaluation R 177 + closedEvaluation R 182 at h
  rw [closed_value_177,closed_value_182] at h
  have hc : closedValue 176 = add (closedValue 177) (closedValue 182) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_175 (R : ClosedSpiderReferences) :
    closedEvaluation R 175 = ofList (closedValue 175) := by
  have h := R.digon _ closedNodes[175]!.face _ (closed_node_admissible 175)
    (closed_node_admissible 176) (by native_decide)
  change closedEvaluation R 175 = ofList d * closedEvaluation R 176 at h
  rw [closed_value_176] at h
  have hc : closedValue 175 = mul d (closedValue 176) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_174 (R : ClosedSpiderReferences) :
    closedEvaluation R 174 = ofList (closedValue 174) := by
  have h := R.circles _ (closed_node_admissible 174) rfl rfl
  change closedEvaluation R 174 = ofList (pow e closedNodes[174]!.graph.circles) at h
  have hc : closedValue 174 = pow e closedNodes[174]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_173 (R : ClosedSpiderReferences) :
    closedEvaluation R 173 = ofList (closedValue 173) := by
  have h := R.digon _ closedNodes[173]!.face _ (closed_node_admissible 173)
    (closed_node_admissible 174) (by native_decide)
  change closedEvaluation R 173 = ofList d * closedEvaluation R 174 at h
  rw [closed_value_174] at h
  have hc : closedValue 173 = mul d (closedValue 174) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_172 (R : ClosedSpiderReferences) :
    closedEvaluation R 172 = ofList (closedValue 172) := by
  have h := R.digon _ closedNodes[172]!.face _ (closed_node_admissible 172)
    (closed_node_admissible 173) (by native_decide)
  change closedEvaluation R 172 = ofList d * closedEvaluation R 173 at h
  rw [closed_value_173] at h
  have hc : closedValue 172 = mul d (closedValue 173) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_171 (R : ClosedSpiderReferences) :
    closedEvaluation R 171 = ofList (closedValue 171) := by
  have h := R.circles _ (closed_node_admissible 171) rfl rfl
  change closedEvaluation R 171 = ofList (pow e closedNodes[171]!.graph.circles) at h
  have hc : closedValue 171 = pow e closedNodes[171]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_170 (R : ClosedSpiderReferences) :
    closedEvaluation R 170 = ofList (closedValue 170) := by
  have h := R.digon _ closedNodes[170]!.face _ (closed_node_admissible 170)
    (closed_node_admissible 171) (by native_decide)
  change closedEvaluation R 170 = ofList d * closedEvaluation R 171 at h
  rw [closed_value_171] at h
  have hc : closedValue 170 = mul d (closedValue 171) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_169 (R : ClosedSpiderReferences) :
    closedEvaluation R 169 = ofList (closedValue 169) := by
  have h := R.digon _ closedNodes[169]!.face _ (closed_node_admissible 169)
    (closed_node_admissible 170) (by native_decide)
  change closedEvaluation R 169 = ofList d * closedEvaluation R 170 at h
  rw [closed_value_170] at h
  have hc : closedValue 169 = mul d (closedValue 170) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_168 (R : ClosedSpiderReferences) :
    closedEvaluation R 168 = ofList (closedValue 168) := by
  have h := R.square _ closedNodes[168]!.face _ _ (closed_node_admissible 168)
    (closed_node_admissible 169) (closed_node_admissible 172) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 168 = closedEvaluation R 169 + closedEvaluation R 172 at h
  rw [closed_value_169,closed_value_172] at h
  have hc : closedValue 168 = add (closedValue 169) (closedValue 172) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_167 (R : ClosedSpiderReferences) :
    closedEvaluation R 167 = ofList (closedValue 167) := by
  have h := R.circles _ (closed_node_admissible 167) rfl rfl
  change closedEvaluation R 167 = ofList (pow e closedNodes[167]!.graph.circles) at h
  have hc : closedValue 167 = pow e closedNodes[167]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_166 (R : ClosedSpiderReferences) :
    closedEvaluation R 166 = ofList (closedValue 166) := by
  have h := R.digon _ closedNodes[166]!.face _ (closed_node_admissible 166)
    (closed_node_admissible 167) (by native_decide)
  change closedEvaluation R 166 = ofList d * closedEvaluation R 167 at h
  rw [closed_value_167] at h
  have hc : closedValue 166 = mul d (closedValue 167) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_165 (R : ClosedSpiderReferences) :
    closedEvaluation R 165 = ofList (closedValue 165) := by
  have h := R.digon _ closedNodes[165]!.face _ (closed_node_admissible 165)
    (closed_node_admissible 166) (by native_decide)
  change closedEvaluation R 165 = ofList d * closedEvaluation R 166 at h
  rw [closed_value_166] at h
  have hc : closedValue 165 = mul d (closedValue 166) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_164 (R : ClosedSpiderReferences) :
    closedEvaluation R 164 = ofList (closedValue 164) := by
  have h := R.digon _ closedNodes[164]!.face _ (closed_node_admissible 164)
    (closed_node_admissible 165) (by native_decide)
  change closedEvaluation R 164 = ofList d * closedEvaluation R 165 at h
  rw [closed_value_165] at h
  have hc : closedValue 164 = mul d (closedValue 165) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_163 (R : ClosedSpiderReferences) :
    closedEvaluation R 163 = ofList (closedValue 163) := by
  have h := R.digon _ closedNodes[163]!.face _ (closed_node_admissible 163)
    (closed_node_admissible 164) (by native_decide)
  change closedEvaluation R 163 = ofList d * closedEvaluation R 164 at h
  rw [closed_value_164] at h
  have hc : closedValue 163 = mul d (closedValue 164) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_162 (R : ClosedSpiderReferences) :
    closedEvaluation R 162 = ofList (closedValue 162) := by
  have h := R.square _ closedNodes[162]!.face _ _ (closed_node_admissible 162)
    (closed_node_admissible 163) (closed_node_admissible 168) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 162 = closedEvaluation R 163 + closedEvaluation R 168 at h
  rw [closed_value_163,closed_value_168] at h
  have hc : closedValue 162 = add (closedValue 163) (closedValue 168) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_161 (R : ClosedSpiderReferences) :
    closedEvaluation R 161 = ofList (closedValue 161) := by
  have h := R.digon _ closedNodes[161]!.face _ (closed_node_admissible 161)
    (closed_node_admissible 162) (by native_decide)
  change closedEvaluation R 161 = ofList d * closedEvaluation R 162 at h
  rw [closed_value_162] at h
  have hc : closedValue 161 = mul d (closedValue 162) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_160 (R : ClosedSpiderReferences) :
    closedEvaluation R 160 = ofList (closedValue 160) := by
  have h := R.square _ closedNodes[160]!.face _ _ (closed_node_admissible 160)
    (closed_node_admissible 161) (closed_node_admissible 175) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 160 = closedEvaluation R 161 + closedEvaluation R 175 at h
  rw [closed_value_161,closed_value_175] at h
  have hc : closedValue 160 = add (closedValue 161) (closedValue 175) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_159 (R : ClosedSpiderReferences) :
    closedEvaluation R 159 = ofList (closedValue 159) := by
  have h := R.circles _ (closed_node_admissible 159) rfl rfl
  change closedEvaluation R 159 = ofList (pow e closedNodes[159]!.graph.circles) at h
  have hc : closedValue 159 = pow e closedNodes[159]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_158 (R : ClosedSpiderReferences) :
    closedEvaluation R 158 = ofList (closedValue 158) := by
  have h := R.digon _ closedNodes[158]!.face _ (closed_node_admissible 158)
    (closed_node_admissible 159) (by native_decide)
  change closedEvaluation R 158 = ofList d * closedEvaluation R 159 at h
  rw [closed_value_159] at h
  have hc : closedValue 158 = mul d (closedValue 159) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_157 (R : ClosedSpiderReferences) :
    closedEvaluation R 157 = ofList (closedValue 157) := by
  have h := R.digon _ closedNodes[157]!.face _ (closed_node_admissible 157)
    (closed_node_admissible 158) (by native_decide)
  change closedEvaluation R 157 = ofList d * closedEvaluation R 158 at h
  rw [closed_value_158] at h
  have hc : closedValue 157 = mul d (closedValue 158) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_156 (R : ClosedSpiderReferences) :
    closedEvaluation R 156 = ofList (closedValue 156) := by
  have h := R.circles _ (closed_node_admissible 156) rfl rfl
  change closedEvaluation R 156 = ofList (pow e closedNodes[156]!.graph.circles) at h
  have hc : closedValue 156 = pow e closedNodes[156]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_155 (R : ClosedSpiderReferences) :
    closedEvaluation R 155 = ofList (closedValue 155) := by
  have h := R.digon _ closedNodes[155]!.face _ (closed_node_admissible 155)
    (closed_node_admissible 156) (by native_decide)
  change closedEvaluation R 155 = ofList d * closedEvaluation R 156 at h
  rw [closed_value_156] at h
  have hc : closedValue 155 = mul d (closedValue 156) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_154 (R : ClosedSpiderReferences) :
    closedEvaluation R 154 = ofList (closedValue 154) := by
  have h := R.digon _ closedNodes[154]!.face _ (closed_node_admissible 154)
    (closed_node_admissible 155) (by native_decide)
  change closedEvaluation R 154 = ofList d * closedEvaluation R 155 at h
  rw [closed_value_155] at h
  have hc : closedValue 154 = mul d (closedValue 155) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_153 (R : ClosedSpiderReferences) :
    closedEvaluation R 153 = ofList (closedValue 153) := by
  have h := R.square _ closedNodes[153]!.face _ _ (closed_node_admissible 153)
    (closed_node_admissible 154) (closed_node_admissible 157) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 153 = closedEvaluation R 154 + closedEvaluation R 157 at h
  rw [closed_value_154,closed_value_157] at h
  have hc : closedValue 153 = add (closedValue 154) (closedValue 157) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_152 (R : ClosedSpiderReferences) :
    closedEvaluation R 152 = ofList (closedValue 152) := by
  have h := R.circles _ (closed_node_admissible 152) rfl rfl
  change closedEvaluation R 152 = ofList (pow e closedNodes[152]!.graph.circles) at h
  have hc : closedValue 152 = pow e closedNodes[152]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_151 (R : ClosedSpiderReferences) :
    closedEvaluation R 151 = ofList (closedValue 151) := by
  have h := R.digon _ closedNodes[151]!.face _ (closed_node_admissible 151)
    (closed_node_admissible 152) (by native_decide)
  change closedEvaluation R 151 = ofList d * closedEvaluation R 152 at h
  rw [closed_value_152] at h
  have hc : closedValue 151 = mul d (closedValue 152) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_150 (R : ClosedSpiderReferences) :
    closedEvaluation R 150 = ofList (closedValue 150) := by
  have h := R.digon _ closedNodes[150]!.face _ (closed_node_admissible 150)
    (closed_node_admissible 151) (by native_decide)
  change closedEvaluation R 150 = ofList d * closedEvaluation R 151 at h
  rw [closed_value_151] at h
  have hc : closedValue 150 = mul d (closedValue 151) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_149 (R : ClosedSpiderReferences) :
    closedEvaluation R 149 = ofList (closedValue 149) := by
  have h := R.digon _ closedNodes[149]!.face _ (closed_node_admissible 149)
    (closed_node_admissible 150) (by native_decide)
  change closedEvaluation R 149 = ofList d * closedEvaluation R 150 at h
  rw [closed_value_150] at h
  have hc : closedValue 149 = mul d (closedValue 150) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_148 (R : ClosedSpiderReferences) :
    closedEvaluation R 148 = ofList (closedValue 148) := by
  have h := R.digon _ closedNodes[148]!.face _ (closed_node_admissible 148)
    (closed_node_admissible 149) (by native_decide)
  change closedEvaluation R 148 = ofList d * closedEvaluation R 149 at h
  rw [closed_value_149] at h
  have hc : closedValue 148 = mul d (closedValue 149) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_147 (R : ClosedSpiderReferences) :
    closedEvaluation R 147 = ofList (closedValue 147) := by
  have h := R.square _ closedNodes[147]!.face _ _ (closed_node_admissible 147)
    (closed_node_admissible 148) (closed_node_admissible 153) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 147 = closedEvaluation R 148 + closedEvaluation R 153 at h
  rw [closed_value_148,closed_value_153] at h
  have hc : closedValue 147 = add (closedValue 148) (closedValue 153) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_146 (R : ClosedSpiderReferences) :
    closedEvaluation R 146 = ofList (closedValue 146) := by
  have h := R.digon _ closedNodes[146]!.face _ (closed_node_admissible 146)
    (closed_node_admissible 147) (by native_decide)
  change closedEvaluation R 146 = ofList d * closedEvaluation R 147 at h
  rw [closed_value_147] at h
  have hc : closedValue 146 = mul d (closedValue 147) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_145 (R : ClosedSpiderReferences) :
    closedEvaluation R 145 = ofList (closedValue 145) := by
  have h := R.digon _ closedNodes[145]!.face _ (closed_node_admissible 145)
    (closed_node_admissible 146) (by native_decide)
  change closedEvaluation R 145 = ofList d * closedEvaluation R 146 at h
  rw [closed_value_146] at h
  have hc : closedValue 145 = mul d (closedValue 146) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_144 (R : ClosedSpiderReferences) :
    closedEvaluation R 144 = ofList (closedValue 144) := by
  have h := R.digon _ closedNodes[144]!.face _ (closed_node_admissible 144)
    (closed_node_admissible 145) (by native_decide)
  change closedEvaluation R 144 = ofList d * closedEvaluation R 145 at h
  rw [closed_value_145] at h
  have hc : closedValue 144 = mul d (closedValue 145) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_143 (R : ClosedSpiderReferences) :
    closedEvaluation R 143 = ofList (closedValue 143) := by
  have h := R.circles _ (closed_node_admissible 143) rfl rfl
  change closedEvaluation R 143 = ofList (pow e closedNodes[143]!.graph.circles) at h
  have hc : closedValue 143 = pow e closedNodes[143]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_142 (R : ClosedSpiderReferences) :
    closedEvaluation R 142 = ofList (closedValue 142) := by
  have h := R.digon _ closedNodes[142]!.face _ (closed_node_admissible 142)
    (closed_node_admissible 143) (by native_decide)
  change closedEvaluation R 142 = ofList d * closedEvaluation R 143 at h
  rw [closed_value_143] at h
  have hc : closedValue 142 = mul d (closedValue 143) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_141 (R : ClosedSpiderReferences) :
    closedEvaluation R 141 = ofList (closedValue 141) := by
  have h := R.digon _ closedNodes[141]!.face _ (closed_node_admissible 141)
    (closed_node_admissible 142) (by native_decide)
  change closedEvaluation R 141 = ofList d * closedEvaluation R 142 at h
  rw [closed_value_142] at h
  have hc : closedValue 141 = mul d (closedValue 142) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_140 (R : ClosedSpiderReferences) :
    closedEvaluation R 140 = ofList (closedValue 140) := by
  have h := R.circles _ (closed_node_admissible 140) rfl rfl
  change closedEvaluation R 140 = ofList (pow e closedNodes[140]!.graph.circles) at h
  have hc : closedValue 140 = pow e closedNodes[140]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_139 (R : ClosedSpiderReferences) :
    closedEvaluation R 139 = ofList (closedValue 139) := by
  have h := R.digon _ closedNodes[139]!.face _ (closed_node_admissible 139)
    (closed_node_admissible 140) (by native_decide)
  change closedEvaluation R 139 = ofList d * closedEvaluation R 140 at h
  rw [closed_value_140] at h
  have hc : closedValue 139 = mul d (closedValue 140) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_138 (R : ClosedSpiderReferences) :
    closedEvaluation R 138 = ofList (closedValue 138) := by
  have h := R.digon _ closedNodes[138]!.face _ (closed_node_admissible 138)
    (closed_node_admissible 139) (by native_decide)
  change closedEvaluation R 138 = ofList d * closedEvaluation R 139 at h
  rw [closed_value_139] at h
  have hc : closedValue 138 = mul d (closedValue 139) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_137 (R : ClosedSpiderReferences) :
    closedEvaluation R 137 = ofList (closedValue 137) := by
  have h := R.square _ closedNodes[137]!.face _ _ (closed_node_admissible 137)
    (closed_node_admissible 138) (closed_node_admissible 141) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 137 = closedEvaluation R 138 + closedEvaluation R 141 at h
  rw [closed_value_138,closed_value_141] at h
  have hc : closedValue 137 = add (closedValue 138) (closedValue 141) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_136 (R : ClosedSpiderReferences) :
    closedEvaluation R 136 = ofList (closedValue 136) := by
  have h := R.circles _ (closed_node_admissible 136) rfl rfl
  change closedEvaluation R 136 = ofList (pow e closedNodes[136]!.graph.circles) at h
  have hc : closedValue 136 = pow e closedNodes[136]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_135 (R : ClosedSpiderReferences) :
    closedEvaluation R 135 = ofList (closedValue 135) := by
  have h := R.digon _ closedNodes[135]!.face _ (closed_node_admissible 135)
    (closed_node_admissible 136) (by native_decide)
  change closedEvaluation R 135 = ofList d * closedEvaluation R 136 at h
  rw [closed_value_136] at h
  have hc : closedValue 135 = mul d (closedValue 136) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_134 (R : ClosedSpiderReferences) :
    closedEvaluation R 134 = ofList (closedValue 134) := by
  have h := R.digon _ closedNodes[134]!.face _ (closed_node_admissible 134)
    (closed_node_admissible 135) (by native_decide)
  change closedEvaluation R 134 = ofList d * closedEvaluation R 135 at h
  rw [closed_value_135] at h
  have hc : closedValue 134 = mul d (closedValue 135) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_133 (R : ClosedSpiderReferences) :
    closedEvaluation R 133 = ofList (closedValue 133) := by
  have h := R.digon _ closedNodes[133]!.face _ (closed_node_admissible 133)
    (closed_node_admissible 134) (by native_decide)
  change closedEvaluation R 133 = ofList d * closedEvaluation R 134 at h
  rw [closed_value_134] at h
  have hc : closedValue 133 = mul d (closedValue 134) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_132 (R : ClosedSpiderReferences) :
    closedEvaluation R 132 = ofList (closedValue 132) := by
  have h := R.digon _ closedNodes[132]!.face _ (closed_node_admissible 132)
    (closed_node_admissible 133) (by native_decide)
  change closedEvaluation R 132 = ofList d * closedEvaluation R 133 at h
  rw [closed_value_133] at h
  have hc : closedValue 132 = mul d (closedValue 133) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_131 (R : ClosedSpiderReferences) :
    closedEvaluation R 131 = ofList (closedValue 131) := by
  have h := R.square _ closedNodes[131]!.face _ _ (closed_node_admissible 131)
    (closed_node_admissible 132) (closed_node_admissible 137) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 131 = closedEvaluation R 132 + closedEvaluation R 137 at h
  rw [closed_value_132,closed_value_137] at h
  have hc : closedValue 131 = add (closedValue 132) (closedValue 137) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_130 (R : ClosedSpiderReferences) :
    closedEvaluation R 130 = ofList (closedValue 130) := by
  have h := R.digon _ closedNodes[130]!.face _ (closed_node_admissible 130)
    (closed_node_admissible 131) (by native_decide)
  change closedEvaluation R 130 = ofList d * closedEvaluation R 131 at h
  rw [closed_value_131] at h
  have hc : closedValue 130 = mul d (closedValue 131) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_129 (R : ClosedSpiderReferences) :
    closedEvaluation R 129 = ofList (closedValue 129) := by
  have h := R.circles _ (closed_node_admissible 129) rfl rfl
  change closedEvaluation R 129 = ofList (pow e closedNodes[129]!.graph.circles) at h
  have hc : closedValue 129 = pow e closedNodes[129]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_128 (R : ClosedSpiderReferences) :
    closedEvaluation R 128 = ofList (closedValue 128) := by
  have h := R.digon _ closedNodes[128]!.face _ (closed_node_admissible 128)
    (closed_node_admissible 129) (by native_decide)
  change closedEvaluation R 128 = ofList d * closedEvaluation R 129 at h
  rw [closed_value_129] at h
  have hc : closedValue 128 = mul d (closedValue 129) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_127 (R : ClosedSpiderReferences) :
    closedEvaluation R 127 = ofList (closedValue 127) := by
  have h := R.digon _ closedNodes[127]!.face _ (closed_node_admissible 127)
    (closed_node_admissible 128) (by native_decide)
  change closedEvaluation R 127 = ofList d * closedEvaluation R 128 at h
  rw [closed_value_128] at h
  have hc : closedValue 127 = mul d (closedValue 128) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_126 (R : ClosedSpiderReferences) :
    closedEvaluation R 126 = ofList (closedValue 126) := by
  have h := R.circles _ (closed_node_admissible 126) rfl rfl
  change closedEvaluation R 126 = ofList (pow e closedNodes[126]!.graph.circles) at h
  have hc : closedValue 126 = pow e closedNodes[126]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_125 (R : ClosedSpiderReferences) :
    closedEvaluation R 125 = ofList (closedValue 125) := by
  have h := R.digon _ closedNodes[125]!.face _ (closed_node_admissible 125)
    (closed_node_admissible 126) (by native_decide)
  change closedEvaluation R 125 = ofList d * closedEvaluation R 126 at h
  rw [closed_value_126] at h
  have hc : closedValue 125 = mul d (closedValue 126) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_124 (R : ClosedSpiderReferences) :
    closedEvaluation R 124 = ofList (closedValue 124) := by
  have h := R.digon _ closedNodes[124]!.face _ (closed_node_admissible 124)
    (closed_node_admissible 125) (by native_decide)
  change closedEvaluation R 124 = ofList d * closedEvaluation R 125 at h
  rw [closed_value_125] at h
  have hc : closedValue 124 = mul d (closedValue 125) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_123 (R : ClosedSpiderReferences) :
    closedEvaluation R 123 = ofList (closedValue 123) := by
  have h := R.square _ closedNodes[123]!.face _ _ (closed_node_admissible 123)
    (closed_node_admissible 124) (closed_node_admissible 127) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 123 = closedEvaluation R 124 + closedEvaluation R 127 at h
  rw [closed_value_124,closed_value_127] at h
  have hc : closedValue 123 = add (closedValue 124) (closedValue 127) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_122 (R : ClosedSpiderReferences) :
    closedEvaluation R 122 = ofList (closedValue 122) := by
  have h := R.circles _ (closed_node_admissible 122) rfl rfl
  change closedEvaluation R 122 = ofList (pow e closedNodes[122]!.graph.circles) at h
  have hc : closedValue 122 = pow e closedNodes[122]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_121 (R : ClosedSpiderReferences) :
    closedEvaluation R 121 = ofList (closedValue 121) := by
  have h := R.digon _ closedNodes[121]!.face _ (closed_node_admissible 121)
    (closed_node_admissible 122) (by native_decide)
  change closedEvaluation R 121 = ofList d * closedEvaluation R 122 at h
  rw [closed_value_122] at h
  have hc : closedValue 121 = mul d (closedValue 122) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_120 (R : ClosedSpiderReferences) :
    closedEvaluation R 120 = ofList (closedValue 120) := by
  have h := R.digon _ closedNodes[120]!.face _ (closed_node_admissible 120)
    (closed_node_admissible 121) (by native_decide)
  change closedEvaluation R 120 = ofList d * closedEvaluation R 121 at h
  rw [closed_value_121] at h
  have hc : closedValue 120 = mul d (closedValue 121) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_119 (R : ClosedSpiderReferences) :
    closedEvaluation R 119 = ofList (closedValue 119) := by
  have h := R.digon _ closedNodes[119]!.face _ (closed_node_admissible 119)
    (closed_node_admissible 120) (by native_decide)
  change closedEvaluation R 119 = ofList d * closedEvaluation R 120 at h
  rw [closed_value_120] at h
  have hc : closedValue 119 = mul d (closedValue 120) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_118 (R : ClosedSpiderReferences) :
    closedEvaluation R 118 = ofList (closedValue 118) := by
  have h := R.digon _ closedNodes[118]!.face _ (closed_node_admissible 118)
    (closed_node_admissible 119) (by native_decide)
  change closedEvaluation R 118 = ofList d * closedEvaluation R 119 at h
  rw [closed_value_119] at h
  have hc : closedValue 118 = mul d (closedValue 119) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_117 (R : ClosedSpiderReferences) :
    closedEvaluation R 117 = ofList (closedValue 117) := by
  have h := R.square _ closedNodes[117]!.face _ _ (closed_node_admissible 117)
    (closed_node_admissible 118) (closed_node_admissible 123) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 117 = closedEvaluation R 118 + closedEvaluation R 123 at h
  rw [closed_value_118,closed_value_123] at h
  have hc : closedValue 117 = add (closedValue 118) (closedValue 123) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_116 (R : ClosedSpiderReferences) :
    closedEvaluation R 116 = ofList (closedValue 116) := by
  have h := R.digon _ closedNodes[116]!.face _ (closed_node_admissible 116)
    (closed_node_admissible 117) (by native_decide)
  change closedEvaluation R 116 = ofList d * closedEvaluation R 117 at h
  rw [closed_value_117] at h
  have hc : closedValue 116 = mul d (closedValue 117) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_115 (R : ClosedSpiderReferences) :
    closedEvaluation R 115 = ofList (closedValue 115) := by
  have h := R.square _ closedNodes[115]!.face _ _ (closed_node_admissible 115)
    (closed_node_admissible 116) (closed_node_admissible 130) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 115 = closedEvaluation R 116 + closedEvaluation R 130 at h
  rw [closed_value_116,closed_value_130] at h
  have hc : closedValue 115 = add (closedValue 116) (closedValue 130) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_114 (R : ClosedSpiderReferences) :
    closedEvaluation R 114 = ofList (closedValue 114) := by
  have h := R.square _ closedNodes[114]!.face _ _ (closed_node_admissible 114)
    (closed_node_admissible 115) (closed_node_admissible 144) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 114 = closedEvaluation R 115 + closedEvaluation R 144 at h
  rw [closed_value_115,closed_value_144] at h
  have hc : closedValue 114 = add (closedValue 115) (closedValue 144) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_113 (R : ClosedSpiderReferences) :
    closedEvaluation R 113 = ofList (closedValue 113) := by
  have h := R.circles _ (closed_node_admissible 113) rfl rfl
  change closedEvaluation R 113 = ofList (pow e closedNodes[113]!.graph.circles) at h
  have hc : closedValue 113 = pow e closedNodes[113]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_112 (R : ClosedSpiderReferences) :
    closedEvaluation R 112 = ofList (closedValue 112) := by
  have h := R.digon _ closedNodes[112]!.face _ (closed_node_admissible 112)
    (closed_node_admissible 113) (by native_decide)
  change closedEvaluation R 112 = ofList d * closedEvaluation R 113 at h
  rw [closed_value_113] at h
  have hc : closedValue 112 = mul d (closedValue 113) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_111 (R : ClosedSpiderReferences) :
    closedEvaluation R 111 = ofList (closedValue 111) := by
  have h := R.digon _ closedNodes[111]!.face _ (closed_node_admissible 111)
    (closed_node_admissible 112) (by native_decide)
  change closedEvaluation R 111 = ofList d * closedEvaluation R 112 at h
  rw [closed_value_112] at h
  have hc : closedValue 111 = mul d (closedValue 112) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_110 (R : ClosedSpiderReferences) :
    closedEvaluation R 110 = ofList (closedValue 110) := by
  have h := R.digon _ closedNodes[110]!.face _ (closed_node_admissible 110)
    (closed_node_admissible 111) (by native_decide)
  change closedEvaluation R 110 = ofList d * closedEvaluation R 111 at h
  rw [closed_value_111] at h
  have hc : closedValue 110 = mul d (closedValue 111) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_109 (R : ClosedSpiderReferences) :
    closedEvaluation R 109 = ofList (closedValue 109) := by
  have h := R.digon _ closedNodes[109]!.face _ (closed_node_admissible 109)
    (closed_node_admissible 110) (by native_decide)
  change closedEvaluation R 109 = ofList d * closedEvaluation R 110 at h
  rw [closed_value_110] at h
  have hc : closedValue 109 = mul d (closedValue 110) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_108 (R : ClosedSpiderReferences) :
    closedEvaluation R 108 = ofList (closedValue 108) := by
  have h := R.digon _ closedNodes[108]!.face _ (closed_node_admissible 108)
    (closed_node_admissible 109) (by native_decide)
  change closedEvaluation R 108 = ofList d * closedEvaluation R 109 at h
  rw [closed_value_109] at h
  have hc : closedValue 108 = mul d (closedValue 109) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_107 (R : ClosedSpiderReferences) :
    closedEvaluation R 107 = ofList (closedValue 107) := by
  have h := R.circles _ (closed_node_admissible 107) rfl rfl
  change closedEvaluation R 107 = ofList (pow e closedNodes[107]!.graph.circles) at h
  have hc : closedValue 107 = pow e closedNodes[107]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_106 (R : ClosedSpiderReferences) :
    closedEvaluation R 106 = ofList (closedValue 106) := by
  have h := R.digon _ closedNodes[106]!.face _ (closed_node_admissible 106)
    (closed_node_admissible 107) (by native_decide)
  change closedEvaluation R 106 = ofList d * closedEvaluation R 107 at h
  rw [closed_value_107] at h
  have hc : closedValue 106 = mul d (closedValue 107) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_105 (R : ClosedSpiderReferences) :
    closedEvaluation R 105 = ofList (closedValue 105) := by
  have h := R.digon _ closedNodes[105]!.face _ (closed_node_admissible 105)
    (closed_node_admissible 106) (by native_decide)
  change closedEvaluation R 105 = ofList d * closedEvaluation R 106 at h
  rw [closed_value_106] at h
  have hc : closedValue 105 = mul d (closedValue 106) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_104 (R : ClosedSpiderReferences) :
    closedEvaluation R 104 = ofList (closedValue 104) := by
  have h := R.digon _ closedNodes[104]!.face _ (closed_node_admissible 104)
    (closed_node_admissible 105) (by native_decide)
  change closedEvaluation R 104 = ofList d * closedEvaluation R 105 at h
  rw [closed_value_105] at h
  have hc : closedValue 104 = mul d (closedValue 105) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_103 (R : ClosedSpiderReferences) :
    closedEvaluation R 103 = ofList (closedValue 103) := by
  have h := R.digon _ closedNodes[103]!.face _ (closed_node_admissible 103)
    (closed_node_admissible 104) (by native_decide)
  change closedEvaluation R 103 = ofList d * closedEvaluation R 104 at h
  rw [closed_value_104] at h
  have hc : closedValue 103 = mul d (closedValue 104) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_102 (R : ClosedSpiderReferences) :
    closedEvaluation R 102 = ofList (closedValue 102) := by
  have h := R.digon _ closedNodes[102]!.face _ (closed_node_admissible 102)
    (closed_node_admissible 103) (by native_decide)
  change closedEvaluation R 102 = ofList d * closedEvaluation R 103 at h
  rw [closed_value_103] at h
  have hc : closedValue 102 = mul d (closedValue 103) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_101 (R : ClosedSpiderReferences) :
    closedEvaluation R 101 = ofList (closedValue 101) := by
  have h := R.circles _ (closed_node_admissible 101) rfl rfl
  change closedEvaluation R 101 = ofList (pow e closedNodes[101]!.graph.circles) at h
  have hc : closedValue 101 = pow e closedNodes[101]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_100 (R : ClosedSpiderReferences) :
    closedEvaluation R 100 = ofList (closedValue 100) := by
  have h := R.digon _ closedNodes[100]!.face _ (closed_node_admissible 100)
    (closed_node_admissible 101) (by native_decide)
  change closedEvaluation R 100 = ofList d * closedEvaluation R 101 at h
  rw [closed_value_101] at h
  have hc : closedValue 100 = mul d (closedValue 101) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_99 (R : ClosedSpiderReferences) :
    closedEvaluation R 99 = ofList (closedValue 99) := by
  have h := R.digon _ closedNodes[99]!.face _ (closed_node_admissible 99)
    (closed_node_admissible 100) (by native_decide)
  change closedEvaluation R 99 = ofList d * closedEvaluation R 100 at h
  rw [closed_value_100] at h
  have hc : closedValue 99 = mul d (closedValue 100) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_98 (R : ClosedSpiderReferences) :
    closedEvaluation R 98 = ofList (closedValue 98) := by
  have h := R.circles _ (closed_node_admissible 98) rfl rfl
  change closedEvaluation R 98 = ofList (pow e closedNodes[98]!.graph.circles) at h
  have hc : closedValue 98 = pow e closedNodes[98]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_97 (R : ClosedSpiderReferences) :
    closedEvaluation R 97 = ofList (closedValue 97) := by
  have h := R.digon _ closedNodes[97]!.face _ (closed_node_admissible 97)
    (closed_node_admissible 98) (by native_decide)
  change closedEvaluation R 97 = ofList d * closedEvaluation R 98 at h
  rw [closed_value_98] at h
  have hc : closedValue 97 = mul d (closedValue 98) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_96 (R : ClosedSpiderReferences) :
    closedEvaluation R 96 = ofList (closedValue 96) := by
  have h := R.digon _ closedNodes[96]!.face _ (closed_node_admissible 96)
    (closed_node_admissible 97) (by native_decide)
  change closedEvaluation R 96 = ofList d * closedEvaluation R 97 at h
  rw [closed_value_97] at h
  have hc : closedValue 96 = mul d (closedValue 97) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_95 (R : ClosedSpiderReferences) :
    closedEvaluation R 95 = ofList (closedValue 95) := by
  have h := R.square _ closedNodes[95]!.face _ _ (closed_node_admissible 95)
    (closed_node_admissible 96) (closed_node_admissible 99) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 95 = closedEvaluation R 96 + closedEvaluation R 99 at h
  rw [closed_value_96,closed_value_99] at h
  have hc : closedValue 95 = add (closedValue 96) (closedValue 99) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_94 (R : ClosedSpiderReferences) :
    closedEvaluation R 94 = ofList (closedValue 94) := by
  have h := R.circles _ (closed_node_admissible 94) rfl rfl
  change closedEvaluation R 94 = ofList (pow e closedNodes[94]!.graph.circles) at h
  have hc : closedValue 94 = pow e closedNodes[94]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_93 (R : ClosedSpiderReferences) :
    closedEvaluation R 93 = ofList (closedValue 93) := by
  have h := R.digon _ closedNodes[93]!.face _ (closed_node_admissible 93)
    (closed_node_admissible 94) (by native_decide)
  change closedEvaluation R 93 = ofList d * closedEvaluation R 94 at h
  rw [closed_value_94] at h
  have hc : closedValue 93 = mul d (closedValue 94) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_92 (R : ClosedSpiderReferences) :
    closedEvaluation R 92 = ofList (closedValue 92) := by
  have h := R.digon _ closedNodes[92]!.face _ (closed_node_admissible 92)
    (closed_node_admissible 93) (by native_decide)
  change closedEvaluation R 92 = ofList d * closedEvaluation R 93 at h
  rw [closed_value_93] at h
  have hc : closedValue 92 = mul d (closedValue 93) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_91 (R : ClosedSpiderReferences) :
    closedEvaluation R 91 = ofList (closedValue 91) := by
  have h := R.digon _ closedNodes[91]!.face _ (closed_node_admissible 91)
    (closed_node_admissible 92) (by native_decide)
  change closedEvaluation R 91 = ofList d * closedEvaluation R 92 at h
  rw [closed_value_92] at h
  have hc : closedValue 91 = mul d (closedValue 92) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_90 (R : ClosedSpiderReferences) :
    closedEvaluation R 90 = ofList (closedValue 90) := by
  have h := R.digon _ closedNodes[90]!.face _ (closed_node_admissible 90)
    (closed_node_admissible 91) (by native_decide)
  change closedEvaluation R 90 = ofList d * closedEvaluation R 91 at h
  rw [closed_value_91] at h
  have hc : closedValue 90 = mul d (closedValue 91) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_89 (R : ClosedSpiderReferences) :
    closedEvaluation R 89 = ofList (closedValue 89) := by
  have h := R.square _ closedNodes[89]!.face _ _ (closed_node_admissible 89)
    (closed_node_admissible 90) (closed_node_admissible 95) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 89 = closedEvaluation R 90 + closedEvaluation R 95 at h
  rw [closed_value_90,closed_value_95] at h
  have hc : closedValue 89 = add (closedValue 90) (closedValue 95) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_88 (R : ClosedSpiderReferences) :
    closedEvaluation R 88 = ofList (closedValue 88) := by
  have h := R.digon _ closedNodes[88]!.face _ (closed_node_admissible 88)
    (closed_node_admissible 89) (by native_decide)
  change closedEvaluation R 88 = ofList d * closedEvaluation R 89 at h
  rw [closed_value_89] at h
  have hc : closedValue 88 = mul d (closedValue 89) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_87 (R : ClosedSpiderReferences) :
    closedEvaluation R 87 = ofList (closedValue 87) := by
  have h := R.digon _ closedNodes[87]!.face _ (closed_node_admissible 87)
    (closed_node_admissible 88) (by native_decide)
  change closedEvaluation R 87 = ofList d * closedEvaluation R 88 at h
  rw [closed_value_88] at h
  have hc : closedValue 87 = mul d (closedValue 88) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_86 (R : ClosedSpiderReferences) :
    closedEvaluation R 86 = ofList (closedValue 86) := by
  have h := R.digon _ closedNodes[86]!.face _ (closed_node_admissible 86)
    (closed_node_admissible 87) (by native_decide)
  change closedEvaluation R 86 = ofList d * closedEvaluation R 87 at h
  rw [closed_value_87] at h
  have hc : closedValue 86 = mul d (closedValue 87) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_85 (R : ClosedSpiderReferences) :
    closedEvaluation R 85 = ofList (closedValue 85) := by
  have h := R.digon _ closedNodes[85]!.face _ (closed_node_admissible 85)
    (closed_node_admissible 86) (by native_decide)
  change closedEvaluation R 85 = ofList d * closedEvaluation R 86 at h
  rw [closed_value_86] at h
  have hc : closedValue 85 = mul d (closedValue 86) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_84 (R : ClosedSpiderReferences) :
    closedEvaluation R 84 = ofList (closedValue 84) := by
  have h := R.digon _ closedNodes[84]!.face _ (closed_node_admissible 84)
    (closed_node_admissible 85) (by native_decide)
  change closedEvaluation R 84 = ofList d * closedEvaluation R 85 at h
  rw [closed_value_85] at h
  have hc : closedValue 84 = mul d (closedValue 85) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_83 (R : ClosedSpiderReferences) :
    closedEvaluation R 83 = ofList (closedValue 83) := by
  have h := R.digon _ closedNodes[83]!.face _ (closed_node_admissible 83)
    (closed_node_admissible 84) (by native_decide)
  change closedEvaluation R 83 = ofList d * closedEvaluation R 84 at h
  rw [closed_value_84] at h
  have hc : closedValue 83 = mul d (closedValue 84) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_82 (R : ClosedSpiderReferences) :
    closedEvaluation R 82 = ofList (closedValue 82) := by
  have h := R.circles _ (closed_node_admissible 82) rfl rfl
  change closedEvaluation R 82 = ofList (pow e closedNodes[82]!.graph.circles) at h
  have hc : closedValue 82 = pow e closedNodes[82]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_81 (R : ClosedSpiderReferences) :
    closedEvaluation R 81 = ofList (closedValue 81) := by
  have h := R.digon _ closedNodes[81]!.face _ (closed_node_admissible 81)
    (closed_node_admissible 82) (by native_decide)
  change closedEvaluation R 81 = ofList d * closedEvaluation R 82 at h
  rw [closed_value_82] at h
  have hc : closedValue 81 = mul d (closedValue 82) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_80 (R : ClosedSpiderReferences) :
    closedEvaluation R 80 = ofList (closedValue 80) := by
  have h := R.digon _ closedNodes[80]!.face _ (closed_node_admissible 80)
    (closed_node_admissible 81) (by native_decide)
  change closedEvaluation R 80 = ofList d * closedEvaluation R 81 at h
  rw [closed_value_81] at h
  have hc : closedValue 80 = mul d (closedValue 81) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_79 (R : ClosedSpiderReferences) :
    closedEvaluation R 79 = ofList (closedValue 79) := by
  have h := R.circles _ (closed_node_admissible 79) rfl rfl
  change closedEvaluation R 79 = ofList (pow e closedNodes[79]!.graph.circles) at h
  have hc : closedValue 79 = pow e closedNodes[79]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_78 (R : ClosedSpiderReferences) :
    closedEvaluation R 78 = ofList (closedValue 78) := by
  have h := R.digon _ closedNodes[78]!.face _ (closed_node_admissible 78)
    (closed_node_admissible 79) (by native_decide)
  change closedEvaluation R 78 = ofList d * closedEvaluation R 79 at h
  rw [closed_value_79] at h
  have hc : closedValue 78 = mul d (closedValue 79) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_77 (R : ClosedSpiderReferences) :
    closedEvaluation R 77 = ofList (closedValue 77) := by
  have h := R.digon _ closedNodes[77]!.face _ (closed_node_admissible 77)
    (closed_node_admissible 78) (by native_decide)
  change closedEvaluation R 77 = ofList d * closedEvaluation R 78 at h
  rw [closed_value_78] at h
  have hc : closedValue 77 = mul d (closedValue 78) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_76 (R : ClosedSpiderReferences) :
    closedEvaluation R 76 = ofList (closedValue 76) := by
  have h := R.square _ closedNodes[76]!.face _ _ (closed_node_admissible 76)
    (closed_node_admissible 77) (closed_node_admissible 80) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 76 = closedEvaluation R 77 + closedEvaluation R 80 at h
  rw [closed_value_77,closed_value_80] at h
  have hc : closedValue 76 = add (closedValue 77) (closedValue 80) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_75 (R : ClosedSpiderReferences) :
    closedEvaluation R 75 = ofList (closedValue 75) := by
  have h := R.circles _ (closed_node_admissible 75) rfl rfl
  change closedEvaluation R 75 = ofList (pow e closedNodes[75]!.graph.circles) at h
  have hc : closedValue 75 = pow e closedNodes[75]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_74 (R : ClosedSpiderReferences) :
    closedEvaluation R 74 = ofList (closedValue 74) := by
  have h := R.digon _ closedNodes[74]!.face _ (closed_node_admissible 74)
    (closed_node_admissible 75) (by native_decide)
  change closedEvaluation R 74 = ofList d * closedEvaluation R 75 at h
  rw [closed_value_75] at h
  have hc : closedValue 74 = mul d (closedValue 75) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_73 (R : ClosedSpiderReferences) :
    closedEvaluation R 73 = ofList (closedValue 73) := by
  have h := R.digon _ closedNodes[73]!.face _ (closed_node_admissible 73)
    (closed_node_admissible 74) (by native_decide)
  change closedEvaluation R 73 = ofList d * closedEvaluation R 74 at h
  rw [closed_value_74] at h
  have hc : closedValue 73 = mul d (closedValue 74) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_72 (R : ClosedSpiderReferences) :
    closedEvaluation R 72 = ofList (closedValue 72) := by
  have h := R.digon _ closedNodes[72]!.face _ (closed_node_admissible 72)
    (closed_node_admissible 73) (by native_decide)
  change closedEvaluation R 72 = ofList d * closedEvaluation R 73 at h
  rw [closed_value_73] at h
  have hc : closedValue 72 = mul d (closedValue 73) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_71 (R : ClosedSpiderReferences) :
    closedEvaluation R 71 = ofList (closedValue 71) := by
  have h := R.digon _ closedNodes[71]!.face _ (closed_node_admissible 71)
    (closed_node_admissible 72) (by native_decide)
  change closedEvaluation R 71 = ofList d * closedEvaluation R 72 at h
  rw [closed_value_72] at h
  have hc : closedValue 71 = mul d (closedValue 72) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_70 (R : ClosedSpiderReferences) :
    closedEvaluation R 70 = ofList (closedValue 70) := by
  have h := R.square _ closedNodes[70]!.face _ _ (closed_node_admissible 70)
    (closed_node_admissible 71) (closed_node_admissible 76) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 70 = closedEvaluation R 71 + closedEvaluation R 76 at h
  rw [closed_value_71,closed_value_76] at h
  have hc : closedValue 70 = add (closedValue 71) (closedValue 76) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_69 (R : ClosedSpiderReferences) :
    closedEvaluation R 69 = ofList (closedValue 69) := by
  have h := R.digon _ closedNodes[69]!.face _ (closed_node_admissible 69)
    (closed_node_admissible 70) (by native_decide)
  change closedEvaluation R 69 = ofList d * closedEvaluation R 70 at h
  rw [closed_value_70] at h
  have hc : closedValue 69 = mul d (closedValue 70) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_68 (R : ClosedSpiderReferences) :
    closedEvaluation R 68 = ofList (closedValue 68) := by
  have h := R.circles _ (closed_node_admissible 68) rfl rfl
  change closedEvaluation R 68 = ofList (pow e closedNodes[68]!.graph.circles) at h
  have hc : closedValue 68 = pow e closedNodes[68]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_67 (R : ClosedSpiderReferences) :
    closedEvaluation R 67 = ofList (closedValue 67) := by
  have h := R.digon _ closedNodes[67]!.face _ (closed_node_admissible 67)
    (closed_node_admissible 68) (by native_decide)
  change closedEvaluation R 67 = ofList d * closedEvaluation R 68 at h
  rw [closed_value_68] at h
  have hc : closedValue 67 = mul d (closedValue 68) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_66 (R : ClosedSpiderReferences) :
    closedEvaluation R 66 = ofList (closedValue 66) := by
  have h := R.digon _ closedNodes[66]!.face _ (closed_node_admissible 66)
    (closed_node_admissible 67) (by native_decide)
  change closedEvaluation R 66 = ofList d * closedEvaluation R 67 at h
  rw [closed_value_67] at h
  have hc : closedValue 66 = mul d (closedValue 67) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_65 (R : ClosedSpiderReferences) :
    closedEvaluation R 65 = ofList (closedValue 65) := by
  have h := R.circles _ (closed_node_admissible 65) rfl rfl
  change closedEvaluation R 65 = ofList (pow e closedNodes[65]!.graph.circles) at h
  have hc : closedValue 65 = pow e closedNodes[65]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_64 (R : ClosedSpiderReferences) :
    closedEvaluation R 64 = ofList (closedValue 64) := by
  have h := R.digon _ closedNodes[64]!.face _ (closed_node_admissible 64)
    (closed_node_admissible 65) (by native_decide)
  change closedEvaluation R 64 = ofList d * closedEvaluation R 65 at h
  rw [closed_value_65] at h
  have hc : closedValue 64 = mul d (closedValue 65) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_63 (R : ClosedSpiderReferences) :
    closedEvaluation R 63 = ofList (closedValue 63) := by
  have h := R.digon _ closedNodes[63]!.face _ (closed_node_admissible 63)
    (closed_node_admissible 64) (by native_decide)
  change closedEvaluation R 63 = ofList d * closedEvaluation R 64 at h
  rw [closed_value_64] at h
  have hc : closedValue 63 = mul d (closedValue 64) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_62 (R : ClosedSpiderReferences) :
    closedEvaluation R 62 = ofList (closedValue 62) := by
  have h := R.square _ closedNodes[62]!.face _ _ (closed_node_admissible 62)
    (closed_node_admissible 63) (closed_node_admissible 66) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 62 = closedEvaluation R 63 + closedEvaluation R 66 at h
  rw [closed_value_63,closed_value_66] at h
  have hc : closedValue 62 = add (closedValue 63) (closedValue 66) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_61 (R : ClosedSpiderReferences) :
    closedEvaluation R 61 = ofList (closedValue 61) := by
  have h := R.circles _ (closed_node_admissible 61) rfl rfl
  change closedEvaluation R 61 = ofList (pow e closedNodes[61]!.graph.circles) at h
  have hc : closedValue 61 = pow e closedNodes[61]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_60 (R : ClosedSpiderReferences) :
    closedEvaluation R 60 = ofList (closedValue 60) := by
  have h := R.digon _ closedNodes[60]!.face _ (closed_node_admissible 60)
    (closed_node_admissible 61) (by native_decide)
  change closedEvaluation R 60 = ofList d * closedEvaluation R 61 at h
  rw [closed_value_61] at h
  have hc : closedValue 60 = mul d (closedValue 61) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_59 (R : ClosedSpiderReferences) :
    closedEvaluation R 59 = ofList (closedValue 59) := by
  have h := R.digon _ closedNodes[59]!.face _ (closed_node_admissible 59)
    (closed_node_admissible 60) (by native_decide)
  change closedEvaluation R 59 = ofList d * closedEvaluation R 60 at h
  rw [closed_value_60] at h
  have hc : closedValue 59 = mul d (closedValue 60) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_58 (R : ClosedSpiderReferences) :
    closedEvaluation R 58 = ofList (closedValue 58) := by
  have h := R.digon _ closedNodes[58]!.face _ (closed_node_admissible 58)
    (closed_node_admissible 59) (by native_decide)
  change closedEvaluation R 58 = ofList d * closedEvaluation R 59 at h
  rw [closed_value_59] at h
  have hc : closedValue 58 = mul d (closedValue 59) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_57 (R : ClosedSpiderReferences) :
    closedEvaluation R 57 = ofList (closedValue 57) := by
  have h := R.digon _ closedNodes[57]!.face _ (closed_node_admissible 57)
    (closed_node_admissible 58) (by native_decide)
  change closedEvaluation R 57 = ofList d * closedEvaluation R 58 at h
  rw [closed_value_58] at h
  have hc : closedValue 57 = mul d (closedValue 58) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_56 (R : ClosedSpiderReferences) :
    closedEvaluation R 56 = ofList (closedValue 56) := by
  have h := R.square _ closedNodes[56]!.face _ _ (closed_node_admissible 56)
    (closed_node_admissible 57) (closed_node_admissible 62) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 56 = closedEvaluation R 57 + closedEvaluation R 62 at h
  rw [closed_value_57,closed_value_62] at h
  have hc : closedValue 56 = add (closedValue 57) (closedValue 62) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_55 (R : ClosedSpiderReferences) :
    closedEvaluation R 55 = ofList (closedValue 55) := by
  have h := R.digon _ closedNodes[55]!.face _ (closed_node_admissible 55)
    (closed_node_admissible 56) (by native_decide)
  change closedEvaluation R 55 = ofList d * closedEvaluation R 56 at h
  rw [closed_value_56] at h
  have hc : closedValue 55 = mul d (closedValue 56) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_54 (R : ClosedSpiderReferences) :
    closedEvaluation R 54 = ofList (closedValue 54) := by
  have h := R.square _ closedNodes[54]!.face _ _ (closed_node_admissible 54)
    (closed_node_admissible 55) (closed_node_admissible 69) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 54 = closedEvaluation R 55 + closedEvaluation R 69 at h
  rw [closed_value_55,closed_value_69] at h
  have hc : closedValue 54 = add (closedValue 55) (closedValue 69) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_53 (R : ClosedSpiderReferences) :
    closedEvaluation R 53 = ofList (closedValue 53) := by
  have h := R.digon _ closedNodes[53]!.face _ (closed_node_admissible 53)
    (closed_node_admissible 54) (by native_decide)
  change closedEvaluation R 53 = ofList d * closedEvaluation R 54 at h
  rw [closed_value_54] at h
  have hc : closedValue 53 = mul d (closedValue 54) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_52 (R : ClosedSpiderReferences) :
    closedEvaluation R 52 = ofList (closedValue 52) := by
  have h := R.digon _ closedNodes[52]!.face _ (closed_node_admissible 52)
    (closed_node_admissible 53) (by native_decide)
  change closedEvaluation R 52 = ofList d * closedEvaluation R 53 at h
  rw [closed_value_53] at h
  have hc : closedValue 52 = mul d (closedValue 53) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_51 (R : ClosedSpiderReferences) :
    closedEvaluation R 51 = ofList (closedValue 51) := by
  have h := R.digon _ closedNodes[51]!.face _ (closed_node_admissible 51)
    (closed_node_admissible 52) (by native_decide)
  change closedEvaluation R 51 = ofList d * closedEvaluation R 52 at h
  rw [closed_value_52] at h
  have hc : closedValue 51 = mul d (closedValue 52) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_50 (R : ClosedSpiderReferences) :
    closedEvaluation R 50 = ofList (closedValue 50) := by
  have h := R.digon _ closedNodes[50]!.face _ (closed_node_admissible 50)
    (closed_node_admissible 51) (by native_decide)
  change closedEvaluation R 50 = ofList d * closedEvaluation R 51 at h
  rw [closed_value_51] at h
  have hc : closedValue 50 = mul d (closedValue 51) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_49 (R : ClosedSpiderReferences) :
    closedEvaluation R 49 = ofList (closedValue 49) := by
  have h := R.circles _ (closed_node_admissible 49) rfl rfl
  change closedEvaluation R 49 = ofList (pow e closedNodes[49]!.graph.circles) at h
  have hc : closedValue 49 = pow e closedNodes[49]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_48 (R : ClosedSpiderReferences) :
    closedEvaluation R 48 = ofList (closedValue 48) := by
  have h := R.digon _ closedNodes[48]!.face _ (closed_node_admissible 48)
    (closed_node_admissible 49) (by native_decide)
  change closedEvaluation R 48 = ofList d * closedEvaluation R 49 at h
  rw [closed_value_49] at h
  have hc : closedValue 48 = mul d (closedValue 49) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_47 (R : ClosedSpiderReferences) :
    closedEvaluation R 47 = ofList (closedValue 47) := by
  have h := R.digon _ closedNodes[47]!.face _ (closed_node_admissible 47)
    (closed_node_admissible 48) (by native_decide)
  change closedEvaluation R 47 = ofList d * closedEvaluation R 48 at h
  rw [closed_value_48] at h
  have hc : closedValue 47 = mul d (closedValue 48) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_46 (R : ClosedSpiderReferences) :
    closedEvaluation R 46 = ofList (closedValue 46) := by
  have h := R.circles _ (closed_node_admissible 46) rfl rfl
  change closedEvaluation R 46 = ofList (pow e closedNodes[46]!.graph.circles) at h
  have hc : closedValue 46 = pow e closedNodes[46]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_45 (R : ClosedSpiderReferences) :
    closedEvaluation R 45 = ofList (closedValue 45) := by
  have h := R.digon _ closedNodes[45]!.face _ (closed_node_admissible 45)
    (closed_node_admissible 46) (by native_decide)
  change closedEvaluation R 45 = ofList d * closedEvaluation R 46 at h
  rw [closed_value_46] at h
  have hc : closedValue 45 = mul d (closedValue 46) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_44 (R : ClosedSpiderReferences) :
    closedEvaluation R 44 = ofList (closedValue 44) := by
  have h := R.digon _ closedNodes[44]!.face _ (closed_node_admissible 44)
    (closed_node_admissible 45) (by native_decide)
  change closedEvaluation R 44 = ofList d * closedEvaluation R 45 at h
  rw [closed_value_45] at h
  have hc : closedValue 44 = mul d (closedValue 45) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_43 (R : ClosedSpiderReferences) :
    closedEvaluation R 43 = ofList (closedValue 43) := by
  have h := R.square _ closedNodes[43]!.face _ _ (closed_node_admissible 43)
    (closed_node_admissible 44) (closed_node_admissible 47) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 43 = closedEvaluation R 44 + closedEvaluation R 47 at h
  rw [closed_value_44,closed_value_47] at h
  have hc : closedValue 43 = add (closedValue 44) (closedValue 47) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_42 (R : ClosedSpiderReferences) :
    closedEvaluation R 42 = ofList (closedValue 42) := by
  have h := R.circles _ (closed_node_admissible 42) rfl rfl
  change closedEvaluation R 42 = ofList (pow e closedNodes[42]!.graph.circles) at h
  have hc : closedValue 42 = pow e closedNodes[42]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_41 (R : ClosedSpiderReferences) :
    closedEvaluation R 41 = ofList (closedValue 41) := by
  have h := R.digon _ closedNodes[41]!.face _ (closed_node_admissible 41)
    (closed_node_admissible 42) (by native_decide)
  change closedEvaluation R 41 = ofList d * closedEvaluation R 42 at h
  rw [closed_value_42] at h
  have hc : closedValue 41 = mul d (closedValue 42) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_40 (R : ClosedSpiderReferences) :
    closedEvaluation R 40 = ofList (closedValue 40) := by
  have h := R.digon _ closedNodes[40]!.face _ (closed_node_admissible 40)
    (closed_node_admissible 41) (by native_decide)
  change closedEvaluation R 40 = ofList d * closedEvaluation R 41 at h
  rw [closed_value_41] at h
  have hc : closedValue 40 = mul d (closedValue 41) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_39 (R : ClosedSpiderReferences) :
    closedEvaluation R 39 = ofList (closedValue 39) := by
  have h := R.digon _ closedNodes[39]!.face _ (closed_node_admissible 39)
    (closed_node_admissible 40) (by native_decide)
  change closedEvaluation R 39 = ofList d * closedEvaluation R 40 at h
  rw [closed_value_40] at h
  have hc : closedValue 39 = mul d (closedValue 40) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_38 (R : ClosedSpiderReferences) :
    closedEvaluation R 38 = ofList (closedValue 38) := by
  have h := R.digon _ closedNodes[38]!.face _ (closed_node_admissible 38)
    (closed_node_admissible 39) (by native_decide)
  change closedEvaluation R 38 = ofList d * closedEvaluation R 39 at h
  rw [closed_value_39] at h
  have hc : closedValue 38 = mul d (closedValue 39) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_37 (R : ClosedSpiderReferences) :
    closedEvaluation R 37 = ofList (closedValue 37) := by
  have h := R.square _ closedNodes[37]!.face _ _ (closed_node_admissible 37)
    (closed_node_admissible 38) (closed_node_admissible 43) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 37 = closedEvaluation R 38 + closedEvaluation R 43 at h
  rw [closed_value_38,closed_value_43] at h
  have hc : closedValue 37 = add (closedValue 38) (closedValue 43) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_36 (R : ClosedSpiderReferences) :
    closedEvaluation R 36 = ofList (closedValue 36) := by
  have h := R.digon _ closedNodes[36]!.face _ (closed_node_admissible 36)
    (closed_node_admissible 37) (by native_decide)
  change closedEvaluation R 36 = ofList d * closedEvaluation R 37 at h
  rw [closed_value_37] at h
  have hc : closedValue 36 = mul d (closedValue 37) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_35 (R : ClosedSpiderReferences) :
    closedEvaluation R 35 = ofList (closedValue 35) := by
  have h := R.digon _ closedNodes[35]!.face _ (closed_node_admissible 35)
    (closed_node_admissible 36) (by native_decide)
  change closedEvaluation R 35 = ofList d * closedEvaluation R 36 at h
  rw [closed_value_36] at h
  have hc : closedValue 35 = mul d (closedValue 36) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_34 (R : ClosedSpiderReferences) :
    closedEvaluation R 34 = ofList (closedValue 34) := by
  have h := R.digon _ closedNodes[34]!.face _ (closed_node_admissible 34)
    (closed_node_admissible 35) (by native_decide)
  change closedEvaluation R 34 = ofList d * closedEvaluation R 35 at h
  rw [closed_value_35] at h
  have hc : closedValue 34 = mul d (closedValue 35) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_33 (R : ClosedSpiderReferences) :
    closedEvaluation R 33 = ofList (closedValue 33) := by
  have h := R.circles _ (closed_node_admissible 33) rfl rfl
  change closedEvaluation R 33 = ofList (pow e closedNodes[33]!.graph.circles) at h
  have hc : closedValue 33 = pow e closedNodes[33]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_32 (R : ClosedSpiderReferences) :
    closedEvaluation R 32 = ofList (closedValue 32) := by
  have h := R.digon _ closedNodes[32]!.face _ (closed_node_admissible 32)
    (closed_node_admissible 33) (by native_decide)
  change closedEvaluation R 32 = ofList d * closedEvaluation R 33 at h
  rw [closed_value_33] at h
  have hc : closedValue 32 = mul d (closedValue 33) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_31 (R : ClosedSpiderReferences) :
    closedEvaluation R 31 = ofList (closedValue 31) := by
  have h := R.digon _ closedNodes[31]!.face _ (closed_node_admissible 31)
    (closed_node_admissible 32) (by native_decide)
  change closedEvaluation R 31 = ofList d * closedEvaluation R 32 at h
  rw [closed_value_32] at h
  have hc : closedValue 31 = mul d (closedValue 32) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_30 (R : ClosedSpiderReferences) :
    closedEvaluation R 30 = ofList (closedValue 30) := by
  have h := R.circles _ (closed_node_admissible 30) rfl rfl
  change closedEvaluation R 30 = ofList (pow e closedNodes[30]!.graph.circles) at h
  have hc : closedValue 30 = pow e closedNodes[30]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_29 (R : ClosedSpiderReferences) :
    closedEvaluation R 29 = ofList (closedValue 29) := by
  have h := R.digon _ closedNodes[29]!.face _ (closed_node_admissible 29)
    (closed_node_admissible 30) (by native_decide)
  change closedEvaluation R 29 = ofList d * closedEvaluation R 30 at h
  rw [closed_value_30] at h
  have hc : closedValue 29 = mul d (closedValue 30) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_28 (R : ClosedSpiderReferences) :
    closedEvaluation R 28 = ofList (closedValue 28) := by
  have h := R.digon _ closedNodes[28]!.face _ (closed_node_admissible 28)
    (closed_node_admissible 29) (by native_decide)
  change closedEvaluation R 28 = ofList d * closedEvaluation R 29 at h
  rw [closed_value_29] at h
  have hc : closedValue 28 = mul d (closedValue 29) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_27 (R : ClosedSpiderReferences) :
    closedEvaluation R 27 = ofList (closedValue 27) := by
  have h := R.square _ closedNodes[27]!.face _ _ (closed_node_admissible 27)
    (closed_node_admissible 28) (closed_node_admissible 31) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 27 = closedEvaluation R 28 + closedEvaluation R 31 at h
  rw [closed_value_28,closed_value_31] at h
  have hc : closedValue 27 = add (closedValue 28) (closedValue 31) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_26 (R : ClosedSpiderReferences) :
    closedEvaluation R 26 = ofList (closedValue 26) := by
  have h := R.circles _ (closed_node_admissible 26) rfl rfl
  change closedEvaluation R 26 = ofList (pow e closedNodes[26]!.graph.circles) at h
  have hc : closedValue 26 = pow e closedNodes[26]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_25 (R : ClosedSpiderReferences) :
    closedEvaluation R 25 = ofList (closedValue 25) := by
  have h := R.digon _ closedNodes[25]!.face _ (closed_node_admissible 25)
    (closed_node_admissible 26) (by native_decide)
  change closedEvaluation R 25 = ofList d * closedEvaluation R 26 at h
  rw [closed_value_26] at h
  have hc : closedValue 25 = mul d (closedValue 26) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_24 (R : ClosedSpiderReferences) :
    closedEvaluation R 24 = ofList (closedValue 24) := by
  have h := R.digon _ closedNodes[24]!.face _ (closed_node_admissible 24)
    (closed_node_admissible 25) (by native_decide)
  change closedEvaluation R 24 = ofList d * closedEvaluation R 25 at h
  rw [closed_value_25] at h
  have hc : closedValue 24 = mul d (closedValue 25) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_23 (R : ClosedSpiderReferences) :
    closedEvaluation R 23 = ofList (closedValue 23) := by
  have h := R.digon _ closedNodes[23]!.face _ (closed_node_admissible 23)
    (closed_node_admissible 24) (by native_decide)
  change closedEvaluation R 23 = ofList d * closedEvaluation R 24 at h
  rw [closed_value_24] at h
  have hc : closedValue 23 = mul d (closedValue 24) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_22 (R : ClosedSpiderReferences) :
    closedEvaluation R 22 = ofList (closedValue 22) := by
  have h := R.digon _ closedNodes[22]!.face _ (closed_node_admissible 22)
    (closed_node_admissible 23) (by native_decide)
  change closedEvaluation R 22 = ofList d * closedEvaluation R 23 at h
  rw [closed_value_23] at h
  have hc : closedValue 22 = mul d (closedValue 23) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_21 (R : ClosedSpiderReferences) :
    closedEvaluation R 21 = ofList (closedValue 21) := by
  have h := R.square _ closedNodes[21]!.face _ _ (closed_node_admissible 21)
    (closed_node_admissible 22) (closed_node_admissible 27) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 21 = closedEvaluation R 22 + closedEvaluation R 27 at h
  rw [closed_value_22,closed_value_27] at h
  have hc : closedValue 21 = add (closedValue 22) (closedValue 27) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_20 (R : ClosedSpiderReferences) :
    closedEvaluation R 20 = ofList (closedValue 20) := by
  have h := R.digon _ closedNodes[20]!.face _ (closed_node_admissible 20)
    (closed_node_admissible 21) (by native_decide)
  change closedEvaluation R 20 = ofList d * closedEvaluation R 21 at h
  rw [closed_value_21] at h
  have hc : closedValue 20 = mul d (closedValue 21) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_19 (R : ClosedSpiderReferences) :
    closedEvaluation R 19 = ofList (closedValue 19) := by
  have h := R.circles _ (closed_node_admissible 19) rfl rfl
  change closedEvaluation R 19 = ofList (pow e closedNodes[19]!.graph.circles) at h
  have hc : closedValue 19 = pow e closedNodes[19]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_18 (R : ClosedSpiderReferences) :
    closedEvaluation R 18 = ofList (closedValue 18) := by
  have h := R.digon _ closedNodes[18]!.face _ (closed_node_admissible 18)
    (closed_node_admissible 19) (by native_decide)
  change closedEvaluation R 18 = ofList d * closedEvaluation R 19 at h
  rw [closed_value_19] at h
  have hc : closedValue 18 = mul d (closedValue 19) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_17 (R : ClosedSpiderReferences) :
    closedEvaluation R 17 = ofList (closedValue 17) := by
  have h := R.digon _ closedNodes[17]!.face _ (closed_node_admissible 17)
    (closed_node_admissible 18) (by native_decide)
  change closedEvaluation R 17 = ofList d * closedEvaluation R 18 at h
  rw [closed_value_18] at h
  have hc : closedValue 17 = mul d (closedValue 18) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_16 (R : ClosedSpiderReferences) :
    closedEvaluation R 16 = ofList (closedValue 16) := by
  have h := R.circles _ (closed_node_admissible 16) rfl rfl
  change closedEvaluation R 16 = ofList (pow e closedNodes[16]!.graph.circles) at h
  have hc : closedValue 16 = pow e closedNodes[16]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_15 (R : ClosedSpiderReferences) :
    closedEvaluation R 15 = ofList (closedValue 15) := by
  have h := R.digon _ closedNodes[15]!.face _ (closed_node_admissible 15)
    (closed_node_admissible 16) (by native_decide)
  change closedEvaluation R 15 = ofList d * closedEvaluation R 16 at h
  rw [closed_value_16] at h
  have hc : closedValue 15 = mul d (closedValue 16) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_14 (R : ClosedSpiderReferences) :
    closedEvaluation R 14 = ofList (closedValue 14) := by
  have h := R.digon _ closedNodes[14]!.face _ (closed_node_admissible 14)
    (closed_node_admissible 15) (by native_decide)
  change closedEvaluation R 14 = ofList d * closedEvaluation R 15 at h
  rw [closed_value_15] at h
  have hc : closedValue 14 = mul d (closedValue 15) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_13 (R : ClosedSpiderReferences) :
    closedEvaluation R 13 = ofList (closedValue 13) := by
  have h := R.square _ closedNodes[13]!.face _ _ (closed_node_admissible 13)
    (closed_node_admissible 14) (closed_node_admissible 17) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 13 = closedEvaluation R 14 + closedEvaluation R 17 at h
  rw [closed_value_14,closed_value_17] at h
  have hc : closedValue 13 = add (closedValue 14) (closedValue 17) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_12 (R : ClosedSpiderReferences) :
    closedEvaluation R 12 = ofList (closedValue 12) := by
  have h := R.circles _ (closed_node_admissible 12) rfl rfl
  change closedEvaluation R 12 = ofList (pow e closedNodes[12]!.graph.circles) at h
  have hc : closedValue 12 = pow e closedNodes[12]!.graph.circles := by native_decide
  rw [hc]
  exact h

private theorem closed_value_11 (R : ClosedSpiderReferences) :
    closedEvaluation R 11 = ofList (closedValue 11) := by
  have h := R.digon _ closedNodes[11]!.face _ (closed_node_admissible 11)
    (closed_node_admissible 12) (by native_decide)
  change closedEvaluation R 11 = ofList d * closedEvaluation R 12 at h
  rw [closed_value_12] at h
  have hc : closedValue 11 = mul d (closedValue 12) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_10 (R : ClosedSpiderReferences) :
    closedEvaluation R 10 = ofList (closedValue 10) := by
  have h := R.digon _ closedNodes[10]!.face _ (closed_node_admissible 10)
    (closed_node_admissible 11) (by native_decide)
  change closedEvaluation R 10 = ofList d * closedEvaluation R 11 at h
  rw [closed_value_11] at h
  have hc : closedValue 10 = mul d (closedValue 11) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_9 (R : ClosedSpiderReferences) :
    closedEvaluation R 9 = ofList (closedValue 9) := by
  have h := R.digon _ closedNodes[9]!.face _ (closed_node_admissible 9)
    (closed_node_admissible 10) (by native_decide)
  change closedEvaluation R 9 = ofList d * closedEvaluation R 10 at h
  rw [closed_value_10] at h
  have hc : closedValue 9 = mul d (closedValue 10) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_8 (R : ClosedSpiderReferences) :
    closedEvaluation R 8 = ofList (closedValue 8) := by
  have h := R.digon _ closedNodes[8]!.face _ (closed_node_admissible 8)
    (closed_node_admissible 9) (by native_decide)
  change closedEvaluation R 8 = ofList d * closedEvaluation R 9 at h
  rw [closed_value_9] at h
  have hc : closedValue 8 = mul d (closedValue 9) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_7 (R : ClosedSpiderReferences) :
    closedEvaluation R 7 = ofList (closedValue 7) := by
  have h := R.square _ closedNodes[7]!.face _ _ (closed_node_admissible 7)
    (closed_node_admissible 8) (closed_node_admissible 13) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 7 = closedEvaluation R 8 + closedEvaluation R 13 at h
  rw [closed_value_8,closed_value_13] at h
  have hc : closedValue 7 = add (closedValue 8) (closedValue 13) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_6 (R : ClosedSpiderReferences) :
    closedEvaluation R 6 = ofList (closedValue 6) := by
  have h := R.digon _ closedNodes[6]!.face _ (closed_node_admissible 6)
    (closed_node_admissible 7) (by native_decide)
  change closedEvaluation R 6 = ofList d * closedEvaluation R 7 at h
  rw [closed_value_7] at h
  have hc : closedValue 6 = mul d (closedValue 7) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_5 (R : ClosedSpiderReferences) :
    closedEvaluation R 5 = ofList (closedValue 5) := by
  have h := R.square _ closedNodes[5]!.face _ _ (closed_node_admissible 5)
    (closed_node_admissible 6) (closed_node_admissible 20) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 5 = closedEvaluation R 6 + closedEvaluation R 20 at h
  rw [closed_value_6,closed_value_20] at h
  have hc : closedValue 5 = add (closedValue 6) (closedValue 20) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_4 (R : ClosedSpiderReferences) :
    closedEvaluation R 4 = ofList (closedValue 4) := by
  have h := R.square _ closedNodes[4]!.face _ _ (closed_node_admissible 4)
    (closed_node_admissible 5) (closed_node_admissible 34) rfl (by native_decide) (by native_decide)
  change closedEvaluation R 4 = closedEvaluation R 5 + closedEvaluation R 34 at h
  rw [closed_value_5,closed_value_34] at h
  have hc : closedValue 4 = add (closedValue 5) (closedValue 34) := by native_decide
  rw [hc,ofList_add]
  exact h

private theorem closed_value_3 (R : ClosedSpiderReferences) :
    closedEvaluation R 3 = ofList (closedValue 3) := by
  have h := R.digon _ closedNodes[3]!.face _ (closed_node_admissible 3)
    (closed_node_admissible 4) (by native_decide)
  change closedEvaluation R 3 = ofList d * closedEvaluation R 4 at h
  rw [closed_value_4] at h
  have hc : closedValue 3 = mul d (closedValue 4) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_2 (R : ClosedSpiderReferences) :
    closedEvaluation R 2 = ofList (closedValue 2) := by
  have h := R.digon _ closedNodes[2]!.face _ (closed_node_admissible 2)
    (closed_node_admissible 3) (by native_decide)
  change closedEvaluation R 2 = ofList d * closedEvaluation R 3 at h
  rw [closed_value_3] at h
  have hc : closedValue 2 = mul d (closedValue 3) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_1 (R : ClosedSpiderReferences) :
    closedEvaluation R 1 = ofList (closedValue 1) := by
  have h := R.digon _ closedNodes[1]!.face _ (closed_node_admissible 1)
    (closed_node_admissible 2) (by native_decide)
  change closedEvaluation R 1 = ofList d * closedEvaluation R 2 at h
  rw [closed_value_2] at h
  have hc : closedValue 1 = mul d (closedValue 2) := by native_decide
  rw [hc,ofList_mul]
  exact h

private theorem closed_value_0 (R : ClosedSpiderReferences) :
    closedEvaluation R 0 = ofList (closedValue 0) := by
  have h := R.digon _ closedNodes[0]!.face _ (closed_node_admissible 0)
    (closed_node_admissible 1) (by native_decide)
  change closedEvaluation R 0 = ofList d * closedEvaluation R 1 at h
  rw [closed_value_1] at h
  have hc : closedValue 0 = mul d (closedValue 1) := by native_decide
  rw [hc,ofList_mul]
  exact h

/-- All nine advertised closed evaluations follow from the actual reduction
forest: capped B, capped H, capped D, shortened prefix, tail and four cores. -/
theorem closed_atlas_evaluations (R : ClosedSpiderReferences) :
    closedRoots.map (closedEvaluation R) = closedTargets.map ofList := by
  change [closedEvaluation R 0, closedEvaluation R 50, closedEvaluation R 83, closedEvaluation R 102, closedEvaluation R 108, closedEvaluation R 114, closedEvaluation R 160, closedEvaluation R 189, closedEvaluation R 202] = _
  rw [closed_value_0, closed_value_50, closed_value_83, closed_value_102, closed_value_108, closed_value_114, closed_value_160, closed_value_189, closed_value_202]
  exact congrArg (List.map ofList) closed_scalar_values

#print axioms closed_atlas_evaluations
end WebMu.Revised.Atlas
