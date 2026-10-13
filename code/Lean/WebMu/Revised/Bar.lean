import WebMu.RevisedLocal

/-! Signed spider circuits for the original construction.  No gauge matrix
occurs in this file.  The reference interface states the generic naturality
rules for the tensor-product bar, not invariance of this paper's tensors.

`OriginalBar.lean` proves that this circuit evaluates to the unchanged tensor
contraction, and transfers the resulting fixedness to its standard coordinates. -/
namespace WebMu.Revised.Bar

abbrev Signs := List Bool
def positive (n : Nat) : Signs := List.replicate n true

/-- A signed spider expression.  All compositions and tensor products are typed. -/
inductive Circuit : Signs → Signs → Type where
  | identity (s : Signs) : Circuit s s
  | down (s t : Signs) (steps : List Step)
      (valid : steps.foldlM descendSigns t = some s) : Circuit s t
  | up (s t : Signs) (steps : List Step)
      (valid : steps.foldlM ascendSigns s = some t) : Circuit s t
  | compose {r s t : Signs} : Circuit r s → Circuit s t → Circuit r t
  | tensor {r s t u : Signs} : Circuit r s → Circuit t u → Circuit (r++t) (s++u)
  | add {s t : Signs} : Circuit s t → Circuit s t → Circuit s t
  | neg {s t : Signs} : Circuit s t → Circuit s t
  | scaleD {s t : Signs} : Circuit s t → Circuit s t
  | zero (s t : Signs) : Circuit s t

/-- Cast only a proved equality of ordered boundary lists. -/
def Circuit.cast {s t s' t' : Signs} (hs : s = s') (ht : t = t')
    (f : Circuit s t) : Circuit s' t' := hs ▸ ht ▸ f

/-- Sparse linear extension of a map specified on tensor words. -/
def bindSparse (x : Tensor) (f : Word → Tensor) : Tensor :=
  x.fold (fun out w p => (f w).fold
    (fun result v q => accumulate result v (Laurent.mul q p)) out) ∅

/-- Exact elementary-table evaluation; words retain their left-to-right order. -/
def evalSparse {s t : Signs} : Circuit s t → Word → Tensor
  | .identity _ => singleton
  | .down _ _ steps _ => fun w => expand steps (singleton w)
  | .up _ _ steps _ => fun w => WebMu.compose steps (singleton w)
  | .compose f g => fun w => bindSparse (evalSparse f w) (evalSparse g)
  | @Circuit.tensor r _ _ _ f g => fun w =>
      tensorProduct (evalSparse f (w.take r.length)) (evalSparse g (w.drop r.length))
  | .add f g => fun w => sumTensor [evalSparse f w, evalSparse g w]
  | .neg f => fun w => scaleTensor (evalSparse f w) (Laurent.monomial 0 (-1))
  | .scaleD f => fun w => scaleTensor (evalSparse f w) d
  | .zero _ _ => fun _ => ∅

def prefixCircuit : Circuit (positive 3) (positive 6) :=
  .down _ _ shortPrefixSteps (by decide)

def bCircuit : Circuit (positive 3) (positive 3 ++ positive 9) :=
  .down _ _ blockSteps (by decide)

def qCircuit : Circuit [] (positive 3 ++ positive 6) :=
  .down _ _ tailSteps (by decide)

def cupCircuit (s : Bool) : Circuit [] [s,!s] :=
  .down _ _ [(.cup,0)] (by cases s <;> decide)

def fourCupCircuit : Circuit [] [true,false,false,true,true,false,false,true] :=
  .tensor (.tensor (cupCircuit true) (cupCircuit false))
    (.tensor (cupCircuit true) (cupCircuit false))

def cCircuit : Circuit [] (positive 3 ++ positive 9) :=
  .compose fourCupCircuit (.down _ _ cSteps (by decide))

def tripodCircuit : Circuit [] (positive 3) :=
  .down _ _ [(.y,0),(.cup,0)] (by decide)

def tauTwoCircuit : Circuit [] (positive 6) := .tensor tripodCircuit tripodCircuit
def tauThreeCircuit : Circuit [] (positive 9) := .tensor tripodCircuit tauTwoCircuit

def correction (j : Fin 8) : List Step × List Step := correctionSteps[j.val]!
def correctionSigns (j : Fin 8) : Signs := (inputSigns 9 (correction j).1).getD []

theorem correction_down_type (j : Fin 8) :
    (correction j).1.foldlM descendSigns (positive 9) = some (correctionSigns j) := by
  revert j
  decide

theorem correction_up_type (j : Fin 8) :
    (correction j).2.foldlM ascendSigns (positive 3) = some (correctionSigns j) := by
  revert j
  decide

def correctionCircuit (j : Fin 8) : Circuit (positive 3) (positive 9) :=
  .compose (.up _ _ (correction j).2 (correction_up_type j))
    (.down _ _ (correction j).1 (correction_down_type j))

def circuitSum {s t : Signs} : List (Circuit s t) → Circuit s t
  | [] => .zero s t
  | f :: fs => .add f (circuitSum fs)

def dCircuit : Circuit (positive 3) (positive 9) :=
  circuitSum ((List.finRange 8).map correctionCircuit)

/-- The remaining exterior strands after n blocks, with their order retained. -/
def exterior : Nat → Signs
  | 0 => positive 6
  | m+1 => positive 9 ++ exterior m

def upNext {m : Nat} (upper : Circuit [] (positive 3 ++ exterior m))
    (lower : Circuit [] (exterior m)) : Circuit [] (positive 3 ++ exterior (m+1)) :=
  .add
    (.compose upper ((Circuit.tensor bCircuit (.identity (exterior m))).cast rfl
      (by simp [exterior, List.append_assoc])))
    (.compose lower ((Circuit.tensor (.neg cCircuit) (.identity (exterior m))).cast rfl
      (by simp [exterior, List.append_assoc])))

def lowNext {m : Nat} (upper : Circuit [] (positive 3 ++ exterior m))
    (lower : Circuit [] (exterior m)) : Circuit [] (exterior (m+1)) :=
  .add (.compose upper (.tensor dCircuit (.identity (exterior m))))
    (.compose lower (.tensor (.neg (.scaleD tauThreeCircuit)) (.identity (exterior m))))

/-- The original transfer is [B,-C; D,-d τ³], with tail [Q;τ²]. -/
def interfaceCircuit : (m : Nat) →
    Circuit [] (positive 3 ++ exterior m) × Circuit [] (exterior m)
  | 0 => (qCircuit, tauTwoCircuit)
  | m+1 => (upNext (interfaceCircuit m).1 (interfaceCircuit m).2,
      lowNext (interfaceCircuit m).1 (interfaceCircuit m).2)

def originalCircuit (m : Nat) : Circuit [] (positive 6 ++ exterior m) :=
  .compose (interfaceCircuit m).1 (.tensor prefixCircuit (.identity (exterior m)))

theorem exterior_length (m : Nat) : (exterior m).length = 9*m+6 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [exterior, positive, ih]; omega

theorem original_boundary_length (m : Nat) :
    (positive 6 ++ exterior m).length = 12+9*m := by
  simp [positive, exterior_length]
  omega

/-- Prior-work inputs: functoriality of the tensor bar on typed spider maps,
and its additive, negative, and d-scalar naturality.  Every field is uniform
in the boundary and the spider word.  No field mentions this paper's family. -/
structure BarReferences where
  Space : Signs → Type
  bar : (s : Signs) → Space s → Space s
  add : (s : Signs) → Space s → Space s → Space s
  neg : (s : Signs) → Space s → Space s
  scaleD : (s : Signs) → Space s → Space s
  zero : (s : Signs) → Space s
  vacuum : Space []
  downMap : (s t : Signs) → (steps : List Step) →
    steps.foldlM descendSigns t = some s → Space s → Space t
  upMap : (s t : Signs) → (steps : List Step) →
    steps.foldlM ascendSigns s = some t → Space s → Space t
  tensorMap : {r s t u : Signs} → (Space r → Space s) → (Space t → Space u) →
    Space (r++t) → Space (s++u)
  IsIntertwiner : {s t : Signs} → (Space s → Space t) → Prop
  identity_intertwiner : ∀ s, IsIntertwiner (id : Space s → Space s)
  down_intertwiner : ∀ s t steps valid, IsIntertwiner (downMap s t steps valid)
  up_intertwiner : ∀ s t steps valid, IsIntertwiner (upMap s t steps valid)
  compose_intertwiner : ∀ {r s t} (f : Space r → Space s) (g : Space s → Space t),
    IsIntertwiner f → IsIntertwiner g → IsIntertwiner (fun x => g (f x))
  tensor_intertwiner : ∀ {r s t u} (f : Space r → Space s) (g : Space t → Space u),
    IsIntertwiner f → IsIntertwiner g → IsIntertwiner (tensorMap f g)
  add_intertwiner : ∀ {s t} (f g : Space s → Space t),
    IsIntertwiner f → IsIntertwiner g → IsIntertwiner (fun x => add t (f x) (g x))
  neg_intertwiner : ∀ {s t} (f : Space s → Space t),
    IsIntertwiner f → IsIntertwiner (fun x => neg t (f x))
  scaleD_intertwiner : ∀ {s t} (f : Space s → Space t),
    IsIntertwiner f → IsIntertwiner (fun x => scaleD t (f x))
  zero_intertwiner : ∀ s t, IsIntertwiner (fun (_ : Space s) => zero t)
  bar_add : ∀ s x y, bar s (add s x y) = add s (bar s x) (bar s y)
  bar_neg : ∀ s x, bar s (neg s x) = neg s (bar s x)
  bar_scaleD : ∀ s x, bar s (scaleD s x) = scaleD s (bar s x)
  bar_zero : ∀ s, bar s (zero s) = zero s
  bar_vacuum : bar [] vacuum = vacuum
  down_natural : ∀ s t steps valid x,
    bar t (downMap s t steps valid x) = downMap s t steps valid (bar s x)
  up_natural : ∀ s t steps valid x,
    bar t (upMap s t steps valid x) = upMap s t steps valid (bar s x)
  tensor_natural : ∀ {r s t u} (f : Space r → Space s) (g : Space t → Space u),
    IsIntertwiner f → IsIntertwiner g →
    (∀ x, bar s (f x) = f (bar r x)) →
    (∀ x, bar u (g x) = g (bar t x)) →
    ∀ x, bar (s++u) (tensorMap f g x) = tensorMap f g (bar (r++t) x)

def BarReferences.interpret (R : BarReferences) {s t : Signs} :
    Circuit s t → R.Space s → R.Space t
  | .identity _ => id
  | .down s t steps valid => R.downMap s t steps valid
  | .up s t steps valid => R.upMap s t steps valid
  | .compose f g => fun x => R.interpret g (R.interpret f x)
  | .tensor f g => R.tensorMap (R.interpret f) (R.interpret g)
  | .add f g => fun x => R.add _ (R.interpret f x) (R.interpret g x)
  | .neg f => fun x => R.neg _ (R.interpret f x)
  | .scaleD f => fun x => R.scaleD _ (R.interpret f x)
  | .zero _ t => fun _ => R.zero t

theorem circuit_intertwiner (R : BarReferences) {s t : Signs} (f : Circuit s t) :
    R.IsIntertwiner (R.interpret f) := by
  induction f with
  | identity s => exact R.identity_intertwiner s
  | down s t steps valid => exact R.down_intertwiner s t steps valid
  | up s t steps valid => exact R.up_intertwiner s t steps valid
  | compose f g ihf ihg => exact R.compose_intertwiner (R.interpret f) (R.interpret g) ihf ihg
  | tensor f g ihf ihg => exact R.tensor_intertwiner _ _ ihf ihg
  | add f g ihf ihg => exact R.add_intertwiner _ _ ihf ihg
  | neg f ih => exact R.neg_intertwiner _ ih
  | scaleD f ih => exact R.scaleD_intertwiner _ ih
  | zero s t => exact R.zero_intertwiner s t

theorem circuit_natural (R : BarReferences) {s t : Signs} (f : Circuit s t)
    (x : R.Space s) :
    R.bar t (R.interpret f x) = R.interpret f (R.bar s x) := by
  induction f with
  | identity => rfl
  | down s t steps valid => exact R.down_natural s t steps valid x
  | up s t steps valid => exact R.up_natural s t steps valid x
  | compose f g ihf ihg =>
    simp only [BarReferences.interpret, ihg, ihf]
  | tensor f g ihf ihg =>
    exact R.tensor_natural (R.interpret f) (R.interpret g)
      (circuit_intertwiner R f) (circuit_intertwiner R g) ihf ihg x
  | add f g ihf ihg => simp only [BarReferences.interpret, R.bar_add, ihf, ihg]
  | neg f ih => simp only [BarReferences.interpret, R.bar_neg, ih]
  | scaleD f ih => simp only [BarReferences.interpret, R.bar_scaleD, ih]
  | zero => exact R.bar_zero _

/-- All m; only the original, signed, untransformed spider circuit is used. -/
theorem original_circuit_fixed (R : BarReferences) (m : Nat) :
    R.bar _ (R.interpret (originalCircuit m) R.vacuum) =
      R.interpret (originalCircuit m) R.vacuum := by
  rw [circuit_natural, R.bar_vacuum]

end WebMu.Revised.Bar
