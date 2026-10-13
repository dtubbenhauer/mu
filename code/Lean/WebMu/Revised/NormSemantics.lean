import WebMu.Revised.Gauge

/-! Finite coefficient semantics of iterated coordinate-norm contraction.
All sums are explicit finite lists. Local identities are premises of the generic
invariant-span theorem, to be discharged by the separately checked local certificate.
-/
namespace WebMu.Revised.NormSemantics
open Algebra

theorem sum_congr {ι : Type} (is : List ι) (f g : ι → Poly)
    (h : ∀ i, f i=g i) : total is f=total is g := congrArg (total is) (funext h)

theorem total_product {ι κ : Type} (is : List ι) (js : List κ)
    (f : ι → Poly) (g : κ → Poly) :
    total is f * total js g = total is (fun i => total js (fun j => f i*g j)) := by
  rw [← total_mul]
  apply sum_congr
  intro i
  rw [mul_total]

theorem total_append {ι : Type} (is js : List ι) (f : ι → Poly) :
    total (is++js) f=total is f+total js f := by
  induction is with
  | nil => simp
  | cons i is ih => simp [ih, poly_add_assoc]

theorem total_map {ι κ : Type} (is : List ι) (g : ι → κ) (f : κ → Poly) :
    total (is.map g) f=total is (fun i => f (g i)) := by
  induction is <;> simp_all

theorem total_flatMap {ι κ : Type} (is : List ι) (g : ι → List κ) (f : κ → Poly) :
    total (is.flatMap g) f=total is (fun i => total (g i) f) := by
  induction is with
  | nil => simp
  | cons i is ih => simp [List.flatMap_cons, total_append, ih]

theorem mul_left_comm (a b c : Poly) : a*(b*c)=b*(a*c) := by
  rw [← poly_mul_assoc, poly_mul_comm a b, poly_mul_assoc]

def gram {ξ ι : Type} (ls : List ξ) (f : ξ → ι → Poly) (i j : ι) : Poly :=
  total ls (fun l => f l i*f l j)

def rightMap {ι κ : Type} (is : List ι) (f : ι → Poly)
    (a : ι → κ → Poly) (j : κ) : Poly := total is (fun i => f i*a i j)

def pullback {ι κ : Type} (is : List ι) (a : ι → κ → Poly)
    (x : ι → ι → Poly) (j k : κ) : Poly :=
  total is (fun i => total is (fun l => a i j*x i l*a l k))

/-- Exact finite Gram transformation, including every cross term. -/
theorem gram_rightMap {ξ ι κ : Type} (ls : List ξ) (is : List ι)
    (f : ξ → ι → Poly) (a : ι → κ → Poly) :
    gram ls (fun l => rightMap is (f l) a) = pullback is a (gram ls f) := by
  funext j k
  simp only [gram, rightMap, pullback, total_product]
  rw [total_swap ls is]
  apply sum_congr
  intro i
  rw [total_swap ls is]
  apply sum_congr
  intro l
  rw [← mul_total, ← total_mul]
  apply sum_congr
  intro h
  simp only [poly_mul_comm, mul_left_comm]

def normStep {ι ε : Type} (is : List ι) (es : List ε)
    (a : ε → ι → ι → Poly) (x : ι → ι → Poly) (i j : ι) : Poly :=
  total es (fun e => pullback is (a e) x i j)

def normReadout {ι ω : Type} (is : List ι) (ws : List ω)
    (q : ω → ι → Poly) (x : ι → ι → Poly) : Poly :=
  total ws (fun w => pullback is (fun i (_ : Unit) => q w i) x () ())

def History (α ε : Type) : Nat → Type
  | 0 => α
  | n+1 => History α ε n × ε

def histories {α ε : Type} (as : List α) (es : List ε) : (n : Nat) → List (History α ε n)
  | 0 => as
  | n+1 => (histories as es n).flatMap (fun h => es.map (fun e => (h,e)))

def rowCoordinates {α ε ι : Type} (is : List ι) (p : α → ι → Poly)
    (a : ε → ι → ι → Poly) : (n : Nat) → History α ε n → ι → Poly
  | 0, h => p h
  | n+1, (h,e) => rightMap is (rowCoordinates is p a n h) (a e)

def normIterate {ι ε : Type} (is : List ι) (es : List ε)
    (a : ε → ι → ι → Poly) (x : ι → ι → Poly) : Nat → ι → ι → Poly
  | 0 => x
  | n+1 => normStep is es a (normIterate is es a x n)

theorem gram_successor {α ε ι : Type} (is : List ι) (as : List α) (es : List ε)
    (p : α → ι → Poly) (a : ε → ι → ι → Poly) (n : Nat) :
    gram (histories as es (n+1)) (rowCoordinates is p a (n+1)) =
      normStep is es a (gram (histories as es n) (rowCoordinates is p a n)) := by
  funext i j
  simp only [gram, histories, total_flatMap, total_map, rowCoordinates, normStep]
  rw [total_swap]
  apply sum_congr
  intro e
  exact congrFun (congrFun (gram_rightMap (histories as es n) is
    (rowCoordinates is p a n) (a e)) i) j

/-- All-parameter matrix norm induction; no finite parameter sample is used. -/
theorem gram_iterate {α ε ι : Type} (is : List ι) (as : List α) (es : List ε)
    (p : α → ι → Poly) (a : ε → ι → ι → Poly) (n : Nat) :
    gram (histories as es n) (rowCoordinates is p a n) =
      normIterate is es a (gram as p) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gram_successor, ih]; rfl

def fullNorm {α ε ι ω : Type} (is : List ι) (as : List α) (es : List ε) (ws : List ω)
    (p : α → ι → Poly) (a : ε → ι → ι → Poly) (q : ω → ι → Poly) (n : Nat) : Poly :=
  total (histories as es n) (fun h => total ws (fun w =>
    let c := rightMap is (rowCoordinates is p a n h) (fun i (_ : Unit) => q w i) ()
    c*c))

/-- The norm of the full tensor equals L N^m(X0), with X0=PᵀP. -/
theorem full_norm_contraction {α ε ι ω : Type}
    (is : List ι) (as : List α) (es : List ε) (ws : List ω)
    (p : α → ι → Poly) (a : ε → ι → ι → Poly) (q : ω → ι → Poly) (n : Nat) :
    fullNorm is as es ws p a q n = normReadout is ws q
      (normIterate is es a (gram as p) n) := by
  unfold fullNorm normReadout
  rw [total_swap]
  apply sum_congr
  intro w
  have hh := congrFun (congrFun (gram_rightMap (histories as es n) is
    (rowCoordinates is p a n) (fun i (_ : Unit) => q w i)) ()) ()
  rw [gram_iterate] at hh
  exact hh

def historyInitial {α ε : Type} : (n : Nat) → History α ε n → α
  | 0, h => h
  | n+1, (h,_) => historyInitial n h

def historyBlocks {α ε : Type} : (n : Nat) → History α ε n → List ε
  | 0, _ => []
  | n+1, (h,e) => historyBlocks n h ++ [e]

def rowWord {ι ε : Type} (is : List ι) (p : ι → Poly)
    (a : ε → ι → ι → Poly) (es : List ε) : ι → Poly :=
  es.foldl (fun row e => rightMap is row (a e)) p

theorem rowCoordinates_history {α ε ι : Type} (is : List ι)
    (p : α → ι → Poly) (a : ε → ι → ι → Poly) (n : Nat) (h : History α ε n) :
    rowCoordinates is p a n h =
      rowWord is (p (historyInitial n h)) a (historyBlocks n h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h with ⟨h,e⟩
    simp only [rowCoordinates, historyInitial, historyBlocks, rowWord, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [ih h]
    rfl

theorem rowWord_pairing {ι ε : Type} (is : List ι) (p q : ι → Poly)
    (a : ε → ι → ι → Poly) (es : List ε) :
    pairing is (rowWord is p a es) q = pairing is p (wordAction is a q es) := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    change pairing is (rowWord is (rightMap is p (a e)) a es) q = _
    rw [ih]
    exact pairing_rowmul is p (a e) (wordAction is a q es)

/-- Every squared coefficient in fullNorm is the coefficient of the ordered
prefix-blocks-tail tensor, not of a reordered construction. -/
theorem full_coordinate_history {α ε ι ω : Type} (is : List ι)
    (p : α → ι → Poly) (a : ε → ι → ι → Poly) (q : ω → ι → Poly)
    (n : Nat) (h : History α ε n) (w : ω) :
    rightMap is (rowCoordinates is p a n h) (fun i (_ : Unit) => q w i) () =
      pairing is (p (historyInitial n h)) (wordAction is a (q w) (historyBlocks n h)) := by
  rw [rowCoordinates_history]
  exact rowWord_pairing is _ (q w) a _

def combine {κ ι : Type} (ks : List κ) (basis : κ → ι → ι → Poly)
    (c : κ → Poly) (i j : ι) : Poly := total ks (fun k => c k*basis k i j)

theorem pullback_combine {κ ι ξ : Type} (is : List ι) (ks : List κ)
    (a : ι → ξ → Poly) (basis : κ → ι → ι → Poly) (c : κ → Poly) :
    pullback is a (combine ks basis c) = combine ks (fun k => pullback is a (basis k)) c := by
  funext i j
  simp only [pullback, combine]
  have he : ∀ u v, a u i*total ks (fun k => c k*basis k u v)*a v j =
      total ks (fun k => c k*(a u i*basis k u v*a v j)) := by
    intro u v
    rw [← mul_total, ← total_mul]
    apply sum_congr
    intro k
    simp only [poly_mul_comm, mul_left_comm]
  simp only [he]
  calc
    total is (fun u => total is (fun v => total ks (fun k => c k*(a u i*basis k u v*a v j)))) =
        total is (fun u => total ks (fun k => total is (fun v => c k*(a u i*basis k u v*a v j)))) := by
          apply sum_congr
          intro u
          exact total_swap is ks _
    _ = total ks (fun k => total is (fun u => total is (fun v => c k*(a u i*basis k u v*a v j)))) :=
      total_swap is ks _
    _ = total ks (fun k => c k*total is (fun u => total is (fun v => a u i*basis k u v*a v j))) := by
      simp only [mul_total]

theorem normStep_combine {κ ι ε : Type} (is : List ι) (es : List ε) (ks : List κ)
    (a : ε → ι → ι → Poly) (basis : κ → ι → ι → Poly) (c : κ → Poly) :
    normStep is es a (combine ks basis c) =
      combine ks (fun k => normStep is es a (basis k)) c := by
  funext i j
  simp only [normStep, pullback_combine, combine]
  rw [total_swap es ks]
  simp only [mul_total]

theorem normReadout_combine {κ ι ω : Type} (is : List ι) (ws : List ω) (ks : List κ)
    (q : ω → ι → Poly) (basis : κ → ι → ι → Poly) (c : κ → Poly) :
    normReadout is ws q (combine ks basis c) =
      total ks (fun k => c k*normReadout is ws q (basis k)) := by
  simp only [normReadout, pullback_combine, combine]
  rw [total_swap ws ks]
  simp only [mul_total]

theorem combine_combination {κ ι : Type} (ks : List κ)
    (basis : κ → ι → ι → Poly) (K : κ → κ → Poly) (c : κ → Poly) :
    combine ks (fun j => combine ks basis (fun i => K i j)) c =
      combine ks basis (action ks K c) := by
  funext i j
  simp only [combine, action, ← mul_total]
  rw [total_swap ks ks]
  apply sum_congr
  intro k
  rw [← total_mul]
  apply sum_congr
  intro l
  simp only [poly_mul_comm, mul_left_comm]

def coefficientIterate {κ : Type} (ks : List κ) (K : κ → κ → Poly)
    (initial : κ → Poly) : Nat → κ → Poly
  | 0 => initial
  | n+1 => action ks K (coefficientIterate ks K initial n)

/-- A finite local invariant-span certificate implies the all-parameter expansion. -/
theorem normIterate_in_span {κ ι ε : Type} (is : List ι) (es : List ε) (ks : List κ)
    (a : ε → ι → ι → Poly) (basis : κ → ι → ι → Poly) (K : κ → κ → Poly)
    (initial : κ → Poly) (x0 : ι → ι → Poly)
    (hinitial : x0=combine ks basis initial)
    (hstep : ∀ k, normStep is es a (basis k)=combine ks basis (fun j => K j k)) (n : Nat) :
    normIterate is es a x0 n = combine ks basis (coefficientIterate ks K initial n) := by
  induction n with
  | zero => exact hinitial
  | succ n ih =>
    simp only [normIterate, ih, normStep_combine, coefficientIterate]
    have hh : (fun k => normStep is es a (basis k)) =
        (fun k => combine ks basis (fun j => K j k)) := funext hstep
    rw [hh, combine_combination]

/-- The full tensor norm is b K^m a once the three finite contraction certificates
(initial, transfer, terminal) have been proved for the concrete local maps. -/
theorem full_norm_transfer {α ε ι ω κ : Type}
    (is : List ι) (as : List α) (es : List ε) (ws : List ω) (ks : List κ)
    (p : α → ι → Poly) (a : ε → ι → ι → Poly) (q : ω → ι → Poly)
    (basis : κ → ι → ι → Poly) (K : κ → κ → Poly) (initial terminal : κ → Poly)
    (hinitial : gram as p=combine ks basis initial)
    (hstep : ∀ k, normStep is es a (basis k)=combine ks basis (fun j => K j k))
    (hterminal : ∀ k, normReadout is ws q (basis k)=terminal k) (n : Nat) :
    fullNorm is as es ws p a q n =
      pairing ks terminal (coefficientIterate ks K initial n) := by
  rw [full_norm_contraction, normIterate_in_span is es ks a basis K initial (gram as p)
    hinitial hstep n, normReadout_combine]
  unfold pairing
  apply sum_congr
  intro k
  rw [hterminal, poly_mul_comm]

#print axioms full_norm_contraction
#print axioms full_norm_transfer
#print axioms full_coordinate_history
end WebMu.Revised.NormSemantics
