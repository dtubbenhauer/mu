import WebMu.Revised.Algebra

/-! Exact cancellation at the interface. No bar compatibility is required. -/
namespace WebMu.Revised.Algebra

def sumP : List Poly → Poly
  | [] => 0
  | x::xs => x + sumP xs

@[simp] theorem sumP_nil : sumP [] = 0 := rfl
@[simp] theorem sumP_cons (x : Poly) (xs : List Poly) : sumP (x::xs) = x + sumP xs := rfl

def total {ι : Type} (is : List ι) (f : ι → Poly) : Poly := sumP (is.map f)

@[simp] theorem total_nil {ι : Type} (f : ι → Poly) : total [] f = 0 := rfl
@[simp] theorem total_cons {ι : Type} (i : ι) (is : List ι) (f : ι → Poly) :
    total (i::is) f = f i + total is f := rfl

@[simp] theorem total_zero {ι : Type} (is : List ι) : total is (fun _ => 0) = 0 := by
  induction is <;> simp_all

theorem total_add {ι : Type} (is : List ι) (f g : ι → Poly) :
    total is (fun i => f i + g i) = total is f + total is g := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [total_cons, ih]
    apply poly_ext
    intro d
    simp only [coefficient_add]
    omega

theorem total_mul {ι : Type} (is : List ι) (f : ι → Poly) (a : Poly) :
    total is (fun i => f i * a) = total is f * a := by
  induction is <;> simp_all [poly_add_mul]

theorem mul_total {ι : Type} (is : List ι) (f : ι → Poly) (a : Poly) :
    total is (fun i => a * f i) = a * total is f := by
  simpa only [poly_mul_comm] using total_mul is f a

theorem total_swap {ι κ : Type} (is : List ι) (js : List κ) (f : ι → κ → Poly) :
    total is (fun i => total js (f i)) = total js (fun j => total is (fun i => f i j)) := by
  induction is with
  | nil => simp
  | cons i is ih => simp only [total_cons, ih, total_add]

theorem total_delta {ι : Type} [DecidableEq ι] (is : List ι) (hnd : is.Nodup)
    (j : ι) (a : Poly) :
    total is (fun i => if i = j then a else 0) = if j ∈ is then a else 0 := by
  induction is with
  | nil => simp
  | cons i is ih =>
    rw [List.nodup_cons] at hnd
    rw [total_cons, ih hnd.2]
    by_cases h : i = j
    · subst i; simp [hnd.1]
    · by_cases hj : j ∈ is
      · simp [h,hj]
      · simp [h,hj,Ne.symm h]

def action {ι : Type} (is : List ι) (a : ι → ι → Poly) (x : ι → Poly) (i : ι) : Poly :=
  total is (fun j => a i j * x j)

def matmul {ι : Type} (is : List ι) (a b : ι → ι → Poly) (i j : ι) : Poly :=
  total is (fun k => a i k * b k j)

def pairing {ι : Type} (is : List ι) (p x : ι → Poly) : Poly :=
  total is (fun i => p i * x i)

def rowmul {ι : Type} (is : List ι) (p : ι → Poly) (a : ι → ι → Poly) (j : ι) : Poly :=
  total is (fun i => p i * a i j)

theorem action_matmul {ι : Type} (is : List ι) (a b : ι → ι → Poly) (x : ι → Poly) :
    action is (matmul is a b) x = action is a (action is b x) := by
  funext i
  simp only [action, matmul]
  calc
    total is (fun j => total is (fun k => a i k * b k j) * x j) =
        total is (fun j => total is (fun k => (a i k * b k j) * x j)) := by
          simp only [total_mul]
    _ = total is (fun k => total is (fun j => (a i k * b k j) * x j)) := total_swap _ _ _
    _ = total is (fun k => a i k * total is (fun j => b k j * x j)) := by
          simp only [poly_mul_assoc, mul_total]

theorem pairing_rowmul {ι : Type} (is : List ι) (p : ι → Poly)
    (a : ι → ι → Poly) (x : ι → Poly) :
    pairing is (rowmul is p a) x = pairing is p (action is a x) := by
  simp only [pairing, rowmul, action]
  calc
    total is (fun j => total is (fun i => p i * a i j) * x j) =
        total is (fun j => total is (fun i => (p i * a i j) * x j)) := by
          simp only [total_mul]
    _ = total is (fun i => total is (fun j => (p i * a i j) * x j)) := total_swap _ _ _
    _ = total is (fun i => p i * total is (fun j => a i j * x j)) := by
          simp only [poly_mul_assoc, mul_total]

theorem action_identity {ι : Type} [DecidableEq ι] (is : List ι)
    (hnd : is.Nodup) (hall : ∀ i, i ∈ is) (x : ι → Poly) :
    action is (fun i j => if i = j then 1 else 0) x = x := by
  funext i
  simp only [action]
  have hf : (fun j => (if i = j then (1:Poly) else 0) * x j) =
      fun j => if j = i then x i else 0 := by
    funext j
    by_cases h : j = i
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hf,total_delta is hnd i,if_pos (hall i)]

def wordAction {ι ε : Type} (is : List ι) (a : ε → ι → ι → Poly)
    (q : ι → Poly) : List ε → ι → Poly
  | [] => q
  | e::es => action is (a e) (wordAction is a q es)

/-- Telescoping for arbitrary ordered exterior decorations. G need not preserve bar. -/
theorem gauge_word {ι ε : Type} [DecidableEq ι] (is : List ι)
    (hnd : is.Nodup) (hall : ∀ i, i ∈ is)
    (g gi : ι → ι → Poly)
    (hinv : matmul is gi g = fun i j => if i = j then 1 else 0)
    (a : ε → ι → ι → Poly) (q : ι → Poly) (es : List ε) :
    wordAction is (fun e => matmul is (matmul is g (a e)) gi) (action is g q) es =
      action is g (wordAction is a q es) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [wordAction, ih, action_matmul]
    rw [← action_matmul is gi g,hinv,action_identity is hnd hall]

theorem gauge_cancellation {ι ε : Type} [DecidableEq ι] (is : List ι)
    (hnd : is.Nodup) (hall : ∀ i, i ∈ is)
    (g gi : ι → ι → Poly)
    (hinv : matmul is gi g = fun i j => if i = j then 1 else 0)
    (p : ι → Poly) (a : ε → ι → ι → Poly) (q : ι → Poly) (es : List ε) :
    pairing is (rowmul is p gi)
      (wordAction is (fun e => matmul is (matmul is g (a e)) gi) (action is g q) es) =
      pairing is p (wordAction is a q es) := by
  rw [gauge_word is hnd hall g gi hinv, pairing_rowmul,
    ← action_matmul is gi g,hinv,action_identity is hnd hall]

end WebMu.Revised.Algebra
