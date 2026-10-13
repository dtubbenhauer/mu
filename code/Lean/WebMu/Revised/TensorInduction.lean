import WebMu.Revised.Lattice

namespace WebMu.Revised
open Laurent

/-- Ordered block decorations, read from the prefix toward the tail. -/
def wordIterate {ι ε : Type} (indices : List ι) (a : ε → ι → ι → Laurent)
    (q : ι → Laurent) : List ε → ι → Laurent
  | [] => q
  | e :: es => step indices (a e) (wordIterate indices a q es)

def intWordIterate {ι ε : Type} (indices : List ι) (a : ε → ι → ι → Int)
    (q : ι → Int) : List ε → ι → Int
  | [] => q
  | e :: es => intStep indices (a e) (intWordIterate indices a q es)

/-- The coefficient of a specified tensor word after the final prefix. -/
def tensorCoefficient {ι ε : Type} (indices : List ι) (p : ι → Laurent)
    (a : ε → ι → ι → Laurent) (q : ι → Laurent) (es : List ε) : Laurent :=
  Laurent.sum (indices.map (fun i => mul (p i) (wordIterate indices a q es i)))

theorem wordIterate_nonpositive {ι ε : Type} (indices : List ι)
    (a : ε → ι → ι → Laurent) (q : ι → Laurent)
    (ha : ∀ e i j, Nonpositive (a e i j)) (hq : ∀ i, Nonpositive (q i))
    (es : List ε) (i : ι) : Nonpositive (wordIterate indices a q es i) := by
  induction es generalizing i with
  | nil => exact hq i
  | cons e es ih => exact step_nonpositive indices (a e) _ (ha e) ih i

theorem wordIterate_constant {ι ε : Type} (indices : List ι)
    (a : ε → ι → ι → Laurent) (q : ι → Laurent)
    (ha : ∀ e i j, Nonpositive (a e i j)) (hq : ∀ i, Nonpositive (q i))
    (es : List ε) :
    (fun i => coeff (wordIterate indices a q es i) 0) =
      intWordIterate indices (fun e i j => coeff (a e i j) 0)
        (fun i => coeff (q i) 0) es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    funext i
    rw [wordIterate, step_constant indices (a e) _ (ha e)
      (wordIterate_nonpositive indices a q ha hq es), ih]
    rfl

theorem tensorCoefficient_nonpositive {ι ε : Type} (indices : List ι)
    (p : ι → Laurent) (a : ε → ι → ι → Laurent) (q : ι → Laurent)
    (hp : ∀ i, Nonpositive (p i)) (ha : ∀ e i j, Nonpositive (a e i j))
    (hq : ∀ i, Nonpositive (q i)) (es : List ε) :
    Nonpositive (tensorCoefficient indices p a q es) := by
  apply nonpositive_sum
  intro z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  exact nonpositive_mul _ _ (hp i) (wordIterate_nonpositive indices a q ha hq es i)

theorem sum_delta {ι : Type} [DecidableEq ι] (indices : List ι)
    (hnd : indices.Nodup) (s : ι) (f : ι → Int) :
    (indices.map (fun i => if i = s then f i else 0)).sum =
      if s ∈ indices then f s else 0 := by
  induction indices with
  | nil => simp
  | cons i is ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, ih hnd.2, List.mem_cons]
    by_cases h : i = s
    · subst i
      simp [hnd.1]
    · by_cases hs : s ∈ is
      · simp [h, hs]
      · have hn : s ≠ i := Ne.symm h
        simp [h, hn, hs]

theorem intStep_delta {ι : Type} [DecidableEq ι] (indices : List ι)
    (hnd : indices.Nodup) (s : ι) (hs : s ∈ indices)
    (a : ι → ι → Int) (z : Int) (i : ι) :
    intStep indices a (fun j => if j = s then z else 0) i = a i s * z := by
  simp only [intStep]
  have h : (fun j => a i j * if j = s then z else 0) =
      (fun j => if j = s then a i j * z else 0) := by
    funext j
    split <;> simp_all
  rw [h, sum_delta indices hnd s]
  simp [hs]

/-- Product of the scalar contributions of the ordered block decorations. -/
def wordProduct {ε : Type} (f : ε → Int) : List ε → Int
  | [] => 1
  | e :: es => f e * wordProduct f es

theorem intWordIterate_single {ι ε : Type} [DecidableEq ι]
    (indices : List ι) (hnd : indices.Nodup) (s : ι) (hs : s ∈ indices)
    (a : ε → ι → ι → Int) (q : ι → Int) (f : ε → Int) (z : Int)
    (ha : ∀ e i, a e i s = if i = s then f e else 0)
    (hq : ∀ i, q i = if i = s then z else 0) (es : List ε) (i : ι) :
    intWordIterate indices a q es i = if i = s then wordProduct f es * z else 0 := by
  induction es generalizing i with
  | nil => simpa [intWordIterate, wordProduct] using hq i
  | cons e es ih =>
    have hf : intWordIterate indices a q es =
        fun i => if i = s then wordProduct f es * z else 0 := funext ih
    rw [intWordIterate, hf, intStep_delta indices hnd s hs, ha]
    by_cases hi : i = s <;> simp [hi, wordProduct, Int.mul_assoc]

/-- Lattice reduction for every exterior decoration, with no bound on the number of blocks. -/
theorem tensorCoefficient_constant_single {ι ε : Type} [DecidableEq ι]
    (indices : List ι) (hnd : indices.Nodup) (s : ι) (hs : s ∈ indices)
    (p : ι → Laurent) (a : ε → ι → ι → Laurent) (q : ι → Laurent)
    (hp : ∀ i, Nonpositive (p i)) (ha : ∀ e i j, Nonpositive (a e i j))
    (hq : ∀ i, Nonpositive (q i)) (f : ε → Int) (z : Int)
    (hac : ∀ e i, coeff (a e i s) 0 = if i = s then f e else 0)
    (hqc : ∀ i, coeff (q i) 0 = if i = s then z else 0) (es : List ε) :
    coeff (tensorCoefficient indices p a q es) 0 =
      coeff (p s) 0 * wordProduct f es * z := by
  simp only [tensorCoefficient, coeff_sum, List.map_map, Function.comp_def]
  have hc : (fun i => coeff (mul (p i) (wordIterate indices a q es i)) 0) =
      fun i => if i = s then coeff (p i) 0 * (wordProduct f es * z) else 0 := by
    funext i
    rw [coeff_mul_zero _ _ (hp i) (wordIterate_nonpositive indices a q ha hq es i)]
    rw [congrFun (wordIterate_constant indices a q ha hq es) i]
    rw [intWordIterate_single indices hnd s hs _ _ f z hac hqc]
    split <;> simp_all
  rw [hc, sum_delta indices hnd s]
  simp [hs, Int.mul_assoc]

theorem wordProduct_delta {ε : Type} [DecidableEq ε] (u : ε) (es : List ε) :
    wordProduct (fun e => if e = u then 1 else 0) es =
      if es = List.replicate es.length u then 1 else 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [wordProduct, ih, List.length_cons, List.replicate_succ, List.cons.injEq]
    split <;> split <;> split <;> grind

/-- Unique constant tensor word: the initial output, m block words, and terminal output. -/
theorem tensor_unique_leading_state {ι α ε ω : Type}
    [DecidableEq ι] [DecidableEq α] [DecidableEq ε] [DecidableEq ω]
    (indices : List ι) (hnd : indices.Nodup) (s : ι) (hs : s ∈ indices)
    (p : α → ι → Laurent) (a : ε → ι → ι → Laurent) (q : ω → ι → Laurent)
    (y : α) (u : ε) (v : ω)
    (hp : ∀ o i, Nonpositive (p o i)) (ha : ∀ e i j, Nonpositive (a e i j))
    (hq : ∀ r i, Nonpositive (q r i))
    (hpc : ∀ o, coeff (p o s) 0 = if o = y then 1 else 0)
    (hac : ∀ e i, coeff (a e i s) 0 = if i = s then (if e = u then 1 else 0) else 0)
    (hqc : ∀ r i, coeff (q r i) 0 = if i = s then (if r = v then 1 else 0) else 0)
    (o : α) (es : List ε) (r : ω) :
    Nonpositive (tensorCoefficient indices (p o) a (q r) es) ∧
    coeff (tensorCoefficient indices (p o) a (q r) es) 0 =
      if o = y ∧ es = List.replicate es.length u ∧ r = v then 1 else 0 := by
  constructor
  · exact tensorCoefficient_nonpositive indices (p o) a (q r) (hp o) ha (hq r) es
  · rw [tensorCoefficient_constant_single indices hnd s hs (p o) a (q r)
        (hp o) ha (hq r) (fun e => if e = u then 1 else 0)
        (if r = v then 1 else 0) hac (hqc r) es, hpc, wordProduct_delta]
    split <;> split <;> split <;> split <;> grind

end WebMu.Revised
