import WebMu.Revised.TensorInduction

namespace WebMu.Revised
open Laurent

/-- Action of the two closed constant rows, in order ABC, scalar. -/
def kStep (x : Int × Int) : Int × Int := (x.2, 2 * x.1)

def kPower : Nat → Int × Int
  | 0 => (1,0)
  | m+1 => kStep (kPower m)

theorem k_squared (x : Int × Int) : kStep (kStep x) = (2*x.1, 2*x.2) := rfl

theorem kPower_even (r : Nat) : kPower (2*r) = ((2:Int)^r, 0) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Nat.mul_succ]
    change kStep (kStep (kPower (2*r))) = ((2:Int)^(r+1), 0)
    rw [ih]
    simp [kStep, Int.pow_succ, Int.mul_comm]

theorem kPower_odd (r : Nat) : kPower (2*r+1) = (0, (2:Int)^(r+1)) := by
  change kStep (kPower (2*r)) = _
  rw [kPower_even]
  simp [kStep, Int.pow_succ, Int.mul_comm]

theorem kPower_first (m : Nat) :
    (kPower m).1 = if m % 2 = 0 then (2:Int)^(m/2) else 0 := by
  have hm : m = 2 * (m / 2) + m % 2 := by omega
  have hr : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hr with h | h
  · rw [if_pos h]
    have he : m = 2 * (m/2) := by omega
    calc
      (kPower m).1 = (kPower (2 * (m/2))).1 := congrArg (fun n => (kPower n).1) he
      _ = (2:Int)^(m/2) := congrArg Prod.fst (kPower_even (m/2))
  · have hn : m % 2 ≠ 0 := by omega
    rw [if_neg hn]
    have he : m = 2 * (m/2) + 1 := by omega
    rw [he, kPower_odd]

theorem intStep_closedRow {ι : Type} [DecidableEq ι] (indices : List ι)
    (hnd : indices.Nodup) (a : ι → ι → Int) (i j : ι) (hj : j ∈ indices)
    (c : Int) (hrow : ∀ l, a i l = if l = j then c else 0) (x : ι → Int) :
    intStep indices a x i = c * x j := by
  simp only [intStep, hrow]
  have hf : (fun l => (if l = j then c else 0) * x l) =
      fun l => if l = j then c * x l else 0 := by
    funext l
    split <;> simp_all
  rw [hf, sum_delta indices hnd j]
  simp [hj]

/-- Row closure is used in its actual direction: other coordinates may be populated. -/
theorem intIterate_closed_pair {ι : Type} [DecidableEq ι] (indices : List ι)
    (hnd : indices.Nodup) (a : ι → ι → Int) (q : ι → Int)
    (s z : ι) (hs : s ∈ indices) (hz : z ∈ indices)
    (hrowS : ∀ j, a s j = if j = z then 1 else 0)
    (hrowZ : ∀ j, a z j = if j = s then 2 else 0)
    (hqs : q s = 1) (hqz : q z = 0) (m : Nat) :
    (intIterate indices a q m s, intIterate indices a q m z) = kPower m := by
  induction m with
  | zero => simp [intIterate, kPower, hqs, hqz]
  | succ m ih =>
    simp only [intIterate, intStep_closedRow indices hnd a s z hz 1 hrowS,
      intStep_closedRow indices hnd a z s hs 2 hrowZ, Int.one_mul, kPower]
    exact congrArg kStep ih

/-- First-order readout, including the prefix, from two local constant rows. -/
theorem selected_coefficient {ι : Type} [DecidableEq ι] (indices : List ι)
    (hnd : indices.Nodup) (p : ι → Laurent) (a : ι → ι → Laurent)
    (q : ι → Laurent) (s z : ι) (hs : s ∈ indices) (hz : z ∈ indices)
    (hp : ∀ i, Nonpositive (p i)) (ha : ∀ i j, Nonpositive (a i j))
    (hq : ∀ i, Nonpositive (q i)) (hzero : ∀ i, coeff (q i) 0 = 0)
    (hpc : ∀ j, coeff (p j) 0 = if j = s then 1 else 0)
    (hrowS : ∀ j, coeff (a s j) 0 = if j = z then 1 else 0)
    (hrowZ : ∀ j, coeff (a z j) 0 = if j = s then 2 else 0)
    (hqs : coeff (q s) (-1) = 1) (hqz : coeff (q z) (-1) = 0) (m : Nat) :
    coeff (Laurent.sum (indices.map (fun i => mul (p i) (iterate indices a q m i)))) (-1) =
      if m % 2 = 0 then (2:Int)^(m/2) else 0 := by
  rw [coeff_sum]
  simp only [List.map_map, Function.comp_def]
  have hf : (fun i => coeff (mul (p i) (iterate indices a q m i)) (-1)) =
      fun i => if i = s then coeff (iterate indices a q m i) (-1) else 0 := by
    funext i
    rw [coeff_mul_neg_one _ _ (hp i) (iterate_nonpositive indices a q ha hq m i),
      iterate_zero_constant indices a q ha hq hzero m i, hpc]
    split <;> simp_all
  rw [hf, sum_delta indices hnd s, if_pos hs]
  rw [congrFun (iterate_first_of_zero_constant indices a q ha hq hzero m) s]
  have h := intIterate_closed_pair indices hnd (fun i j => coeff (a i j) 0)
    (fun i => coeff (q i) (-1)) s z hs hz hrowS hrowZ hqs hqz m
  rw [← kPower_first]
  exact congrArg Prod.fst h

end WebMu.Revised
