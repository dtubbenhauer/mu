import WebMu.Revised.GrowthBridge
import WebMu.Revised.CoefficientBridge

/-! Coefficientwise degree arguments for the written local proof.  These
lemmas separate cancellation from storage normalization and from finite path
enumeration.  No local integrality conclusion is an input. -/
namespace WebMu.Revised.LocalDegreeProof
open Laurent Algebra TruncatedGrowth

def DegreeLE (p : Laurent) (b : Int) : Prop := ∀ e, b < e → coeff p e = 0

theorem degree_of_bound (p : Laurent) (b : Int) (h : BoundedAbove b p) :
    DegreeLE p b := by
  intro e he
  induction p with
  | nil => rfl
  | cons x p ih =>
    have hx := h x (by simp)
    have hp : BoundedAbove b p := by intro y hy; exact h y (by simp [hy])
    simp only [coeff, if_neg (show x.1 ≠ e by omega), Int.zero_add, ih hp]

theorem degree_mono {p : Laurent} {a b : Int} (h : DegreeLE p a) (hab : a ≤ b) :
    DegreeLE p b := by intro e he; exact h e (by omega)

theorem degree_add {p q : Laurent} {a : Int} (hp : DegreeLE p a) (hq : DegreeLE q a) :
    DegreeLE (add p q) a := by intro e he; rw [coeff_add,hp e he,hq e he]; rfl

theorem degree_neg {p : Laurent} {a : Int} (hp : DegreeLE p a) : DegreeLE (neg p) a := by
  intro e he; rw [Algebra.coeff_neg,hp e he]; rfl

theorem degree_shift {p : Laurent} {a : Int} (hp : DegreeLE p a) (e c : Int) :
    DegreeLE (shiftScale p e c) (a+e) := by
  intro k hk; rw [coeff_shiftScale,hp (k-e) (by omega)]; simp

def truncate (p : Laurent) (b : Int) : Laurent := p.filter (fun x => x.1 ≤ b)

theorem coeff_truncate (p : Laurent) (b e : Int) :
    coeff (truncate p b) e = if e ≤ b then coeff p e else 0 := by
  induction p with
  | nil => simp [truncate,coeff]
  | cons x p ih =>
    rcases x with ⟨k,c⟩
    simp only [truncate,List.filter_cons,decide_eq_true_eq]
    change coeff (if k ≤ b then (k,c)::truncate p b else truncate p b) e = _
    by_cases hk : k ≤ b <;> by_cases he : e ≤ b <;> by_cases hke : k=e <;>
      simp [hk,he,hke,coeff,ih] <;> omega

theorem truncate_equiv {p : Laurent} {b : Int} (h : DegreeLE p b) :
    Equiv p (truncate p b) := by
  intro e; rw [coeff_truncate]
  split
  · rfl
  next hn => exact h e (by omega)

theorem truncate_bounded (p : Laurent) (b : Int) : BoundedAbove b (truncate p b) := by
  intro x hx; exact of_decide_eq_true (List.mem_filter.mp hx).2

theorem bounded_add {p q : Laurent} {b : Int} (hp : BoundedAbove b p)
    (hq : BoundedAbove b q) : BoundedAbove b (add p q) := by
  induction p,q using add.induct with
  | case1 q => simpa [add] using hq
  | case2 p => simpa [add] using hp
  | case3 i a ps j c qs hij ih =>
    simp only [add,if_pos hij]
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x; exact hp _ (by simp)
    · exact ih (by intro y hy; exact hp y (by simp [hy])) hq x hx
  | case4 i a ps j c qs hij hji ih =>
    simp only [add,if_neg hij,if_pos hji]
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x; exact hq _ (by simp)
    · exact ih hp (by intro y hy; exact hq y (by simp [hy])) x hx
  | case5 i a ps j c qs hij hji hac ih =>
    simp only [add,if_neg hij,if_neg hji,if_pos hac]
    exact ih (by intro y hy; exact hp y (by simp [hy]))
      (by intro y hy; exact hq y (by simp [hy]))
  | case6 i a ps j c qs hij hji hac ih =>
    simp only [add,if_neg hij,if_neg hji,if_neg hac]
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x; exact hp (i,a) (by simp)
    · exact ih (by intro y hy; exact hp y (by simp [hy]))
        (by intro y hy; exact hq y (by simp [hy])) x hx

theorem bounded_shift {p : Laurent} {b : Int} (hp : BoundedAbove b p) (e c : Int) :
    BoundedAbove (b+e) (shiftScale p e c) := by
  intro x hx
  unfold shiftScale at hx
  split at hx
  · simp at hx
  · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    have := hp y hy; dsimp; omega

theorem bounded_mul {p q : Laurent} {a b : Int}
    (hp : BoundedAbove a p) (hq : BoundedAbove b q) : BoundedAbove (a+b) (mul p q) := by
  induction p with
  | nil => simp [mul,BoundedAbove]
  | cons x p ih =>
    apply bounded_add
    · intro y hy
      have hh := bounded_shift hq x.1 x.2 y hy
      have hx := hp x (by simp)
      omega
    · exact ih (by intro y hy; exact hp y (by simp [hy]))

theorem degree_mul {p q : Laurent} {a b : Int} (hp : DegreeLE p a) (hq : DegreeLE q b) :
    DegreeLE (mul p q) (a+b) := by
  intro e he
  rw [mul_congr (truncate_equiv hp) (truncate_equiv hq)]
  exact degree_of_bound _ _ (bounded_mul (truncate_bounded p a) (truncate_bounded q b)) e he

theorem degree_sum {ps : List Laurent} {a : Int} (h : ∀ p ∈ ps, DegreeLE p a) :
    DegreeLE (Laurent.sum ps) a := by
  induction ps with
  | nil => intro e he; rfl
  | cons p ps ih => exact degree_add (h p (by simp)) (ih (by intro q hq; exact h q (by simp [hq])))

theorem canonical_tail (x : Int × Int) (p : Laurent) (h : canonical (x::p)=true) :
    canonical p=true := by
  cases p with
  | nil => rfl
  | cons y p => exact (show (x.2 != 0 && decide (x.1 < y.1)) = true ∧ canonical (y::p)=true from by simpa only [canonical,Bool.and_eq_true] using h).2

theorem canonical_head_nonzero (x : Int × Int) (p : Laurent)
    (h : canonical (x::p)=true) : x.2 ≠ 0 := by
  cases p <;> simp only [canonical,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq] at h
  · exact h
  · exact h.1.1

theorem canonical_head_lt (x : Int × Int) (p : Laurent)
    (h : canonical (x::p)=true) : ∀ y ∈ p, x.1 < y.1 := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih =>
    have hh : x.2 ≠ 0 ∧ x.1 < y.1 ∧ canonical (y::p)=true := by
      simpa [canonical,and_assoc] using h
    intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · subst z; exact hh.2.1
    · have hz' := ih y hh.2.2 z hz
      omega

theorem coeff_zero_of_no_exponent (p : Laurent) (e : Int)
    (h : ∀ x ∈ p, x.1 ≠ e) : coeff p e=0 := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [coeff,if_neg (h x (by simp)),Int.zero_add]; exact ih (by intro y hy; exact h y (by simp [hy]))

theorem canonical_coeff_mem (p : Laurent) (h : canonical p=true)
    (x : Int × Int) (hx : x ∈ p) : coeff p x.1=x.2 := by
  induction p with
  | nil => simp at hx
  | cons y p ih =>
    have ht := canonical_tail y p h
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      rw [coeff,if_pos rfl,coeff_zero_of_no_exponent p y.1
        (by intro z hz; have := canonical_head_lt y p h z hz; omega)]
      omega
    · rw [coeff,if_neg (by have := canonical_head_lt y p h x hx; omega),Int.zero_add]
      exact ih ht hx

theorem canonical_nonzero_mem (p : Laurent) (hc : canonical p=true)
    (x : Int × Int) (hx : x ∈ p) : x.2 ≠ 0 := by
  induction p with
  | nil => simp at hx
  | cons y p ih =>
    rcases List.mem_cons.mp hx with hx | hx
    · subst x; exact canonical_head_nonzero y p hc
    · exact ih (canonical_tail y p hc) hx

theorem nonpositive_of_degree (p : Laurent) (hc : canonical p=true) (h : DegreeLE p 0) :
    Nonpositive p := by
  apply List.all_eq_true.mpr
  intro x hx
  apply decide_eq_true
  by_cases hn : x.1 ≤ 0
  · exact hn
  · have he := h x.1 (by omega)
    rw [canonical_coeff_mem p hc x hx] at he
    exact False.elim (canonical_nonzero_mem p hc x hx he)

end WebMu.Revised.LocalDegreeProof
