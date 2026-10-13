import WebMu.Revised.Shortening
import WebMu.Revised.Applications
import WebMu.Revised.SupportBounds

/-! Generic insertion of the actual tripod tensor.  The ordered output index
is `(old index, inserted three-letter state)`; when the old index is a pair
`(u,z)`, its flattened word is `u ++ state ++ z`.  Taking `u.length = 6`
is exactly the insertion in the manuscript.  The only hypotheses in the
canonical conclusion are the uniform tensor-bar naturality and canonical
characterization from the cited theory, valid at arbitrary boundary lengths. -/
namespace WebMu.Revised.ShorteningCanonical
open Laurent Algebra

set_option maxRecDepth 100000

/-- The full coefficient characterization, on any standard tensor index set. -/
def Leading {ι : Type} [DecidableEq ι] (f : ι → Poly) (c : ι) : Prop :=
  (∀ i d, 0 < d → coefficient (f i) d = 0) ∧
  (∀ i, coefficient (f i) 0 = if i = c then 1 else 0)

/-- The generic existence/uniqueness theorem, with no dimension restriction. -/
structure CanonicalCharacterization (ι : Type) [DecidableEq ι]
    (bar : (ι → Poly) → ι → Poly) where
  canonical : ι → ι → Poly
  fixed : ∀ c, bar (canonical c) = canonical c
  leading : ∀ c, Leading (canonical c) c
  unique : ∀ c f, bar f = f → Leading f c → f = canonical c

def tripodCoordinate (w : Word) : Poly := ofList (tripod.getD w [])

def insert {ι : Type} (f : ι → Poly) (b : ι × Word) : Poly :=
  f b.1 * tripodCoordinate b.2

def flattenInserted (b : (Word × Word) × Word) : Word := b.1.1 ++ b.2 ++ b.1.2

/-- The newly inserted outputs occupy precisely positions 7,8,9. -/
theorem flatten_after_six (u z : Word) (hu : u.length = 6) :
    (flattenInserted ((u,z),[0,1,2])).take 6 = u ∧
    (flattenInserted ((u,z),[0,1,2])).drop 9 = z := by
  constructor
  · simp [flattenInserted, List.append_assoc, ← hu]
  · simp [flattenInserted, List.drop_append,hu]

private theorem coeff_mul_nonpositive_right (p q : Laurent)
    (hp : ∀ d, 0 < d → coeff p d = 0) (hq : Nonpositive q) :
    (∀ d, 0 < d → coeff (mul p q) d = 0) ∧
    coeff (mul p q) 0 = coeff p 0 * coeff q 0 := by
  induction q with
  | nil =>
    constructor
    · intro d _; exact (Algebra.mul_comm p [] d).trans rfl
    · simpa [coeff] using Algebra.mul_comm p [] 0
  | cons term q ih =>
    rcases term with ⟨e,a⟩
    rw [nonpositive_cons] at hq
    obtain ⟨hi,hc⟩ := ih hq.2
    constructor
    · intro d hd
      rw [coeff_mul_cons, hp (d-e) (by omega), hi d hd]
      simp
    · rw [coeff_mul_cons, hc]
      by_cases he : e=0
      · simp [he,coeff,Int.mul_add]
      · have he' : 0 < 0-e := by omega
        rw [hp (0-e) he']
        simp [coeff,he]

private theorem poly_mul_nonpositive_right (p : Poly) (q : Laurent)
    (hp : ∀ d, 0 < d → coefficient p d = 0) (hq : Nonpositive q) :
    (∀ d, 0 < d → coefficient (p * ofList q) d = 0) ∧
    coefficient (p * ofList q) 0 = coefficient p 0 * coeff q 0 := by
  induction p using Quotient.inductionOn with
  | _ p => exact coeff_mul_nonpositive_right p q hp hq

theorem tripodCoordinate_nonpositive (w : Word) : Nonpositive (tripod.getD w []) :=
  bounded_nonpositive _ (allEntries_getD _ _ tripod_nonpositive (fun _ => rfl) w)

theorem tripodCoordinate_constant (w : Word) :
    coefficient (tripodCoordinate w) 0 = if w=[0,1,2] then 1 else 0 := by
  simpa [tripodCoordinate] using singleConstant_getD tripod [0,1,2] tripod_unique_constant w

/-- Inserting the leading tripod state preserves every original coefficient. -/
theorem insert_ABC {ι : Type} (f : ι → Poly) (i : ι) : insert f (i,[0,1,2]) = f i := by
  change f i * ofList (tripod.getD [0,1,2] []) = f i
  rw [tripod_ABC]
  exact poly_mul_one _

/-- Multiplication by the actual tripod preserves the complete leading lattice. -/
theorem insert_leading {ι : Type} [DecidableEq ι] (f : ι → Poly) (c : ι)
    (hf : Leading f c) : Leading (insert f) (c,[0,1,2]) := by
  constructor
  · intro b d hd
    exact (poly_mul_nonpositive_right (f b.1) _ (hf.1 b.1)
      (tripodCoordinate_nonpositive b.2)).1 d hd
  · intro b
    unfold insert tripodCoordinate
    rw [(poly_mul_nonpositive_right (f b.1) _ (hf.1 b.1)
      (tripodCoordinate_nonpositive b.2)).2, hf.2 b.1]
    change (if b.1=c then (1:Int) else 0) * coefficient (tripodCoordinate b.2) 0 = _
    rw [tripodCoordinate_constant]
    rcases b with ⟨i,w⟩
    by_cases hi : i=c <;> by_cases hw : w=[0,1,2] <;> simp [hi,hw]

/-- Canonicality of insertion follows only from the general bar and uniqueness
rules. In particular no assertion about this paper's family is an input. -/
theorem insertion_canonical {ι : Type} [DecidableEq ι]
    (barIn : (ι → Poly) → ι → Poly)
    (barOut : (ι × Word → Poly) → ι × Word → Poly)
    (C : CanonicalCharacterization ι barIn)
    (D : CanonicalCharacterization (ι × Word) barOut)
    (bar_natural : ∀ f, barOut (insert f) = insert (barIn f)) (c : ι) :
    insert (C.canonical c) = D.canonical (c,[0,1,2]) := by
  apply D.unique
  · rw [bar_natural,C.fixed]
  · exact insert_leading _ _ (C.leading c)

/-- The actual 27-dimensional three-factor standard tensor index. -/
abbrev TripodIndex := { w : Word // validWord 3 w = true }

def tripodIndex : TripodIndex := ⟨[0,1,2],by decide⟩

def insertTyped {ι : Type} (f : ι → Poly) (b : ι × TripodIndex) : Poly :=
  insert f (b.1,b.2.val)

theorem insertTyped_ABC {ι : Type} (f : ι → Poly) (i : ι) :
    insertTyped f (i,tripodIndex) = f i := insert_ABC f i

theorem insertTyped_leading {ι : Type} [DecidableEq ι] (f : ι → Poly) (c : ι)
    (hf : Leading f c) : Leading (insertTyped f) (c,tripodIndex) := by
  have h := insert_leading f c hf
  constructor
  · intro b d hd
    exact h.1 (b.1,b.2.val) d hd
  · intro b
    change coefficient (insert f (b.1,b.2.val)) 0 = _
    rw [h.2]
    have he : (b.1,b.2.val) = (c,[0,1,2]) ↔ b = (c,tripodIndex) := by
      rcases b with ⟨i,w⟩
      simp only [Prod.mk.injEq,tripodIndex,Subtype.ext_iff]
    simp only [he]

/-- Canonical insertion on the actual three-factor standard tensor basis.
The input index may be any fixed tensor boundary, split as `(u,z)` when
inserting after six factors. This is the finite-dimensional manuscript claim. -/
theorem typed_insertion_canonical {ι : Type} [DecidableEq ι]
    (barIn : (ι → Poly) → ι → Poly)
    (barOut : (ι × TripodIndex → Poly) → ι × TripodIndex → Poly)
    (C : CanonicalCharacterization ι barIn)
    (D : CanonicalCharacterization (ι × TripodIndex) barOut)
    (bar_natural : ∀ f, barOut (insertTyped f) = insertTyped (barIn f)) (c : ι) :
    insertTyped (C.canonical c) = D.canonical (c,tripodIndex) := by
  apply D.unique
  · rw [bar_natural,C.fixed]
  · exact insertTyped_leading _ _ (C.leading c)

#print axioms typed_insertion_canonical
#print axioms insertion_canonical
end WebMu.Revised.ShorteningCanonical
