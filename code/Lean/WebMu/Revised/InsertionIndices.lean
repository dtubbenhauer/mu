import WebMu.Revised.WebCanonical

/-! Ordered standard-basis indices for insertion after the sixth tensor factor. -/
namespace WebMu.Revised.Insertion
open Bar WebCanonical ShorteningCanonical

abbrev Index (n : Nat) := { w : Word // validWord n w = true }

theorem length_index {n : Nat} (w : Index n) : w.val.length = n :=
  (Bar.validWord_iff _ _).mp w.property |>.1

theorem ternary_index {n : Nat} (w : Index n) : Ternary w.val :=
  (Bar.validWord_iff _ _).mp w.property |>.2

def join {a b : Nat} (u : Index a) (v : Index b) : Index (a+b) :=
  ⟨u.val++v.val, Bar.validWord_append u.property v.property⟩

def split {a b : Nat} (w : Index (a+b)) : Index a × Index b := by
  have hl := length_index w
  have ht := ternary_index w
  exact (⟨w.val.take a,(Bar.validWord_iff _ _).mpr ⟨by simp [hl], by
      intro x hx; exact ht x (List.mem_of_mem_take hx)⟩⟩,
    ⟨w.val.drop a,(Bar.validWord_iff _ _).mpr ⟨by simp [hl],by
      intro x hx; exact ht x (List.mem_of_mem_drop hx)⟩⟩)

@[simp] theorem split_join {a b : Nat} (u : Index a) (v : Index b) :
    split (join u v) = (u,v) := by
  apply Prod.ext <;> apply Subtype.ext
  · simp [split,join,← length_index u]
  · simp [split,join,← length_index u]

@[simp] theorem join_split {a b : Nat} (w : Index (a+b)) :
    join (split w).1 (split w).2 = w := by
  apply Subtype.ext
  exact List.take_append_drop _ _

abbrev OldIndex (n : Nat) := Index (6+n)
abbrev NewIndex (n : Nat) := Index ((6+3)+n)

/-- The exact boundary order is the old first six letters, the tripod, then the
old suffix. No permutation of tensor factors is implicit. -/
def insertedIndex {n : Nat} (b : OldIndex n × TripodIndex) : NewIndex n :=
  join (join (split b.1).1 b.2) (split b.1).2

def removeIndex {n : Nat} (w : NewIndex n) : OldIndex n × TripodIndex :=
  let halves := split w
  let head := split halves.1
  (join head.1 halves.2,head.2)

@[simp] theorem remove_inserted {n : Nat} (b : OldIndex n × TripodIndex) :
    removeIndex (insertedIndex b) = b := by
  rcases b with ⟨b,t⟩
  simp [removeIndex,insertedIndex]

@[simp] theorem inserted_remove {n : Nat} (w : NewIndex n) :
    insertedIndex (removeIndex w) = w := by
  simp [removeIndex,insertedIndex]

@[simp] theorem inserted_word {n : Nat} (u : OldIndex n) (v : TripodIndex) :
    (insertedIndex (u,v)).val = u.val.take 6 ++ v.val ++ u.val.drop 6 := rfl

/-- Equality of full ordered words, rather than merely equality of a weight. -/
theorem inserted_injective {n : Nat} {a b : OldIndex n × TripodIndex}
    (h : insertedIndex a = insertedIndex b) : a=b := by
  have h' := congrArg removeIndex h
  simpa using h'

/-- Transport the already proved complete leading congruence along the actual
bijection of standard tensor indices. -/
def insertCoordinates {n : Nat} (f : OldIndex n → Algebra.Poly) :
    NewIndex n → Algebra.Poly := fun w => insertTyped f (removeIndex w)

theorem insertCoordinates_leading {n : Nat} (f : OldIndex n → Algebra.Poly)
    (c : OldIndex n) (h : Leading f c) :
    Leading (insertCoordinates f) (insertedIndex (c,tripodIndex)) := by
  have hi := insertTyped_leading f c h
  constructor
  · intro w d hd
    exact hi.1 (removeIndex w) d hd
  · intro w
    change Algebra.coefficient (insertTyped f (removeIndex w)) 0 = _
    rw [hi.2]
    have he : removeIndex w = (c,tripodIndex) ↔ w=insertedIndex (c,tripodIndex) := by
      constructor
      · intro hw
        rw [← inserted_remove w,hw]
      · intro hw
        rw [hw,remove_inserted]
    simp only [he]

theorem insertCoordinates_ABC {n : Nat} (f : OldIndex n → Algebra.Poly)
    (c : OldIndex n) : insertCoordinates f (insertedIndex (c,tripodIndex)) = f c := by
  simp only [insertCoordinates,remove_inserted,insertTyped_ABC]

end WebMu.Revised.Insertion
