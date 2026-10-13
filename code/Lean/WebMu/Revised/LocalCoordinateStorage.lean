import WebMu.Revised.CircuitSparseSemantics
import WebMu.Revised.LocalDegreeAlgebra

/-! Storage and boundary checks used only to convert coefficientwise local
proofs to the existing sparse-list lattice API. No degree or leading-state
assertion is checked in this file. -/
namespace WebMu.Revised.LocalDegreeProof
open Laurent Algebra Bar
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem prefix_storage : ∀ j : Fin 28,
    allEntries (prefixHat j) (fun _ p => canonical p)=true := by native_decide

theorem block_storage : ∀ j : Fin 28,
    allEntries (blockHat j) (fun k p => k.1<28 && k.2<3^9 && canonical p)=true := by native_decide

theorem tail_storage :
    allEntries tailHat (fun k p => k.1<28 && k.2<3^6 && canonical p)=true := by native_decide

theorem prefix_canonical (j : Fin 28) (w : Word) : canonical ((prefixHat j).getD w [])=true :=
  allEntries_getD _ _ (prefix_storage j) (by intro; rfl) w

theorem storage_canonical {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (p : α → Bool)
    (h : allEntries x (fun k q => p k && canonical q)=true) (k : α) :
    canonical (x.getD k [])=true := by
  have hh : allEntries x (fun _ q => canonical q)=true := by
    apply List.all_eq_true.mpr
    rintro ⟨u,q⟩ hu
    exact (show p u=true ∧ canonical q=true from by simpa only [Bool.and_eq_true] using List.all_eq_true.mp h (u,q) hu).2
  exact allEntries_getD _ _ hh (by intro; rfl) k

theorem block_canonical (j : Fin 28) (k : Nat × Nat) : canonical ((blockHat j).getD k [])=true :=
  storage_canonical _ _ (block_storage j) k

theorem tail_canonical (k : Nat × Nat) : canonical (tailHat.getD k [])=true :=
  storage_canonical _ _ tail_storage k

theorem storage_zero {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (x : Std.HashMap α Laurent) (p : α → Bool)
    (h : allEntries x (fun k q => p k && canonical q)=true) (k : α) (hn : p k≠true) :
    x.getD k []=[] := by
  by_cases hz : x.getD k []=[]
  · exact hz
  · have hh : allEntries x (fun k _ => p k)=true := by
      apply List.all_eq_true.mpr
      rintro ⟨u,q⟩ hu
      exact (show p u=true ∧ canonical q=true from by simpa only [Bool.and_eq_true] using List.all_eq_true.mp h (u,q) hu).1
    exact False.elim (hn (map_valid_nonzero x p hh k hz))

theorem block_outside (j : Fin 28) (i e : Nat) (he : 3^9≤e) :
    (blockHat j).getD (i,e) []=[] :=
  storage_zero (blockHat j) (fun k => k.1<28 && k.2<3^9) (block_storage j) (i,e) (by
    intro h
    have hh : i<28 ∧ e<3^9 := by simpa using h
    omega)

theorem tail_outside (i e : Nat) (he : 3^6≤e) : tailHat.getD (i,e) []=[] :=
  storage_zero tailHat (fun k => k.1<28 && k.2<3^6) tail_storage (i,e) (by
    intro h
    have hh : i<28 ∧ e<3^6 := by simpa using h
    omega)

end WebMu.Revised.LocalDegreeProof
