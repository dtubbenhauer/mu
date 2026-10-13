import WebMu.Revised.NormTransfer
import WebMu.Revised.Reindex

namespace WebMu.Revised.ShortNorm
open Laurent Algebra NormSemantics

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem shortPrefix_bound (i : Fin 28) :
    allEntries (shortPrefix i) (fun w _ => validWord 6 w) = true := by
  by_cases hi : i.val < 27
  · exact (raw_boundaries_check ⟨i.val,hi⟩).2.2.2
  · have he : i = (27 : Fin 28) := Fin.ext (by omega)
    subst i
    simp [shortPrefix,allEntries]

theorem prefixN_encode (w : Word) (hw : w.length = 6 ∧ Ternary w) (i : Fin 28) :
    prefixN (encode w) i = originalPrefix w i := by
  unfold prefixN shortPrefixColumn
  rw [hashmap_fold_poly]
  calc
    total (shortPrefix i).toList (fun (z,p) =>
        if (0,encode z) == (0,encode w) then ofList p else 0) =
      total (shortPrefix i).toList (fun (z,p) => if z == w then ofList p else 0) := by
        apply total_congr_mem
        rintro ⟨z,p⟩ hm
        have hz := tensor_entries_valid _ _ (shortPrefix_bound i) z p hm
        have he := encode_eq_iff_fixed_length z w hz.2 hw.2 (hz.1.trans hw.1.symm)
        simp only [beq_iff_eq,Prod.mk.injEq,true_and,he]
    _ = originalPrefix w i := hashmap_total_lookup (shortPrefix i) w ofList rfl

theorem blockN_original : blockN = originalBlock := rfl
theorem tailN_original : tailN = originalTail := rfl

theorem norm_coordinate_original (m : Nat) (b : Boundary m) :
    pairing (List.finRange 28) (prefixN (encode b.initial))
      (wordAction (List.finRange 28) blockN (tailN (encode b.terminal))
        (b.blocks.map encode)) = tensorOriginal m b := by
  have hp : prefixN (encode b.initial) = originalPrefix b.initial :=
    funext (prefixN_encode b.initial ⟨b.initial_length,b.initial_ternary⟩)
  rw [hp,blockN_original,tailN_original]
  rfl

theorem decode_length (n a : Nat) : (decodeWord n a).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [decodeWord,ih]

theorem decode_ternary (n a : Nat) : Ternary (decodeWord n a) := by
  induction n generalizing a with
  | zero => simp [decodeWord,Ternary]
  | succ n ih =>
    intro b hb
    have hh : b ∈ decodeWord n (a/3) ∨ b = a%3 := by simpa [decodeWord] using hb
    cases hh with
    | inl h => exact ih _ _ h
    | inr h => subst b; exact Nat.mod_lt _ (by decide)

theorem encode_decode (n a : Nat) (ha : a < 3^n) : encode (decodeWord n a) = a := by
  induction n generalizing a with
  | zero =>
    have he : a = 0 := by simpa using ha
    subst a
    rfl
  | succ n ih =>
    have hd : a/3 < 3^n := by
      have hh : a < 3^n*3 := by simpa [Nat.pow_succ] using ha
      omega
    simp only [decodeWord,encode_snoc,ih _ hd]
    omega

theorem encode_bound (w : Word) (hw : Ternary w) : encode w < 3^w.length := by
  induction w using reverse_induction with
  | hnil => decide
  | hsnoc w a ih =>
    have ha : a < 3 := hw a (by simp)
    have hi := ih (fun b hb => hw b (by simp [hb]))
    simp only [encode_snoc,List.length_append,List.length_cons,List.length_nil,
      Nat.zero_add,Nat.pow_succ]
    omega

theorem history_blocks_length (m : Nat) (h : History Nat Nat m) :
    (historyBlocks m h).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => rcases h with ⟨h,e⟩; simp [historyBlocks,ih]

def normBoundary (m : Nat) (h : History Nat Nat m) (r : Nat) : Boundary m where
  initial := decodeWord 6 (historyInitial m h)
  blocks := (historyBlocks m h).map (decodeWord 9)
  terminal := decodeWord 6 r
  initial_length := decode_length _ _
  blocks_length := by simp [history_blocks_length]
  terminal_length := decode_length _ _
  initial_ternary := decode_ternary _ _
  blocks_valid := by
    intro w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    exact ⟨decode_length _ _,decode_ternary _ _⟩
  terminal_ternary := decode_ternary _ _

theorem history_bounds (m : Nat) (h : History Nat Nat m)
    (hh : h ∈ histories initialWords blockWords m) :
    historyInitial m h < 3^6 ∧ ∀ e ∈ historyBlocks m h, e < 3^9 := by
  induction m with
  | zero => exact ⟨List.mem_range.mp hh,by simp [historyBlocks]⟩
  | succ m ih =>
    rcases h with ⟨h,e⟩
    obtain ⟨h',hh',he⟩ := List.mem_flatMap.mp hh
    obtain ⟨e',he',heq⟩ := List.mem_map.mp he
    cases heq
    obtain ⟨hinit,hblocks⟩ := ih h hh'
    refine ⟨hinit,?_⟩
    intro a ha
    have hd : a ∈ historyBlocks m h ∨ a = e := by simpa [historyBlocks] using ha
    cases hd with
    | inl hd => exact hblocks a hd
    | inr hd => subst a; exact List.mem_range.mp he'

theorem normBoundary_coordinate (m : Nat) (h : History Nat Nat m) (r : Nat)
    (hh : h ∈ histories initialWords blockWords m) (hr : r ∈ tailWords) :
    rightMap (List.finRange 28) (rowCoordinates (List.finRange 28) prefixN blockN m h)
      (fun i (_ : Unit) => tailN r i) () = tensorOriginal m (normBoundary m h r) := by
  rw [full_coordinate_history]
  have hs := history_bounds m h hh
  have hp : encode (normBoundary m h r).initial = historyInitial m h :=
    encode_decode _ _ hs.1
  have ht : encode (normBoundary m h r).terminal = r :=
    encode_decode _ _ (List.mem_range.mp hr)
  have hb : (normBoundary m h r).blocks.map encode = historyBlocks m h := by
    simp only [normBoundary,List.map_map]
    have he : (historyBlocks m h).map (encode ∘ decodeWord 9) =
        (historyBlocks m h).map id := by
      apply List.map_congr_left
      intro e he
      exact encode_decode _ _ (hs.2 e he)
    simpa using he
  have he := norm_coordinate_original m (normBoundary m h r)
  rw [hp,ht,hb] at he
  exact he

def originalCoordinateNorm (m : Nat) : Poly :=
  total (histories initialWords blockWords m) (fun h => total tailWords (fun r =>
    tensorOriginal m (normBoundary m h r) * tensorOriginal m (normBoundary m h r)))

theorem original_norm_polynomial (m : Nat) :
    originalCoordinateNorm m = ofList (normPolynomial m) := by
  rw [← full_norm_polynomial]
  unfold originalCoordinateNorm fullNorm
  apply total_congr_mem
  intro h hh
  apply total_congr_mem
  intro r hr
  rw [normBoundary_coordinate m h r hh hr]

theorem original_norm_integral_constant_one (m : Nat) :
    (∀ d, 0 < d → coefficient (originalCoordinateNorm m) d = 0) ∧
      coefficient (originalCoordinateNorm m) 0 = 1 := by
  rw [original_norm_polynomial]
  exact ⟨fun d hd => Laurent.coeff_positive _ (norm_support_constant m).1 d hd,
    (norm_support_constant m).2⟩

theorem history_ext (m : Nat) (h k : History Nat Nat m)
    (hi : historyInitial m h = historyInitial m k)
    (hb : historyBlocks m h = historyBlocks m k) : h = k := by
  induction m with
  | zero => exact hi
  | succ m ih =>
    rcases h with ⟨h,e⟩
    rcases k with ⟨k,f⟩
    obtain ⟨hb,hef⟩ := List.append_inj' hb (by rfl)
    exact Prod.ext (ih h k hi hb) (List.singleton_inj.mp hef)

theorem history_exists (a : Nat) (es : List Nat) (m : Nat) (hm : es.length = m) :
    ∃ h : History Nat Nat m, historyInitial m h = a ∧ historyBlocks m h = es := by
  induction es using reverse_induction generalizing m with
  | hnil =>
    have he : m = 0 := hm.symm
    subst m
    exact ⟨a,rfl,rfl⟩
  | hsnoc es e ih =>
    have he : m = es.length+1 := by simpa using hm.symm
    rw [he]
    obtain ⟨h,hi,hb⟩ := ih es.length rfl
    exact ⟨(h,e),hi,by simp [historyBlocks,hb]⟩

theorem history_member (m : Nat) (h : History Nat Nat m)
    (hi : historyInitial m h < 3^6)
    (hb : ∀ e ∈ historyBlocks m h, e < 3^9) :
    h ∈ histories initialWords blockWords m := by
  induction m with
  | zero => exact List.mem_range.mpr hi
  | succ m ih =>
    rcases h with ⟨h,e⟩
    apply List.mem_flatMap.mpr
    refine ⟨h,ih h hi (fun a ha => hb a (by simp [historyBlocks,ha])),?_⟩
    apply List.mem_map.mpr
    exact ⟨e,List.mem_range.mpr (hb e (by simp [historyBlocks])),rfl⟩

theorem normBoundary_surjective (m : Nat) (b : Boundary m) :
    ∃ h ∈ histories initialWords blockWords m, ∃ r ∈ tailWords,
      normBoundary m h r = b := by
  obtain ⟨h,hi,hb⟩ := history_exists (encode b.initial) (b.blocks.map encode) m
    (by simp [b.blocks_length])
  have hmem : h ∈ histories initialWords blockWords m := by
    apply history_member m h
    · rw [hi,← b.initial_length]
      exact encode_bound _ b.initial_ternary
    · intro e he
      rw [hb] at he
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
      have hv := b.blocks_valid w hw
      rw [← hv.1]
      exact encode_bound _ hv.2
  refine ⟨h,hmem,encode b.terminal,?_,?_⟩
  · apply List.mem_range.mpr
    rw [← b.terminal_length]
    exact encode_bound _ b.terminal_ternary
  · apply Boundary.ext
    · change decodeWord 6 (historyInitial m h) = b.initial
      rw [hi,← b.initial_length,decodeWord_encode _ b.initial_ternary]
    · change (historyBlocks m h).map (decodeWord 9) = b.blocks
      rw [hb,List.map_map]
      have he : b.blocks.map (decodeWord 9 ∘ encode) = b.blocks.map id := by
        apply List.map_congr_left
        intro w hw
        have hv := b.blocks_valid w hw
        exact hv.1 ▸ decodeWord_encode w hv.2
      simpa using he
    · change decodeWord 6 (encode b.terminal) = b.terminal
      rw [← b.terminal_length,decodeWord_encode _ b.terminal_ternary]

theorem normBoundary_codes (m : Nat) (h : History Nat Nat m) (r : Nat)
    (hh : h ∈ histories initialWords blockWords m) (hr : r ∈ tailWords) :
    encode (normBoundary m h r).initial = historyInitial m h ∧
    (normBoundary m h r).blocks.map encode = historyBlocks m h ∧
    encode (normBoundary m h r).terminal = r := by
  have hs := history_bounds m h hh
  refine ⟨encode_decode _ _ hs.1,?_,encode_decode _ _ (List.mem_range.mp hr)⟩
  change ((historyBlocks m h).map (decodeWord 9)).map encode = _
  rw [List.map_map]
  have he : (historyBlocks m h).map (encode ∘ decodeWord 9) =
      (historyBlocks m h).map id := by
    apply List.map_congr_left
    intro e he
    exact encode_decode _ _ (hs.2 e he)
  simpa using he

theorem normBoundary_injective (m : Nat) (h k : History Nat Nat m) (r s : Nat)
    (hh : h ∈ histories initialWords blockWords m) (hk : k ∈ histories initialWords blockWords m)
    (hr : r ∈ tailWords) (hs : s ∈ tailWords)
    (he : normBoundary m h r = normBoundary m k s) : h = k ∧ r = s := by
  have hc := normBoundary_codes m h r hh hr
  have kc := normBoundary_codes m k s hk hs
  have hi := congrArg (fun b : Boundary m => encode b.initial) he
  have hb := congrArg (fun b : Boundary m => b.blocks.map encode) he
  have ht := congrArg (fun b : Boundary m => encode b.terminal) he
  dsimp only at hi hb ht
  rw [hc.1,kc.1] at hi
  rw [hc.2.1,kc.2.1] at hb
  rw [hc.2.2,kc.2.2] at ht
  exact ⟨history_ext m h k hi hb,ht⟩

theorem productList_nodup {α β : Type} (as : List α) (bs : List β)
    (ha : as.Nodup) (hb : bs.Nodup) :
    (as.flatMap (fun a => bs.map (fun b => (a,b)))).Nodup := by
  rw [List.nodup_iff_pairwise_ne,List.pairwise_flatMap]
  constructor
  · intro a _
    rw [List.pairwise_map]
    exact hb.imp (fun h he => h (congrArg Prod.snd he))
  · apply List.Pairwise.imp_of_mem _ ha
    intro a c _ _ h x hx y hy he
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp hy
    exact h (congrArg Prod.fst he)

theorem histories_nodup (m : Nat) : (histories initialWords blockWords m).Nodup := by
  induction m with
  | zero => exact List.nodup_range
  | succ m ih => exact productList_nodup _ _ ih List.nodup_range

def allBoundaries (m : Nat) : List (Boundary m) :=
  (histories initialWords blockWords m).flatMap (fun h => tailWords.map (normBoundary m h))

theorem allBoundaries_mem (m : Nat) (b : Boundary m) : b ∈ allBoundaries m := by
  obtain ⟨h,hh,r,hr,he⟩ := normBoundary_surjective m b
  exact List.mem_flatMap.mpr ⟨h,hh,List.mem_map.mpr ⟨r,hr,he⟩⟩

theorem allBoundaries_nodup (m : Nat) : (allBoundaries m).Nodup := by
  unfold allBoundaries
  rw [List.nodup_iff_pairwise_ne,List.pairwise_flatMap]
  constructor
  · intro h hh
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ (List.nodup_range : tailWords.Nodup)
    intro r s hr hs hn he
    exact hn (normBoundary_injective m h h r s hh hh hr hs he).2
  · apply List.Pairwise.imp_of_mem _ (histories_nodup m)
    intro h k hh hk hn b hb c hc he
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hb
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hc
    exact hn (normBoundary_injective m h k r s hh hk hr hs he).1

/-- The sum is over every standard tensor basis coordinate exactly once. -/
theorem original_norm_all_boundaries (m : Nat) :
    originalCoordinateNorm m = total (allBoundaries m)
      (fun b => tensorOriginal m b * tensorOriginal m b) := by
  simp only [allBoundaries,NormSemantics.total_flatMap,NormSemantics.total_map]
  rfl

end WebMu.Revised.ShortNorm
