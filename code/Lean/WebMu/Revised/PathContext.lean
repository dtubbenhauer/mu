import WebMu.Revised.ElementaryPathDerivations

/-! Tensor-factor contexts for uncollected paths. A local path and every one of
its intermediate words can be placed between fixed spectator words. -/
namespace WebMu.Revised.LocalPaths
open Laurent Algebra GrowthBridge Bar Elementary

def frame (pre post : Word) (p : Path) : Path :=
  ⟨pre++p.input++post,pre++p.output++post,p.edges.map (surround pre post),
    p.degree,p.multiplicity⟩

def shiftStep (n : Nat) (s : Step) : Step := (s.1,n+s.2)

def fits : List Step → Word → Bool
  | [], _ => true
  | s::ss, u => decide (s.2+arity s.1 ≤ u.length) &&
      (branches s u).all (fun e => fits ss e.output)

theorem branches_shifted (pre u post : Word) (s : Step)
    (h : s.2+arity s.1 ≤ u.length) :
    branches (shiftStep pre.length s) (pre++u++post) =
      (branches s u).map (surround pre post) := by
  rcases s with ⟨op,i⟩
  simp only at h
  have hi : i ≤ u.length := by omega
  have ht : (pre++u++post).take (pre.length+i)=pre++u.take i := by
    rw [List.append_assoc,List.take_length_add_append,List.take_append_of_le_length hi]
  have hd : (pre++u++post).drop (pre.length+i)=u.drop i++post := by
    rw [List.append_assoc,List.drop_length_add_append,List.drop_append_of_le_length hi]
  have he : (pre++u++post).drop (pre.length+i+arity op)=u.drop (i+arity op)++post := by
    rw [Nat.add_assoc,List.append_assoc,List.drop_length_add_append,List.drop_append_of_le_length h]
  have ha : arity op ≤ (u.drop i).length := by simp only [List.length_drop]; omega
  have hbound : pre.length+i+arity op ≤ (pre++u++post).length := by
    simp only [List.length_append]; omega
  simp only [branches,transitions,shiftStep,h,hbound,↓reduceIte,ht,hd,he,
    List.take_append_of_le_length ha,List.flatMap_map,List.map_flatMap]
  simp [surround,List.map_map,Function.comp_def,List.append_assoc]

theorem frame_extend (pre post : Word) (p : Path) (e : Edge) :
    frame pre post (extend p e)=extend (frame pre post p) (surround pre post e) := by
  simp [frame,extend,List.map_append,surround]

theorem flatMap_congr_mem {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x∈xs, f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp),ih (by intro y hy; exact h y (by simp [hy]))]

theorem walk_context (ss : List Step) (pre post : Word) (p : Path)
    (h : fits ss p.output=true) :
    walk (ss.map (shiftStep pre.length)) (frame pre post p) =
      (walk ss p).map (frame pre post) := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih =>
    simp only [fits,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
    simp only [List.map_cons,walk]
    rw [show (frame pre post p).output=pre++p.output++post from rfl,
      branches_shifted pre p.output post s h.1]
    simp only [List.flatMap_map,List.map_flatMap,Function.comp_def,← frame_extend]
    apply flatMap_congr_mem
    intro e he
    exact ih (extend p e) (h.2 e he)

theorem downPaths_context (ss : List Step) (pre u post : Word)
    (h : fits ss.reverse u=true) :
    downPaths (ss.map (shiftStep pre.length)) (pre++u++post) =
      (downPaths ss u).map (frame pre post) := by
  simp only [downPaths,← walk_initial,← List.map_reverse]
  have hi : initial (pre++u++post)=frame pre post (initial u) := by rfl
  rw [hi]
  exact walk_context ss.reverse pre post (initial u) h

end WebMu.Revised.LocalPaths
