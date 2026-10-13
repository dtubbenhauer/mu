import WebMu.Revised.Sparse

/-! Exact separation of the original block into its four signed web entries.
No coordinate change, conjugation, or bar operator occurs in this file. -/
namespace WebMu.Revised
open Laurent Algebra

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def encodeExterior (x : Tensor) : Std.HashMap Nat Laurent :=
  x.fold (fun out w p => accumulate out (encode w) p) ∅

def separatedBlock (j : Nat) : Column :=
  if j < 27 then addMap (splitColumn (rawB j)) (putRow (encodeExterior (rawD j)) 27)
  else addMap (scaleMap (splitColumn rawC) (monomial 0 (-1)))
    (putRow (scaleMap (encodeExterior tau3) (neg d)) 27)

def separatedTail : Column := addMap (splitColumn rawQ) (putRow (encodeExterior tau2) 27)

theorem original_block_separation_check : ∀ j : Fin 28,
    sameEntries (block j) (separatedBlock j) = true := by native_decide

theorem original_block_separation (j : Fin 28) (key : Nat × Nat) :
    (block j).getD key [] = (separatedBlock j).getD key [] :=
  sameEntries_getD _ _ (original_block_separation_check j) key

theorem original_tail_separation_check : sameEntries tail separatedTail = true := by native_decide

theorem original_tail_separation (key : Nat × Nat) :
    tail.getD key [] = separatedTail.getD key [] :=
  sameEntries_getD _ _ original_tail_separation_check key

theorem splitColumn_poly (x : Tensor) (i w : Nat) :
    ofList ((splitColumn x).getD (i,w) []) =
    total x.toList (fun (s,p) =>
      if (encode (s.take 3),encode (s.drop 3)) == (i,w) then ofList p else 0) := by
  exact hashmap_fold_poly x (fun s => (encode (s.take 3),encode (s.drop 3))) (fun _ p => p) (i,w)

theorem encodeExterior_poly (x : Tensor) (w : Nat) :
    ofList ((encodeExterior x).getD w []) =
    total x.toList (fun (s,p) => if encode s == w then ofList p else 0) := by
  exact hashmap_fold_poly x encode (fun _ p => p) w

theorem original_C_signed : inputSigns 12 (cSteps ++
    [(.cup,0),(.cup,0),(.cup,0),(.cup,0)]) = some [] := by decide

end WebMu.Revised
