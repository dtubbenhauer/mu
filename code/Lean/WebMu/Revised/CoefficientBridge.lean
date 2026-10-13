import WebMu.Revised.Gauge
import WebMu.Revised.TensorInduction

namespace WebMu.Revised.Algebra
open Laurent

theorem ofList_sum (ps : List Laurent) : ofList (Laurent.sum ps) = sumP (ps.map ofList) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [Laurent.sum, ofList_add, List.map_cons, sumP, ih]

theorem ofList_total {ι : Type} (is : List ι) (f : ι → Laurent) :
    ofList (Laurent.sum (is.map f)) = total is (fun i => ofList (f i)) := by
  simp only [ofList_sum, total, List.map_map, Function.comp_def]

theorem total_foldl {ι : Type} (is : List ι) (f : ι → Poly) (p : Poly) :
    is.foldl (fun a i => a + f i) p = p + total is f := by
  induction is generalizing p with
  | nil => simp
  | cons i is ih => simp only [List.foldl_cons, ih, total_cons, poly_add_assoc]

theorem ofList_foldl {ι : Type} (is : List ι) (f : ι → Laurent) (p : Laurent) :
    ofList (is.foldl (fun a i => add a (f i)) p) = ofList p + total is (fun i => ofList (f i)) := by
  induction is generalizing p with
  | nil => simp
  | cons i is ih => simp only [List.foldl_cons, ih, ofList_add, total_cons, poly_add_assoc]

theorem ofList_step {ι : Type} (is : List ι) (a : ι → ι → Laurent) (x : ι → Laurent) (i : ι) :
    ofList (step is a x i) = action is (fun i j => ofList (a i j)) (fun j => ofList (x j)) i := by
  simp only [step, ofList_total, ofList_mul, action]

theorem ofList_wordIterate {ι ε : Type} (is : List ι)
    (a : ε → ι → ι → Laurent) (q : ι → Laurent) (es : List ε) :
    (fun i => ofList (wordIterate is a q es i)) =
      wordAction is (fun e i j => ofList (a e i j)) (fun i => ofList (q i)) es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    funext i
    simp only [wordIterate,ofList_step,wordAction,ih]

theorem ofList_tensorCoefficient {ι ε : Type} (is : List ι)
    (p : ι → Laurent) (a : ε → ι → ι → Laurent) (q : ι → Laurent) (es : List ε) :
    ofList (tensorCoefficient is p a q es) = pairing is (fun i => ofList (p i))
      (wordAction is (fun e i j => ofList (a e i j)) (fun i => ofList (q i)) es) := by
  simp only [tensorCoefficient,ofList_total,ofList_mul,pairing,
    congrFun (ofList_wordIterate is a q es)]

theorem coefficient_total {ι : Type} (is : List ι) (f : ι → Poly) (d : Int) :
    coefficient (total is f) d = (is.map (fun i => coefficient (f i) d)).sum := by
  induction is <;> simp_all [coefficient_add]

end WebMu.Revised.Algebra
