import WebMu.Revised.Algebra

namespace WebMu.Revised.Algebra
open Laurent

/-- q=v² followed by multiplication by v⁻δ. -/
def substituteKL (delta : Int) (p : Laurent) : Laurent :=
  p.map (fun (i,a) => (2*i-delta,a))

theorem substituteKL_coefficient (p : Laurent) (delta k : Int)
    (hdelta : delta = 2*k+1) :
    coeff (substituteKL delta p) (-1) = coeff p k := by
  induction p with
  | nil => rfl
  | cons term p ih =>
    rcases term with ⟨i,a⟩
    simp only [substituteKL,List.map_cons,coeff] at ih ⊢
    have he : 2*i-delta = -1 ↔ i = k := by omega
    simp only [he,ih]

end WebMu.Revised.Algebra
