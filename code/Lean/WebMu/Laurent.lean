import Std

/-! Exact sparse Laurent arithmetic. Exponents are powers of v, not t.
    A polynomial is represented by nonzero terms in strictly increasing order.
    The finite certificate checks this invariant on its inputs and outputs. -/
namespace WebMu

abbrev Laurent := List (Int × Int)

namespace Laurent

def monomial (degree : Int) (coefficient : Int := 1) : Laurent :=
  if coefficient == 0 then [] else [(degree, coefficient)]

def one : Laurent := monomial 0

def add : Laurent → Laurent → Laurent
  | [], q => q
  | p, [] => p
  | (i, a) :: ps, (j, b) :: qs =>
    if i < j then (i, a) :: add ps ((j, b) :: qs)
    else if j < i then (j, b) :: add ((i, a) :: ps) qs
    else if a + b == 0 then add ps qs else (i, a + b) :: add ps qs
termination_by p q => p.length + q.length

def shiftScale (p : Laurent) (degree coefficient : Int) : Laurent :=
  if coefficient == 0 then [] else p.map fun (i, a) => (i + degree, a * coefficient)

def mul : Laurent → Laurent → Laurent
  | [], _ => []
  | (i,a) :: p, q => add (shiftScale q i a) (mul p q)

def neg (p : Laurent) : Laurent := p.map fun (i, a) => (i, -a)

def pow (p : Laurent) : Nat → Laurent
  | 0 => one
  | n + 1 => mul p (pow p n)

def coeff : Laurent → Int → Int
  | [], _ => 0
  | (i,a) :: rest, degree => (if i = degree then a else 0) + coeff rest degree

def canonical : Laurent → Bool
  | [] => true
  | [(_, a)] => a != 0
  | (i, a) :: (j, b) :: rest =>
    a != 0 && i < j && canonical ((j, b) :: rest)

/-- Membership in Z[t^2], where t = v^(-1). -/
def integralEven (p : Laurent) : Bool :=
  canonical p && p.all (fun (i, _) => i ≤ 0 && i % 2 == 0)

end Laurent
end WebMu
