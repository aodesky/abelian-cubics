import Cubic.AllGaloisCounts.IntegerIntervalCount
import Cubic.AllGaloisCounts.MarkedFactorization

noncomputable section

namespace Cubic.AllGaloisCounts.MarkedLatticeData
open CountData IntegerIntervalCount
open Cubic.Counting.GeneralMonicCount (T)

/-- Integral coefficients `(a,r,v)` in the unique marked-factor parametrization. -/
def parameters (H : ℝ) : Set (ℤ × ℤ × ℤ) :=
  {p | |(p.1 : ℝ)| ≤ H ∧ p.2.2 ∈ vSet H p.1 p.2.1}

def toMarked (p : ℤ × ℤ × ℤ) : Polynomial ℤ × ℤ :=
  (MarkedFactorization.markedPolynomial p.1 p.2.1 p.2.2, p.2.1)

/-- The root sum is over all integers, as in `eqn:markedRootLatticeSum`. -/
def latticeSum (H : ℝ) : ℝ :=
  H ^ 2 * ∑ a ∈ T H, ∑' r : ℤ, F (r / H) (a / H)

end Cubic.AllGaloisCounts.MarkedLatticeData
