import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.PoissonSummation.CoefficientArithmetic

/-!
# Actual height fibers for the introductory height-zeta theorem

The fibers are defined from the independently constructed adelic height on
the original integral rational points. Their cardinalities are not defined
by Dirichlet coefficients or the desired divisor formula. Finiteness is
proved separately, since `Nat.card` alone would not express it.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightCountingData

open AdelicHeightZetaData

def pointHeight (P : IntegralRationalPoints) : ℂ :=
  height 1 0 (RationalAdelicEmbedding.diagonal P.val)

def Fiber (n : ℕ) := {P : IntegralRationalPoints // pointHeight P = (Real.sqrt n : ℂ)}

def count (n : ℕ) : ℕ := Nat.card (Fiber n)

/-- The paper's literal divisor sum, with its integer-valued inert signs. -/
def divisorFormula (n : ℕ) : ℤ := ∑ d ∈ n.divisors,
  (3 : ℤ) ^ ArithmeticFunction.cardDistinctFactors (primeResiduePart 1 d) *
  (-1 : ℤ) ^ ArithmeticFunction.cardFactors (primeResiduePart 2 d)

end Cubic.PoissonSummation.HeightCountingData
