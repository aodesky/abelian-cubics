import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.PoissonSummation.FiniteEulerProduct
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The displayed expression in `thm:heightZetaFunctionFormula2`

Invariant divisor parameters are `(s₀,σ,σ)`, with both `s₀` and `σ` complex.
These definitions describe only the proposed right-hand side. The original
height series remains independently defined in `AdelicHeightZetaData`.
Neither the infinite products nor this expression assume convergence.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaFormulaData

open FiniteEulerProduct

/-- The linear parameter `(s₀+s₁+s₂)/2` on the entire invariant parameter space. -/
def parameter (s₀ σ : ℂ) : ℂ := s₀ / 2 + σ

/-- The inert factor after extracting the Riemann zeta function. -/
def inertCorrection (q : InertPrimes) (z : ℂ) : ℂ :=
  (1 + (q.1 : ℂ) ^ (-z))⁻¹

/-- The split factor after extracting the Riemann zeta function. -/
def splitCorrection (p : SplitPrimes) (z : ℂ) : ℂ :=
  1 + 3 * (p.1 : ℂ) ^ (-z) / (1 - (p.1 : ℂ) ^ (-z))

/-- The paper's displayed Euler expression, independently of the height series. -/
def eulerExpression (z : ℂ) : ℂ :=
  (1 - (3 : ℂ) ^ (-z)) * riemannZeta z *
    (∏' q : InertPrimes, inertCorrection q z) *
    (∏' p : SplitPrimes, splitCorrection p z)

end Cubic.PoissonSummation.HeightZetaFormulaData
