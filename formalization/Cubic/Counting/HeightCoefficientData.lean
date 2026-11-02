import Cubic.PoissonSummation.LeadingTermsData
import Cubic.PoissonSummation.QuadraticDirichletCharacter
import Cubic.PoissonSummation.HeightCountingData
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Objects in `eqn:dSummatoryForGeneralTrace`

`ζ_E(s) = ζ(s) L(s, χ₋₃)` uses mathlib's continuations of the Riemann zeta function
and the Dirichlet L-function. `DedekindFactorization` identifies this with the
ideal-counting Dedekind zeta function of `E = ℚ(√-3)` for `Re s > 1`.

`𝒵(s)` is the current paper's `Z₀(s)=(1−3⁻ˢ)²ξ(s)²R(s)`.
Internally its correction is `LeadingTermsData.correction (2*s)`.

`MeanValue` is the critical-line dyadic estimate used by the preceding
mean-value proof: `∫_U^{2U} |ζ_E(1/2+it)|² dt ≪_η U^{1+η}` for
`U ≥ 2`. It is a hypothesis of the lemmas that use it;
`TopacogullariMeanValue.meanValue` derives it from the black-box statement
`TopacogullariSecondMoment.BlackBox`. The current proof instead uses the
stronger `CriticalMeanSquare.Claim` and the direct Gaussian residue argument.
-/

noncomputable section

namespace Cubic.Counting.HeightCoefficientData

open Complex Cubic.PoissonSummation

/-- `ζ_E(s) = ζ(s) L(s, χ₋₃)`. -/
def zetaE (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction QuadraticDirichletCharacter.character s

/-- The continuation of `Z₀(s)`, factored through `ξ(s)²`. -/
def calZ (s : ℂ) : ℂ := zetaE s ^ 2 * LeadingTermsData.correction (2 * s)

/-- The Dirichlet coefficients `d_n` of `𝒵(s) = Z₀(s) = Σ d_n n^{-s}`. -/
def d (n : ℕ) : ℝ := HeightCountingData.count n

/-- The mean value of `|ζ_E|²` on the critical line, as quoted in the paper from
[Topacogullari 2021, Theorem 1.5]. -/
def MeanValue : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∀ U : ℝ, 2 ≤ U →
    ∫ t in U..2 * U, ‖zetaE ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ K * U ^ (1 + η)

end Cubic.Counting.HeightCoefficientData
