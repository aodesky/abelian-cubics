import Cubic.BoxAsymptotic.ZeroModeSeries
import Cubic.BoxAsymptotic.ZeroModeLaurent
import CubicTargets.BoxAsymptotic.ZeroMode

/-!
# `eq:F0`: the actual mass series, its Euler product, and its Laurent coefficients

The mass table is proved from the congruences, the convergent sum is rearranged using
the unique decomposition `n = 3^e M`, and its coefficients at the double pole are
computed by differentiating an analytic numerator. Convergence uses the direct
fourfold divisor majorant and the split/inert Euler factors.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.ZeroMode

open Cubic.BoxAsymptotic.ZeroModeData CubicTargets.BoxAsymptotic
open Cubic.PoissonSummation

theorem «eq:F0» : ZeroModeClaim := by
  refine ⟨fun s hs => ?_, ZeroModeLaurent.numerator_one,
    ZeroModeLaurent.derivative_real, ZeroModeLaurent.laurent⟩
  have h := ZeroModeSeries.series_hasSum s hs
  exact ⟨h.summable, h.tsum_eq⟩

/-- The first line of `eq:F0`, with the ideal-counting Dedekind zeta function. -/
theorem dedekind_formula
    (s : ℂ) (hs : 1 < s.re) :
    series s = (1 / 3) * (1 + 2 * (3 : ℂ) ^ (-(2 * s))) * (1 - (3 : ℂ) ^ (-s)) *
      NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E s ^ 2 *
      HeightZetaCorrectionProduct.value s := by
  rw [(«eq:F0»).1 s hs |>.2, continuation, QuadraticZetaRegularization.value,
    ← QuadraticDedekindFactorization.factorization s hs]
  rfl

/-- The lower Laurent coefficient, in the trace-one constants of the manuscript. -/
theorem lower_coefficient : b₀ = aStar *
    (1 + 2 * Cubic.Counting.AsymptoticConstantsData.originalSecondaryRatio -
      19 / 22 * Real.log 3) := by
  rw [b₀, ZeroModeLaurent.numerator_derivative, Complex.ofReal_re]

end Cubic.BoxAsymptotic.ZeroMode
