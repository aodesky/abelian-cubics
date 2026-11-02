import Cubic.Introduction.CubeIdealSumData
import Mathlib.Analysis.Analytic.Basic

/-! Kühleitner–Nowak, arXiv:math/0307221, Corollary 2, in the equivalent
residue form supplied by the Theorem on PDF p.2. The coefficients below
are actual ideal counts of a fixed quadratic field, not arbitrary
arithmetic functions. Equations (4.4) and the ensuing Euler-product
calculation supply absolute convergence on `Re s>1`.

If `F(s)=(s−1)² D(s)` near one, the residue of `D(s)X^s/s` is
`F(1)X log X + (F'(1)−F(1))X`. Analyticity and agreement on a genuine
right-neighborhood uniquely determine those two coefficients.
No cubic-point comparison or removal of a local factor is assumed here.
-/

namespace CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum

open Cubic.Introduction.CubeIdealSumData Filter Asymptotics
open scoped Topology

structure FieldInput (K : Type) [Field K] [NumberField K] : Prop where
  absolute : ∀ s : ℂ, 1 < s.re → LSeriesSummable (coefficient K) s
  estimate : ∀ F : ℂ → ℂ, AnalyticAt ℂ F 1 →
    (∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ),
      F t = ((t : ℂ) - 1) ^ 2 * LSeries (coefficient K) t) →
    (fun X : ℝ => summatory K X -
      (F 1 * X * Real.log X + (deriv F 1 - F 1) * X)) =O[atTop] error

def BlackBox : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → FieldInput K

end CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum
