import Cubic.PoissonSummation.HeightZetaFormulaData
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Full concrete target for `thm:heightZetaFunctionFormula2`

All heights, points and the integral locus are the original adelic objects.
The two complex parameters range over the full invariant divisor space;
neither `Re(s₀)>0` nor `Re(σ)>1` is assumed in the theorem's conclusion.

Continuation is witnessed by a single meromorphic function of
`z=(s₀+2σ)/2`, agreeing with the original series throughout its full convergence
region. Pullback through this linear parameter gives the multivariate
continuation on `Re(s₀+2σ)>1`; this is not a restriction to a one-dimensional
slice. The paper itself constructs a continuation depending only on `z`.

This is a statement, not an assumed theorem. The assumed general Poisson
input will be explicit in any proof which uses it; it is not an axiom here.
-/

namespace CubicTargets.PoissonSummation.HeightZetaFunctionFormula

open Cubic.PoissonSummation
open AdelicHeightZetaData HeightZetaFormulaData FiniteEulerProduct
open scoped Cubic.QuadraticCorrespondence.RationalQuotientGroup

structure Claim : Prop where
  series_absolute : ∀ s₀ σ : ℂ, 2 < (s₀ + 2 * σ).re →
    Summable (fun P : IntegralRationalPoints => ‖zetaTerm s₀ σ P‖)
  inert_product_absolute : ∀ z : ℂ, 1 < z.re →
    Summable (fun q : InertPrimes => ‖inertCorrection q z - 1‖)
  split_product_absolute : ∀ z : ℂ, 1 < z.re →
    Summable (fun p : SplitPrimes => ‖splitCorrection p z - 1‖)
  euler_formula : ∀ s₀ σ : ℂ, 2 < (s₀ + 2 * σ).re →
    heightZeta s₀ σ = eulerExpression (parameter s₀ σ)
  meromorphic_continuation : ∃ F : ℂ → ℂ,
    MeromorphicOn F {z : ℂ | (1 / 2 : ℝ) < z.re} ∧
    ∀ s₀ σ : ℂ, 2 < (s₀ + 2 * σ).re → heightZeta s₀ σ = F (parameter s₀ σ)

end CubicTargets.PoissonSummation.HeightZetaFunctionFormula
