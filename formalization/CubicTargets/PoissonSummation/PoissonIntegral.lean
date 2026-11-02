import Cubic.PoissonSummation.AdelicSpectralIntegrand

/-!
# Concrete full target for `lemma:poissonIntegral`

Both sides use the original objects: the reciprocal-height sum over integral
rational points, and actual local Haar integrals of the height and inverse
automorphic character. The scalar six is the paper's dual-measure factor.
Defining this proposition does not assume its equality. Any proof using the
assumed general Poisson input must retain that input as an explicit hypothesis.
-/

namespace CubicTargets.PoissonSummation.PoissonIntegral

open MeasureTheory Cubic.PoissonSummation

structure Claim : Prop where
  series_absolute : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
    Summable (fun P : AdelicHeightZetaData.IntegralRationalPoints =>
      ‖AdelicHeightZetaData.zetaTerm s₀ σ P‖)
  spectral_integrable : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
    Integrable (AdelicSpectralIntegrand.integrand s₀ σ)
  poisson_equality : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
    AdelicHeightZetaData.heightZeta s₀ σ =
      6 * ∫ t : ℝ, AdelicSpectralIntegrand.integrand s₀ σ t

end CubicTargets.PoissonSummation.PoissonIntegral
