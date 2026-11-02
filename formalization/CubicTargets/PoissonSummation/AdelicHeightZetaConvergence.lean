import Cubic.PoissonSummation.AdelicFourierSpectrumMeasure
import CubicTargets.PoissonSummation.AdelicPeriodizationConvergence

/-!
# Concrete full target for `lemma:heightZetaConvergence`

All objects are fixed to the original adelic torus and rational-point height
series. The statement has no geometric or analytic data parameters and retains
every conclusion of the paper lemma. Its proof is in
`Cubic.PoissonSummation.AdelicHeightZetaConvergence`.
-/

namespace CubicTargets.PoissonSummation.AdelicHeightZetaConvergence

open MeasureTheory Cubic.PoissonSummation.AdelicHeightZetaData
open Cubic.PoissonSummation.AdelicQuotientMeasure
open Cubic.PoissonSummation.AdelicRationalCharacter
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  Cubic.PoissonSummation.ArchimedeanHaarData
  Cubic.PoissonSummation.RestrictedProductHaar
  Cubic.PoissonSummation.AdelicHeightZetaData
  Cubic.PoissonSummation.AdelicQuotientMeasure
  Cubic.PoissonSummation.AdelicFourierSpectrum

structure Claim : Prop extends toPeriodization : AdelicPeriodizationConvergence.Claim where
  fourier_integrable : ∀ (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure] (s₀ σ : ℂ), 0 < s₀.re → 1 < σ.re →
    Integrable (Cubic.PoissonSummation.AdelicFourierSpectrum.transform s₀ σ) ν

end CubicTargets.PoissonSummation.AdelicHeightZetaConvergence
