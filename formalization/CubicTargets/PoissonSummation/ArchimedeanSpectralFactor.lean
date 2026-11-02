import Cubic.PoissonSummation.ArchimedeanHaarData

/-!
# Concrete target for `eqn:archimedeanSpectralFactor`

The target includes existence and uniqueness of the paper-normalized Haar
measure, and asserts the formula for every measure with that normalization.
Thus normalization is not an undischarged existence assumption. All point spaces,
heights, logarithms and automorphic characters are the original constructed data.

The surrounding Poisson argument has `Re s₀ > 0`, `Re σ > 1`, and real `t`.
The target retains this parameter range and both displayed equalities, together
with integrability of the actual torus integrand.
-/

noncomputable section

namespace CubicTargets.PoissonSummation.ArchimedeanSpectralFactor

open MeasureTheory Cubic.PoissonSummation.ArchimedeanHaarData
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  Cubic.PoissonSummation.ArchimedeanHaarData

/-- Full concrete target, with measure construction and analytic prerequisites retained. -/
structure Claim : Prop where
  exists_measure : ∃ μ : Measure Points, NormalizedHaar μ
  unique_measure : ∀ μ ν : Measure Points, NormalizedHaar μ → NormalizedHaar ν → μ = ν
  integrable : ∀ (μ : Measure Points), NormalizedHaar μ →
    ∀ (s₀ σ : ℂ) (t : ℝ), 0 < s₀.re → 1 < σ.re → Integrable (integrand s₀ σ t) μ
  sum_formula : ∀ (μ : Measure Points), NormalizedHaar μ →
    ∀ (s₀ σ : ℂ) (t : ℝ), 0 < s₀.re → 1 < σ.re →
    fourier μ s₀ σ t = 1 / (s₀ + 2 * Real.pi * Complex.I * t) +
      1 / (2 * σ - 2 * Real.pi * Complex.I * t)
  fraction_formula : ∀ (μ : Measure Points), NormalizedHaar μ →
    ∀ (s₀ σ : ℂ) (t : ℝ), 0 < s₀.re → 1 < σ.re →
    fourier μ s₀ σ t = (s₀ + 2 * σ) /
      ((s₀ + 2 * Real.pi * Complex.I * t) * (2 * σ - 2 * Real.pi * Complex.I * t))

end CubicTargets.PoissonSummation.ArchimedeanSpectralFactor
