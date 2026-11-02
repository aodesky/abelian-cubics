import Cubic.PoissonSummation.ArchimedeanHaar

/-!
# Fourier integration on the original real torus

The integrand uses the full adelic height and inverse descended automorphic
character restricted to infinity. The proved logarithmic pushforward transfers
both integrability and the integral to the already evaluated real-coordinate
integral. This is a local measure comparison, without a global quotient measure.
-/

noncomputable section

namespace Cubic.PoissonSummation.ArchimedeanTorusFourier

open MeasureTheory ArchimedeanHaarData
open Cubic.ToricHeights.ArchimedeanQuotientLogarithm (coordinate continuous_coordinate)
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology ArchimedeanHaarData

/-- The local component of the descended character has the same radial formula. -/
theorem integrand_eq (s₀ σ : ℂ) (t : ℝ) (x : Points) :
    integrand s₀ σ t x = ArchimedeanFourier.integrand s₀ σ t (coordinate x) := by
  simpa only [integrand, AdelicRationalCharacter.automorphicCharacter_mk,
    AdelicFourierComponents.infiniteIntegrand] using
    AdelicFourierComponents.infiniteIntegrand_eq s₀ σ t x

/-- Actual torus integrability holds on the larger local range `Re σ > 0`. -/
theorem integrable (μ : Measure Points) (hμ : NormalizedHaar μ)
    (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    Integrable (integrand s₀ σ t) μ := by
  have hi : Integrable (ArchimedeanFourier.integrand s₀ σ t) (μ.map coordinate) := by
    rw [hμ.2]
    exact ArchimedeanFourier.integrable s₀ σ t h₀ hσ
  have h := (integrable_map_measure hi.aestronglyMeasurable
    continuous_coordinate.measurable.aemeasurable).mp hi
  simpa only [Function.comp_def, ← integrand_eq] using h

/-- Equality of actual torus and coordinate integrals with exactly the paper's scalar. -/
theorem fourier_eq_coordinate (μ : Measure Points) (hμ : NormalizedHaar μ)
    (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    fourier μ s₀ σ t = ArchimedeanFourier.fourier s₀ σ t := by
  have hi : Integrable (ArchimedeanFourier.integrand s₀ σ t) (μ.map coordinate) := by
    rw [hμ.2]
    exact ArchimedeanFourier.integrable s₀ σ t h₀ hσ
  unfold fourier
  simp_rw [integrand_eq]
  rw [← integral_map continuous_coordinate.measurable.aemeasurable hi.aestronglyMeasurable,
    hμ.2]
  rfl

theorem fourier_eq_sum (μ : Measure Points) (hμ : NormalizedHaar μ)
    (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    fourier μ s₀ σ t = 1 / (s₀ + 2 * Real.pi * Complex.I * t) +
      1 / (2 * σ - 2 * Real.pi * Complex.I * t) := by
  rw [fourier_eq_coordinate μ hμ s₀ σ t h₀ hσ]
  exact ArchimedeanFourier.fourier_eq_sum s₀ σ t h₀ hσ

theorem fourier_eq_fraction (μ : Measure Points) (hμ : NormalizedHaar μ)
    (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    fourier μ s₀ σ t = (s₀ + 2 * σ) /
      ((s₀ + 2 * Real.pi * Complex.I * t) * (2 * σ - 2 * Real.pi * Complex.I * t)) := by
  rw [fourier_eq_coordinate μ hμ s₀ σ t h₀ hσ]
  exact ArchimedeanFourier.fourier_eq_fraction s₀ σ t h₀ hσ

end Cubic.PoissonSummation.ArchimedeanTorusFourier
