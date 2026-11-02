import Cubic.PoissonSummation.AdelicData
import Cubic.PoissonSummation.AdelicRationalCharacter
import Cubic.PoissonSummation.FiniteAdelicFourier
import Cubic.PoissonSummation.ArchimedeanFourier

/-!
# Local Fourier integrands of the assembled adelic height

Restrict the independently constructed adelic height and its proved descended
automorphic character to their local components. At finite places their actual Haar integrals are
the already evaluated ones. At infinity the original-point integrand factors
through the logarithmic coordinate, with the exact inverse-character sign.

The archimedean integral below is explicitly in the radial coordinate with
Lebesgue measure. `ArchimedeanHaar` and `ArchimedeanTorusFourier` prove its
comparison with the original torus Haar integral. No global Fourier factorization
is asserted here.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicFourierComponents

open MeasureTheory
open Cubic.ToricHeights QuotientFiniteFourierProduct
open scoped Cubic.QuadraticCorrespondence.RationalQuotientGroup

/-- The full adelic height and descended automorphic character, with the original finite cutoff. -/
def finiteIntegrand (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ) (x : (family p).Carrier) : ℂ :=
  (family p).integralLocus.indicator
      (fun y => AdelicData.inverseHeight s₀ σ (AdelicData.includeFinite p y)) x *
    ((AdelicRationalCharacter.automorphicCharacter t
      (QuotientGroup.mk (AdelicData.includeFinite p x)) : Circle) : ℂ)⁻¹

theorem finiteIntegrand_eq (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ) :
    finiteIntegrand p s₀ σ t = FiniteAdelicFourier.integrand p s₀ σ t := by
  funext x
  simp only [finiteIntegrand, FiniteAdelicFourier.integrand,
    AdelicData.inverseHeight_includeFinite, AdelicRationalCharacter.automorphicCharacter_finite,
    FiniteAdelicData.inverseHeight_includeLocal, FiniteAdelicData.character_includeLocal]

theorem finite_integrable (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Integrable (finiteIntegrand p s₀ σ t) (family p).measure := by
  rw [finiteIntegrand_eq]
  exact FiniteAdelicFourier.local_integrable p s₀ σ t hσ

theorem finite_integral_eq (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ) :
    (∫ x, finiteIntegrand p s₀ σ t x ∂(family p).measure) =
      FiniteAdelicFourier.localFourier p s₀ σ t := by
  rw [finiteIntegrand_eq]
  rfl

/-- This product of local integrals inherits its convergence from the analytic local theorem. -/
theorem finite_integrals_multipliable (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Multipliable (fun p : Nat.Primes => ∫ x, finiteIntegrand p s₀ σ t x ∂(family p).measure) := by
  simp only [finite_integral_eq]
  exact FiniteAdelicFourier.multipliable_localFourier s₀ σ t hσ

theorem finite_integrals_product (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    (∏' p : Nat.Primes, ∫ x, finiteIntegrand p s₀ σ t x ∂(family p).measure) =
      FiniteEulerProduct.value (FiniteEulerProduct.spectralParameter σ t) := by
  simp only [finite_integral_eq]
  exact FiniteAdelicFourier.spectral_product s₀ σ t hσ

/-- The paper's finite Fourier part: a product of actual local Haar integrals
of the adelic height and the inverse descended automorphic character. -/
def finiteFourier (s₀ σ : ℂ) (t : ℝ) : ℂ :=
  ∏' p : Nat.Primes, ∫ x, finiteIntegrand p s₀ σ t x ∂(family p).measure

/-- The previously evaluated original-point integrals are these adelic components. -/
theorem finiteFourier_eq (s₀ σ : ℂ) (t : ℝ) :
    finiteFourier s₀ σ t =
      CubicTargets.PoissonSummation.FiniteFourierProduct.finiteFourier family s₀ σ t := by
  simp only [finiteFourier, finite_integral_eq, FiniteAdelicFourier.localFourier_eq,
    CubicTargets.PoissonSummation.FiniteFourierProduct.finiteFourier]

/-- The unrestricted archimedean integrand on original real quotient points. -/
def infiniteIntegrand (s₀ σ : ℂ) (t : ℝ) (x : ArchimedeanQuotientLogarithm.Points) : ℂ :=
  AdelicData.inverseHeight s₀ σ (AdelicData.includeInfinite x) *
    ((AdelicData.character t (AdelicData.includeInfinite x) : Circle) : ℂ)⁻¹

/-- Factorization through the original point's logarithmic coordinate, before integration. -/
theorem infiniteIntegrand_eq (s₀ σ : ℂ) (t : ℝ) (x : ArchimedeanQuotientLogarithm.Points) :
    infiniteIntegrand s₀ σ t x =
      ArchimedeanFourier.integrand s₀ σ t (ArchimedeanQuotientLogarithm.coordinate x) := by
  simp only [infiniteIntegrand, AdelicData.inverseHeight_includeInfinite,
    AdelicData.character_includeInfinite, ArchimedeanQuotientLogarithm.inverseHeight_eq,
    ArchimedeanQuotientLogarithm.character_eq, ArchimedeanFourier.integrand,
    ArchimedeanFourier.inverseHeight, ArchimedeanFourier.character]

theorem infiniteIntegrand_radialSection (s₀ σ : ℂ) (t u : ℝ) :
    infiniteIntegrand s₀ σ t (ArchimedeanQuotientLogarithm.radialSection u) =
      ArchimedeanFourier.integrand s₀ σ t u := by
  rw [infiniteIntegrand_eq, ArchimedeanQuotientLogarithm.coordinate_radialSection]

/-- Integrability in `du`; the torus measure comparison is supplied in `ArchimedeanHaar`. -/
theorem radial_integrable (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    Integrable (fun u : ℝ =>
      infiniteIntegrand s₀ σ t (ArchimedeanQuotientLogarithm.radialSection u)) := by
  simp only [infiniteIntegrand_radialSection]
  exact ArchimedeanFourier.integrable s₀ σ t h₀ hσ

/-- The two denominator signs for the original height and character along the radial section. -/
theorem radial_integral_eq_sum (s₀ σ : ℂ) (t : ℝ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    (∫ u : ℝ, infiniteIntegrand s₀ σ t (ArchimedeanQuotientLogarithm.radialSection u)) =
      1 / (s₀ + 2 * Real.pi * Complex.I * t) +
        1 / (2 * σ - 2 * Real.pi * Complex.I * t) := by
  simp only [infiniteIntegrand_radialSection]
  exact ArchimedeanFourier.fourier_eq_sum s₀ σ t h₀ hσ

end Cubic.PoissonSummation.AdelicFourierComponents
