import Cubic.PoissonSummation.AdelicFourierSpectrumMeasure
import Cubic.PoissonSummation.RealFourierInversion

/-!
# Determining the dual-Haar scalar from quotient Fourier inversion

The actual quotient coordinate has measure `du/6`. Test its dual inversion
property on a nonvanishing integrable function of that coordinate, using the
already constructed archimedean height with parameters `(1,1)`. Its real
Fourier transform is integrable and its inversion is proved in mathlib.
This fixes the previously undetermined scalar of the full dual Haar measure's
restriction to the surviving spectrum. Real inversion is used only to verify
the dual-measure normalization; the adelic Poisson application remains separate.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicDualNormalization

open MeasureTheory Filter Set
open AdelicRationalCharacter AdelicLevelQuotient AdelicQuotientMeasure AdelicFourierSpectrum
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicQuotientMeasure
  AdelicFourierSpectrum NNReal ENNReal

theorem character_coordinate (t : ℝ) (q : AutomorphicQuotient) :
    automorphicCharacter t q = Circle.exp (2 * Real.pi * t * quotientRealCoordinate q) := by
  rw [automorphicCharacter_eq_map]
  rfl

/-- A nonvanishing `L¹` test function on the actual quotient, independently of Poisson. -/
def referenceFunction (q : AutomorphicQuotient) : ℂ :=
  ArchimedeanFourier.inverseHeight 1 1 (quotientRealCoordinate q)

def referenceTransform (χ : PontryaginDual AutomorphicQuotient) : ℂ :=
  characterIntegral quotientMeasure referenceFunction χ

theorem reference_integrable : Integrable referenceFunction quotientMeasure := by
  have hc := ArchimedeanFourier.continuous_inverseHeight (1 : ℂ) (1 : ℂ)
  apply (integrable_map_measure hc.aestronglyMeasurable
    measurable_quotientRealCoordinate.aemeasurable).mp
  rw [map_quotientMeasure_coordinate]
  exact (ArchimedeanFourier.integrable_inverseHeight 1 1 (by norm_num) (by norm_num)).smul_measure
    (by norm_num)

theorem reference_ne_zero (q : AutomorphicQuotient) : referenceFunction q ≠ 0 :=
  Complex.exp_ne_zero _

theorem referenceTransform_support : Function.support referenceTransform ⊆ levelAnnihilator := by
  intro χ hχ k hk
  by_contra hn
  apply hχ
  apply characterIntegral_eq_zero_of_invariant quotientMeasure referenceFunction χ k _ hn
  intro q
  have hk' : AdelicCompactQuotient.quotientCoordinate k = 1 := quotientLevel_le_ker hk
  simp only [referenceFunction, quotientRealCoordinate, map_mul, hk', one_mul]

/-- The factor `1/6` is obtained from the actual quotient pushforward. -/
theorem referenceTransform_parameter (t : ℝ) :
    referenceTransform (automorphicCharacter t) =
      (1 / 6 : ℂ) * ArchimedeanFourier.fourier 1 1 t := by
  let g : ℝ → ℂ := ArchimedeanFourier.integrand 1 1 t
  have hc : Continuous g := by
    apply (ArchimedeanFourier.continuous_inverseHeight 1 1).mul
    apply Continuous.inv₀
    · exact continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop))
    · intro u
      exact (ArchimedeanFourier.character t u).coe_ne_zero
  calc
    referenceTransform (automorphicCharacter t) =
        ∫ q, g (quotientRealCoordinate q) ∂quotientMeasure := by
      unfold referenceTransform characterIntegral
      apply integral_congr_ae
      filter_upwards with q
      rw [character_coordinate]
      rfl
    _ = ∫ u, g u ∂(quotientMeasure.map quotientRealCoordinate) :=
      (integral_map measurable_quotientRealCoordinate.aemeasurable hc.aestronglyMeasurable).symm
    _ = _ := by
      rw [map_quotientMeasure_coordinate, integral_smul_measure]
      norm_num [Complex.real_smul, g, ArchimedeanFourier.fourier]

theorem referenceTransform_integrable (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure] : Integrable referenceTransform ν := by
  rw [integrable_iff_coordinate ν referenceTransform referenceTransform_support]
  simp only [referenceTransform_parameter]
  exact (ArchimedeanFourier.integrable_fourier 1 1 (by norm_num) (by norm_num)).const_mul _

theorem reference_reconstruction (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure] (q : AutomorphicQuotient) :
    (∫ χ, referenceTransform χ * (χ q : ℂ) ∂ν) =
      ((spectralScalar ν : ℂ) / 6) * referenceFunction q := by
  have hsupp : Function.support (fun χ : PontryaginDual AutomorphicQuotient =>
      referenceTransform χ * (χ q : ℂ)) ⊆ levelAnnihilator := by
    intro χ hχ
    exact referenceTransform_support (left_ne_zero_of_mul hχ)
  rw [integral_eq_scalar_mul ν _ hsupp]
  simp only [referenceTransform_parameter, character_coordinate]
  have he : (fun t : ℝ => (1 / 6 : ℂ) * ArchimedeanFourier.fourier 1 1 t *
      (Circle.exp (2 * Real.pi * t * quotientRealCoordinate q) : ℂ)) =
      fun t => (1 / 6 : ℂ) * ((ArchimedeanFourier.character t (quotientRealCoordinate q) : ℂ) *
        ArchimedeanFourier.fourier 1 1 t) := by
    funext t
    unfold ArchimedeanFourier.character
    ring
  rw [he, integral_const_mul, ArchimedeanFourier.fourier_inversion 1 1
    (by norm_num) (by norm_num)]
  unfold referenceFunction
  ring

/-- Fourier normalization on the full quotient forces the restricted measure
to be `6 dt`; the scalar is proved, not chosen in a measure definition. -/
theorem spectralScalar_eq_six (ν : Measure (PontryaginDual AutomorphicQuotient))
    [ν.IsHaarMeasure]
    (hInv : ∀ F : AutomorphicQuotient → ℂ,
      let Fhat := fun χ : PontryaginDual AutomorphicQuotient =>
        ∫ q, F q * (χ q : ℂ)⁻¹ ∂quotientMeasure
      Integrable F quotientMeasure → Integrable Fhat ν →
        ∀ᵐ q ∂quotientMeasure, F q = ∫ χ, Fhat χ * (χ q : ℂ) ∂ν) :
    spectralScalar ν = 6 := by
  have hAE := hInv referenceFunction reference_integrable (referenceTransform_integrable ν)
  obtain ⟨q, hq⟩ := hAE.exists
  change referenceFunction q = ∫ χ, referenceTransform χ * (χ q : ℂ) ∂ν at hq
  rw [reference_reconstruction] at hq
  have hc : (spectralScalar ν : ℂ) / 6 = 1 :=
    mul_right_cancel₀ (reference_ne_zero q) (hq.symm.trans (one_mul _).symm)
  have he : (spectralScalar ν : ℂ) = 6 := (div_eq_one_iff_eq (by norm_num)).mp hc
  exact_mod_cast he

end Cubic.PoissonSummation.AdelicDualNormalization
