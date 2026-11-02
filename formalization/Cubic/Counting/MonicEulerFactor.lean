import CubicTargets.Counting.GeneralMonic
import Cubic.PoissonSummation.LeadingTermsSimplifiedDerivative

/-!
# Proof of `eqn:monicEulerFactor`

With `s = 2z`, the local factor `1 - 2/(p^z(p^z+1))` is the split factor of the correction
product `E(s)` of `prop:leadingTerms`, so for `Re z > 1/2` its product converges absolutely
(`LeadingTermsSplitProduct.absolute`). The simplified Euler product of `E(s)`
(`LeadingTermsEulerProduct.correction_formula`) then gives
`𝓔_mon(z) = (1 + 2·3^{-2z}) / (3(1 - 3^{-z})) · E(2z)`,
and at `z = 1` this is `(11/18) E(2)`, which is real and positive.
-/

noncomputable section

namespace Cubic.Counting.MonicEulerFactor

open Cubic.Counting.MonicConstantsData Cubic.PoissonSummation
open Cubic.PoissonSummation.FiniteEulerProduct

theorem two_re {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) : 1 < (2 * z).re := by
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  linarith

theorem half_two (z : ℂ) : 2 * z / 2 = z := by ring

theorem splitFactor_two (p : SplitPrimes) (z : ℂ) :
    LeadingTermsData.splitFactor p (2 * z) = monicSplitFactor p z := by
  simp only [LeadingTermsData.splitFactor, monicSplitFactor, half_two]

theorem three_add_ne_zero {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) : 1 + (3 : ℂ) ^ (-z) ≠ 0 := by
  have h := LeadingTermsSplitProduct.inversePower_add_ne_zero primeThree (two_re hz)
  rwa [half_two] at h

theorem three_sub_ne_zero {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) : 1 - (3 : ℂ) ^ (-z) ≠ 0 := by
  have h := LeadingTermsSplitProduct.inversePower_sub_ne_zero primeThree (two_re hz)
  rwa [half_two] at h

theorem zeta_ne_zero {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) : riemannZeta (2 * z) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (two_re hz)

theorem three_sq (z : ℂ) : (3 : ℂ) ^ (-(2 * z)) = ((3 : ℂ) ^ (-z)) ^ 2 := by
  have h := LeadingTermsSplitProduct.inversePower_sq primeThree (2 * z)
  rw [half_two] at h
  exact h

/-- `𝓔_mon(z) = (1 + 2·3^{-2z}) / (3(1 - 3^{-z})) · E(2z)` for `Re z > 1/2`. -/
theorem eq_correction {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) :
    monicEulerFactor z = (1 + 2 * (3 : ℂ) ^ (-(2 * z))) / (3 * (1 - (3 : ℂ) ^ (-z))) *
      LeadingTermsData.correction (2 * z) := by
  rw [LeadingTermsEulerProduct.correction_formula (2 * z) (two_re hz), half_two,
    monicEulerFactor]
  simp only [splitFactor_two]
  have h1 := three_add_ne_zero hz
  have h2 := three_sub_ne_zero hz
  have h3 := zeta_ne_zero hz
  field_simp

theorem value_one : monicEulerFactor 1 = 11 / 18 * LeadingTermsData.correction 2 := by
  rw [eq_correction (by norm_num)]
  norm_num [Complex.cpow_neg, Complex.cpow_ofNat]

theorem «eqn:monicEulerFactor» :
    CubicTargets.Counting.GeneralMonic.MonicEulerFactorClaim := by
  refine ⟨fun z hz => ⟨zeta_ne_zero hz, three_add_ne_zero hz, ?_⟩, ?_, ?_⟩
  · simpa only [splitFactor_two] using LeadingTermsSplitProduct.absolute (2 * z) (two_re hz)
  · rw [value_one]
    simp [LeadingTermsCorrection.correction_two_real]
  · rw [value_one]
    have h := LeadingTermsCorrection.correction_two_pos
    have hi := LeadingTermsCorrection.correction_two_real
    simp only [Complex.mul_re, hi, mul_zero, sub_zero]
    norm_num
    exact h

end Cubic.Counting.MonicEulerFactor
