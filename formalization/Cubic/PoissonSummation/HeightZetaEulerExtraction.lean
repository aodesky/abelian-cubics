import Cubic.PoissonSummation.HeightZetaFormulaData
import Cubic.PoissonSummation.FiniteFourierProduct
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Extracting the Riemann zeta factor

The contour calculation in `thm:heightZetaFunctionFormula2` produces the
unscaled inert/split product. This file identifies that convergent product
with the paper's displayed Euler expression, removing the prime three exactly
once. It uses mathlib's proved Riemann-zeta Euler product. No identification
with the original height series or contour evaluation is assumed here.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaEulerExtraction

open FiniteEulerProduct HeightZetaFormulaData

private theorem norm_inv_one_add_sub_one (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    ‖(1 + x)⁻¹ - 1‖ ≤ 2 * ‖x‖ := by
  have hd : 1 / 2 ≤ ‖1 + x‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-x)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at h
    linarith
  have hn : 1 + x ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : (1 + x)⁻¹ - 1 = -x / (1 + x) := by field_simp; ring
  rw [he, norm_div, norm_neg]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 + x‖)).mpr
  nlinarith [norm_nonneg x]

private theorem norm_split_correction_sub_one (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    ‖(1 + 3 * x / (1 - x)) - 1‖ ≤ 6 * ‖x‖ := by
  have hd : 1 / 2 ≤ ‖1 - x‖ := by
    have h := norm_sub_norm_le (1 : ℂ) x
    simp only [norm_one] at h
    linarith
  rw [add_sub_cancel_left, norm_div, norm_mul]
  norm_num
  apply (div_le_iff₀ (by linarith : 0 < ‖1 - x‖)).mpr
  nlinarith [norm_nonneg x]

theorem inert_product_absolute (z : ℂ) (hz : 1 < z.re) :
    Summable (fun q : InertPrimes => ‖inertCorrection q z - 1‖) := by
  apply (((summable_prime_power hz).subtype (fun p => (p : ℕ) % 3 = 2)).mul_left 2).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro q
  exact norm_inv_one_add_sub_one _ (Complex.norm_prime_cpow_le_one_half q.1 hz)

theorem split_product_absolute (z : ℂ) (hz : 1 < z.re) :
    Summable (fun p : SplitPrimes => ‖splitCorrection p z - 1‖) := by
  apply (((summable_prime_power hz).subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 6).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro p
  exact norm_split_correction_sub_one _ (Complex.norm_prime_cpow_le_one_half p.1 hz)

theorem inert_product_multipliable (z : ℂ) (hz : 1 < z.re) :
    Multipliable (fun q : InertPrimes => inertCorrection q z) := by
  simpa using multipliable_one_add_of_summable (inert_product_absolute z hz)

theorem split_product_multipliable (z : ℂ) (hz : 1 < z.re) :
    Multipliable (fun p : SplitPrimes => splitCorrection p z) := by
  simpa using multipliable_one_add_of_summable (split_product_absolute z hz)

private theorem zeta_deviations_summable (z : ℂ) (hz : 1 < z.re) :
    Summable (fun p : Nat.Primes => ‖(1 - (p : ℂ) ^ (-z))⁻¹ - 1‖) := by
  apply ((summable_prime_power hz).mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  simpa only [norm_neg, add_neg_cancel_right, sub_eq_add_neg] using
    norm_inv_one_add_sub_one (-((p : ℂ) ^ (-z)))
      (by simpa using Complex.norm_prime_cpow_le_one_half p hz)

theorem zeta_inert_multipliable (z : ℂ) (hz : 1 < z.re) :
    Multipliable (fun q : InertPrimes => (1 - (q.1 : ℂ) ^ (-z))⁻¹) := by
  simpa using multipliable_one_add_of_summable
    ((zeta_deviations_summable z hz).subtype (fun p => (p : ℕ) % 3 = 2))

theorem zeta_split_multipliable (z : ℂ) (hz : 1 < z.re) :
    Multipliable (fun p : SplitPrimes => (1 - (p.1 : ℂ) ^ (-z))⁻¹) := by
  simpa using multipliable_one_add_of_summable
    ((zeta_deviations_summable z hz).subtype (fun p => (p : ℕ) % 3 = 1))

/-- The inert quadratic denominator splits without changing its sign. -/
theorem inert_factor (q : InertPrimes) (z : ℂ) :
    inertFactor q z = (1 - (q.1 : ℂ) ^ (-z))⁻¹ * inertCorrection q z := by
  have he : (q.1 : ℂ) ^ (-(2 * z)) = ((q.1 : ℂ) ^ (-z)) ^ 2 := by
    rw [neg_mul_eq_mul_neg, ← Complex.cpow_nat_mul]
    norm_num
  simp only [inertFactor, inertCorrection, he, ← mul_inv]
  congr 1
  ring

theorem split_factor (p : SplitPrimes) (z : ℂ) (hz : 1 < z.re) :
    splitFactor p z = (1 - (p.1 : ℂ) ^ (-z))⁻¹ * splitCorrection p z := by
  have hn := Complex.one_sub_prime_cpow_ne_zero p.1.2 hz
  unfold splitFactor splitCorrection
  field_simp [hn]
  ring

/-- Removing the exceptional prime from mathlib's convergent zeta product. -/
theorem zeta_without_three (z : ℂ) (hz : 1 < z.re) :
    (∏' q : InertPrimes, (1 - (q.1 : ℂ) ^ (-z))⁻¹) *
        (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-z))⁻¹) =
      (1 - (3 : ℂ) ^ (-z)) * riemannZeta z := by
  have hp := hasProd_primes_mod_three (f := fun p : Nat.Primes => (1 - (p : ℂ) ^ (-z))⁻¹)
    (zeta_inert_multipliable z hz).hasProd
    (zeta_split_multipliable z hz).hasProd
  have he := hp.unique (riemannZeta_eulerProduct_hasProd hz)
  have hn : 1 - (3 : ℂ) ^ (-z) ≠ 0 := Complex.one_sub_prime_cpow_ne_zero Nat.prime_three hz
  change (1 - (3 : ℂ) ^ (-z))⁻¹ * _ * _ = riemannZeta z at he
  rw [← he]
  field_simp

/-- The full product identity after contour evaluation, with all product convergence justified. -/
theorem eulerExpression_eq_unscaled_product (z : ℂ) (hz : 1 < z.re) :
    eulerExpression z =
      (∏' q : InertPrimes, inertFactor q z) * (∏' p : SplitPrimes, splitFactor p z) := by
  have hi : (∏' q : InertPrimes, inertFactor q z) =
      (∏' q : InertPrimes, (1 - (q.1 : ℂ) ^ (-z))⁻¹) *
        ∏' q : InertPrimes, inertCorrection q z := by
    simp only [inert_factor]
    exact (zeta_inert_multipliable z hz).tprod_mul (inert_product_multipliable z hz)
  have hs : (∏' p : SplitPrimes, splitFactor p z) =
      (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-z))⁻¹) *
        ∏' p : SplitPrimes, splitCorrection p z := by
    simp only [split_factor _ _ hz]
    exact (zeta_split_multipliable z hz).tprod_mul (split_product_multipliable z hz)
  rw [hi, hs, eulerExpression, ← zeta_without_three z hz]
  ring

end Cubic.PoissonSummation.HeightZetaEulerExtraction
