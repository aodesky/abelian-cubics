import Cubic.PoissonSummation.LeadingTermsPrimeSums

/-!
# Logarithmic differentiation of the original correction product

This proves the intermediate formula in the paper's proof of
`prop:leadingTerms`. Mathlib's infinite-product differentiation theorem is
applied only after local uniform convergence, absolute summability of the
logarithmic derivatives, and nonvanishing have all been established.
-/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsLogDerivative

open FiniteEulerProduct LeadingTermsCorrection LeadingTermsLocalDerivatives
open LeadingTermsPrimeSums

def inertProduct (s : ℂ) : ℂ :=
  ∏' q : InertPrimes, HeightZetaCorrectionProduct.inert q (s / 2)

def splitProduct (s : ℂ) : ℂ :=
  ∏' p : SplitPrimes, HeightZetaCorrectionProduct.split p (s / 2)

theorem inert_locally_uniform : HasProdLocallyUniformlyOn
    (fun q s => HeightZetaCorrectionProduct.inert q (s / 2)) inertProduct
    {s : ℂ | 1 < s.re} := by
  exact HeightZetaCorrectionProduct.locally_uniform_inert.comp (fun s : ℂ => s / 2)
    (fun _ hs => half_re hs) (by fun_prop)

theorem split_locally_uniform : HasProdLocallyUniformlyOn
    (fun p s => HeightZetaCorrectionProduct.split p (s / 2)) splitProduct
    {s : ℂ | 1 < s.re} := by
  exact HeightZetaCorrectionProduct.locally_uniform_split.comp (fun s : ℂ => s / 2)
    (fun _ hs => half_re hs) (by fun_prop)

theorem inert_differentiable (q : InertPrimes) :
    Differentiable ℂ (fun s : ℂ => HeightZetaCorrectionProduct.inert q (s / 2)) :=
  (HeightZetaCorrectionProduct.differentiable_inert q).comp (by fun_prop)

theorem split_differentiable (p : SplitPrimes) :
    Differentiable ℂ (fun s : ℂ => HeightZetaCorrectionProduct.split p (s / 2)) :=
  (HeightZetaCorrectionProduct.differentiable_split p).comp (by fun_prop)

theorem inertProduct_differentiable :
    DifferentiableOn ℂ inertProduct {s : ℂ | 1 < s.re} :=
  inert_locally_uniform.differentiableOn
    (Filter.Eventually.of_forall fun _S => DifferentiableOn.fun_finset_prod
      fun q _ => (inert_differentiable q).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem splitProduct_differentiable :
    DifferentiableOn ℂ splitProduct {s : ℂ | 1 < s.re} :=
  split_locally_uniform.differentiableOn
    (Filter.Eventually.of_forall fun _S => DifferentiableOn.fun_finset_prod
      fun p _ => (split_differentiable p).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem products_nonzero : inertProduct 2 ≠ 0 ∧ splitProduct 2 ≠ 0 := by
  have h := correction_two_ne_zero
  change (1 - (3 : ℂ) ^ (-(2 / 2 : ℂ))) ^ 2 * (inertProduct 2 * splitProduct 2) ≠ 0 at h
  exact mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).2

theorem inert_product_log_derivative : logDeriv inertProduct 2 =
    ∑' q : InertPrimes, (Real.log (q.1 : ℝ) : ℂ) / ((q.1 : ℂ) ^ 2 - 1) := by
  have hl : Summable (fun q : InertPrimes =>
      logDeriv (fun s : ℂ => HeightZetaCorrectionProduct.inert q (s / 2)) 2) := by
    simpa only [inert_log_derivative] using summable_inert_log.of_norm
  have he := logDeriv_tprod_eq_tsum (isOpen_lt continuous_const Complex.continuous_re)
    (x := (2 : ℂ)) (s := {s : ℂ | 1 < s.re}) (by norm_num)
    (f := fun q : InertPrimes => fun s : ℂ => HeightZetaCorrectionProduct.inert q (s / 2))
    (fun q => by
      norm_num only [div_self (by norm_num : (2 : ℂ) ≠ 0), inert_one]
      exact_mod_cast (inertReal_pos q).ne')
    (fun q => (inert_differentiable q).differentiableOn) hl
    inert_locally_uniform.multipliableLocallyUniformlyOn products_nonzero.1
  simpa only [inert_log_derivative] using he

theorem split_product_log_derivative : logDeriv splitProduct 2 =
    ∑' p : SplitPrimes, 3 * ((p.1 : ℂ) - 1) * (Real.log (p.1 : ℝ) : ℂ) /
      ((p.1 : ℂ) ^ 3 - 3 * (p.1 : ℂ) + 2) := by
  have hl : Summable (fun p : SplitPrimes =>
      logDeriv (fun s : ℂ => HeightZetaCorrectionProduct.split p (s / 2)) 2) := by
    simpa only [split_log_derivative] using summable_original_split_log.of_norm
  have he := logDeriv_tprod_eq_tsum (isOpen_lt continuous_const Complex.continuous_re)
    (x := (2 : ℂ)) (s := {s : ℂ | 1 < s.re}) (by norm_num)
    (f := fun p : SplitPrimes => fun s : ℂ => HeightZetaCorrectionProduct.split p (s / 2))
    (fun p => by
      norm_num only [div_self (by norm_num : (2 : ℂ) ≠ 0), split_one]
      exact_mod_cast (splitReal_pos p).ne')
    (fun p => (split_differentiable p).differentiableOn) hl
    split_locally_uniform.multipliableLocallyUniformlyOn products_nonzero.2
  simpa only [split_log_derivative] using he

/-- The paper's original, unsimplified prime-sum expression, differentiated in `s`. -/
theorem correction_log_derivative :
    deriv LeadingTermsData.correction 2 / LeadingTermsData.correction 2 =
      (1 / 2 : ℂ) * (Real.log 3 : ℂ) +
      (∑' q : InertPrimes, (Real.log (q.1 : ℝ) : ℂ) / ((q.1 : ℂ) ^ 2 - 1)) +
      ∑' p : SplitPrimes, 3 * ((p.1 : ℂ) - 1) * (Real.log (p.1 : ℝ) : ℂ) /
        ((p.1 : ℂ) ^ 3 - 3 * (p.1 : ℂ) + 2) := by
  have hU := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)
  have hi := inertProduct_differentiable.differentiableAt hU
  have hs := splitProduct_differentiable.differentiableAt hU
  have hr : DifferentiableAt ℂ (fun s : ℂ => (1 - (3 : ℂ) ^ (-(s / 2))) ^ 2) 2 := by
    fun_prop
  change logDeriv (fun s : ℂ => (1 - (3 : ℂ) ^ (-(s / 2))) ^ 2 *
    (inertProduct s * splitProduct s)) 2 = _
  rw [logDeriv_mul (f := fun s : ℂ => (1 - (3 : ℂ) ^ (-(s / 2))) ^ 2)
    (g := fun s => inertProduct s * splitProduct s) 2 (by norm_num [Complex.cpow_neg])
    (mul_ne_zero products_nonzero.1 products_nonzero.2) hr (hi.fun_mul hs),
    logDeriv_mul 2 products_nonzero.1 products_nonzero.2 hi hs,
    ramified_log_derivative, inert_product_log_derivative, split_product_log_derivative]
  ring

end Cubic.PoissonSummation.LeadingTermsLogDerivative
