import Cubic.PoissonSummation.LeadingTermsEulerProduct

/-!
# The simplified logarithmic derivative of `E(s)` at 2

This is the final prime-sum calculation in `prop:leadingTerms`. It uses
the actual locally uniform split product and the proved extraction of
`1/ζ(s)`. The coefficient `3/8` is the ramified quotient's derivative
in `s`; the zeta contribution has a minus sign because it is reciprocal.
-/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsSimplifiedDerivative

open Filter LeadingTermsData FiniteEulerProduct LeadingTermsLocalDerivatives
open scoped Topology

def product (s : ℂ) : ℂ := ∏' p : SplitPrimes, LeadingTermsData.splitFactor p s

theorem product_nonzero : product 2 ≠ 0 := by
  have h := LeadingTermsCorrection.correction_two_ne_zero
  rw [LeadingTermsEulerProduct.correction_formula 2 (by norm_num)] at h
  exact (mul_ne_zero_iff.mp h).2

theorem factor_nonzero (p : SplitPrimes) : LeadingTermsData.splitFactor p 2 ≠ 0 := by
  have hn : HeightZetaCorrectionProduct.split p 1 ≠ 0 := by
    rw [LeadingTermsCorrection.split_one]
    exact_mod_cast (LeadingTermsCorrection.splitReal_pos p).ne'
  have he := LeadingTermsSplitProduct.local_identity p (s := 2) (by norm_num)
  norm_num only [div_self (by norm_num : (2 : ℂ) ≠ 0)] at he
  rw [he] at hn
  exact (mul_ne_zero_iff.mp hn).2

theorem product_differentiable :
    DifferentiableOn ℂ product {s : ℂ | 1 < s.re} :=
  LeadingTermsSplitProduct.locally_uniform.differentiableOn
    (Eventually.of_forall fun _S => DifferentiableOn.fun_finset_prod
      fun p _ => LeadingTermsSplitProduct.differentiable p)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem product_log_derivative : logDeriv product 2 = ∑' p : SplitPrimes, splitLogTerm p := by
  have hs : Summable (fun p : SplitPrimes => logDeriv (LeadingTermsData.splitFactor p) 2) := by
    simpa only [simplified_split_log_derivative] using
      LeadingTermsPrimeSums.summable_split_log.of_norm
  have he := logDeriv_tprod_eq_tsum (isOpen_lt continuous_const Complex.continuous_re)
    (x := (2 : ℂ)) (s := {s : ℂ | 1 < s.re}) (by norm_num)
    (f := LeadingTermsData.splitFactor) factor_nonzero LeadingTermsSplitProduct.differentiable hs
    LeadingTermsSplitProduct.locally_uniform.multipliableLocallyUniformlyOn product_nonzero
  simpa only [simplified_split_log_derivative] using he

theorem correction_log_derivative : deriv correction 2 / correction 2 =
    -deriv riemannZeta 2 / riemannZeta 2 + (3 / 8 : ℂ) * (Real.log 3 : ℂ) +
      ∑' p : SplitPrimes, splitLogTerm p := by
  have hU : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  let R : ℂ → ℂ := fun s => (1 - (3 : ℂ) ^ (-(s / 2))) / (1 + (3 : ℂ) ^ (-(s / 2)))
  let V : ℂ → ℂ := fun s => 1 / riemannZeta s
  have he : correction =ᶠ[𝓝 (2 : ℂ)] (fun s => R s * V s * product s) := by
    filter_upwards [hU] with s hs using LeadingTermsEulerProduct.correction_formula s hs
  have hz := differentiableAt_riemannZeta (s := (2 : ℂ)) (by norm_num)
  have hzn := riemannZeta_ne_zero_of_one_lt_re (s := (2 : ℂ)) (by norm_num)
  have hV : DifferentiableAt ℂ V 2 := (differentiableAt_const (1 : ℂ)).div hz hzn
  have hR : DifferentiableAt ℂ R 2 := by
    dsimp [R]
    fun_prop (disch := norm_num [Complex.cpow_neg])
  have hnR : R 2 ≠ 0 := by norm_num [R, Complex.cpow_neg]
  have hnV : V 2 ≠ 0 := one_div_ne_zero hzn
  have hP := product_differentiable.differentiableAt hU
  have hlogR : logDeriv R 2 = (3 / 8 : ℂ) * (Real.log 3 : ℂ) :=
    ramified_quotient_log_derivative
  have hlogV : logDeriv V 2 = -deriv riemannZeta 2 / riemannZeta 2 := by
    rw [show V = (fun s : ℂ => 1 / riemannZeta s) from rfl,
      logDeriv_div 2 one_ne_zero hzn (differentiableAt_const _) hz]
    simp [logDeriv_apply, neg_div]
  calc
    _ = logDeriv (fun s => R s * V s * product s) 2 := by
      rw [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    _ = _ := by
      rw [logDeriv_mul (f := fun s => R s * V s) (g := product) 2
        (mul_ne_zero hnR hnV) product_nonzero (hR.fun_mul hV) hP,
        logDeriv_mul 2 hnR hnV hR hV, hlogR, hlogV, product_log_derivative]
      ring

end Cubic.PoissonSummation.LeadingTermsSimplifiedDerivative
