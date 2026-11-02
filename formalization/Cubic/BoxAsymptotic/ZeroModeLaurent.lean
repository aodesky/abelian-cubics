import Cubic.BoxAsymptotic.ZeroModeData
import Cubic.Counting.MonicConceptualConstants
import Cubic.Counting.EulerKroneckerGamma
import Cubic.Counting.AsymptoticConstantIdentities
import Cubic.PoissonSummation.HeightZetaLaurent

/-! The Laurent coefficients in `eq:F0`, obtained from the actual analytic numerator.
No Poisson or smoothing hypothesis enters this calculation. -/

noncomputable section

namespace Cubic.BoxAsymptotic.ZeroModeLaurent

open Cubic.BoxAsymptotic.ZeroModeData CubicTargets.BoxAsymptotic
open Cubic.PoissonSummation Cubic.Counting
open Cubic.Counting.MonicConceptualConstants
open Cubic.Counting.AsymptoticConstantsData Cubic.Counting.AsymptoticConstantsConvergence
open Filter Asymptotics
open scoped Topology

theorem numerator_analytic : AnalyticAt ℂ numerator 1 := by
  have hlocal : AnalyticAt ℂ localFactor 1 := by
    unfold localFactor
    have h (c : ℂ) : AnalyticAt ℂ (fun s : ℂ => (3 : ℂ) ^ (-(c * s))) 1 := by
      exact (((differentiable_const c).mul differentiable_id).neg.const_cpow
        (Or.inl (by norm_num : (3 : ℂ) ≠ 0))).analyticAt 1
    have h1 : AnalyticAt ℂ (fun s : ℂ => (3 : ℂ) ^ (-s)) 1 := by simpa using h 1
    exact (analyticAt_const.fun_mul (analyticAt_const.fun_add
      (analyticAt_const.fun_mul (h 2)))).fun_mul (analyticAt_const.fun_sub h1)
  have hR := HeightZetaCorrectionProduct.differentiableOn_value.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num :
      (1 : ℂ) ∈ {s : ℂ | (1 / 2 : ℝ) < s.re}))
  exact (hlocal.fun_mul ((QuadraticZetaRegularization.differentiable_regular.analyticAt 1).fun_pow 2)).fun_mul hR

theorem numerator_eq {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    numerator s = R s / 4 * HeightZetaLaurent.numerator (2 * s) := by
  rw [numerator, localFactor, R, HeightZetaLaurent.numerator, LeadingTermsData.correction]
  rw [MonicEulerFactor.half_two]
  have hn := MonicEulerFactor.three_sub_ne_zero hs
  field_simp

theorem height_numerator : HeightZetaLaurent.numerator 2 = (4 / 3 : ℂ) * (originalLeading : ℂ) := by
  rw [HeightZetaLaurent.numerator_two,
    LeadingTermsAssembly.L_one_eq_residue QuadraticDedekindFactorization.factorization,
    QuadraticDedekindResidue.residue_value_complex,
    AsymptoticConstantIdentities.original_leading_correction]
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h30 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 3 ≠ 0 by positivity)
  field_simp
  rw [h3]
  ring

theorem numerator_one : numerator 1 = (aStar : ℂ) := by
  rw [numerator_eq (by norm_num), R_one]
  norm_num only [mul_one]
  rw [height_numerator]
  simp only [aStar, GeneralMonicData.Cconst]
  push_cast
  ring

theorem height_derivative : deriv HeightZetaLaurent.numerator 2 =
    HeightZetaLaurent.numerator 2 * ((originalSecondaryRatio : ℂ) + 1 / 2) := by
  have h := HeightZetaLaurent.coefficient_ratio
  have hγ : deriv QuadraticZetaRegularization.regular 1 / QuadraticZetaRegularization.regular 1 =
      (classicalEulerKronecker : ℂ) := EulerKroneckerGamma.evaluation
  rw [hγ, LeadingTermsLogDerivative.correction_log_derivative] at h
  simp_rw [← inert_log_cast, ← original_split_log_cast] at h
  rw [tsum_mul_left] at h
  have he : (classicalEulerKronecker : ℂ) +
      ((1 / 2 : ℂ) * (Real.log 3 : ℂ) + (∑' q, (inertLogTerm q : ℂ)) +
        3 * ∑' p, (originalSplitLogTerm p : ℂ)) = (originalSecondaryRatio : ℂ) + 1 / 2 := by
    simp only [originalSecondaryRatio, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one,
      Complex.ofReal_tsum]
    ring
  rw [he, div_eq_iff HeightZetaLaurent.numerator_two_ne_zero] at h
  exact h.trans (mul_comm _ _)

theorem numerator_derivative : deriv numerator 1 =
    ((aStar * (1 + 2 * originalSecondaryRatio - 19 / 22 * Real.log 3) : ℝ) : ℂ) := by
  have he : numerator =ᶠ[𝓝 (1 : ℂ)]
      (fun s => R s / 4 * HeightZetaLaurent.numerator (2 * s)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℂ) ∈ {s : ℂ | (1 / 2 : ℝ) < s.re})] with s hs using numerator_eq hs
  have hh : HasDerivAt (fun s : ℂ => HeightZetaLaurent.numerator (2 * s))
      (deriv HeightZetaLaurent.numerator 2 * 2) 1 := by
    exact HasDerivAt.comp_of_eq 1
      (HeightZetaLaurent.numerator_analytic 2 (by norm_num)).differentiableAt.hasDerivAt
      (by simpa using (hasDerivAt_id (1 : ℂ)).const_mul 2) (by norm_num)
  rw [he.deriv_eq, ((hasDerivAt_R.div_const 4).fun_mul hh).deriv,
    height_derivative, R_one, height_numerator]
  simp only [mul_one, aStar, GeneralMonicData.Cconst]
  rw [height_numerator]
  push_cast
  ring

theorem derivative_real : deriv numerator 1 = (b₀ : ℂ) := by
  rw [b₀, numerator_derivative, Complex.ofReal_re]

theorem quotient {s : ℂ} (hs : s ≠ 1) : continuation s = numerator s / (s - 1) ^ 2 := by
  rw [continuation, numerator, QuadraticZetaRegularization.regular_eq s hs]
  field_simp [sub_ne_zero.mpr hs]

theorem laurent :
    (fun s : ℂ => continuation s - (aStar : ℂ) / (s - 1) ^ 2 - (b₀ : ℂ) / (s - 1))
      =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) := by
  have h := AnalyticLaurent.laurent_of_analytic_numerator numerator_analytic (F := continuation)
    (by filter_upwards [self_mem_nhdsWithin] with s hs using quotient hs)
  simpa only [numerator_one, derivative_real] using h

end Cubic.BoxAsymptotic.ZeroModeLaurent
