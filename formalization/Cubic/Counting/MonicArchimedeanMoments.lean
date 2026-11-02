import Cubic.Counting.MonicArchimedeanFactor
import Cubic.Counting.GeneralMonicIntegrals
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Proof of `eqn:monicArchimedeanMoments`

The paper's two definite integrals are evaluated directly by
`GeneralMonicIntegrals.integral_g₁` and `integral_g₂`, using explicit antiderivatives.
The other lemmas retain the value and derivative of the function `V` used in the
companion constants note. They are not part of the current paper statement.
-/

noncomputable section

namespace Cubic.Counting.MonicArchimedeanMoments

open Cubic.Counting.MonicConstantsData Cubic.Counting.MonicArchimedeanFactor
open MeasureTheory Metric

/-- The integrand at `z = 1`, as a real function. -/
theorem integrand_one (u : ℝ) :
    (((3 + u ^ 2 : ℝ)) : ℂ) ^ (1 : ℂ) = ((GeneralMonicIntegrals.g₁ u : ℝ) : ℂ) := by
  rw [Complex.cpow_one]; rfl

theorem value_one : archimedeanFactor 1 = 20 / 3 := by
  simp only [archimedeanFactor, integrand_one, intervalIntegral.integral_ofReal,
    GeneralMonicIntegrals.integral_g₁]
  push_cast; ring

/-- The derivative of the integrand in `z`. -/
def integrandDeriv (z : ℂ) (u : ℝ) : ℂ :=
  (((3 + u ^ 2 : ℝ)) : ℂ) ^ z * Complex.log (((3 + u ^ 2 : ℝ)) : ℂ)

theorem hasDerivAt_integrand (z : ℂ) (u : ℝ) :
    HasDerivAt (fun w : ℂ => (((3 + u ^ 2 : ℝ)) : ℂ) ^ w) (integrandDeriv z u) z := by
  have hc : (((3 + u ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (3 + u ^ 2 : ℝ) ≠ 0)
  simpa [integrandDeriv] using (hasDerivAt_id z).const_cpow (c := (((3 + u ^ 2 : ℝ)) : ℂ))
    (Or.inl hc)

theorem continuous_integrandDeriv (z : ℂ) : Continuous (integrandDeriv z) := by
  unfold integrandDeriv
  refine (continuous_integrand z).mul ?_
  exact continuous_iff_continuousAt.mpr fun u =>
    (Complex.continuous_ofReal.comp (by fun_prop)).continuousAt.clog (base_mem_slitPlane u)

theorem integrandDeriv_bound {z : ℂ} (hz : z ∈ ball (1 : ℂ) 1) {u : ℝ} (hu : |u| ≤ 1) :
    ‖integrandDeriv z u‖ ≤ 64 := by
  have hc0 : (0 : ℝ) < 3 + u ^ 2 := by positivity
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
  have hc1 : (1 : ℝ) ≤ 3 + u ^ 2 := by nlinarith
  have hc4 : 3 + u ^ 2 ≤ (4 : ℝ) := by linarith
  have hre : z.re ≤ 2 := by
    have h := mem_ball.mp hz
    have := Complex.abs_re_le_norm (z - 1)
    rw [dist_eq_norm] at h
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith [le_abs_self (z.re - 1)]
  unfold integrandDeriv
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc0, ← Complex.ofReal_log hc0.le,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hc1)]
  have h1 : (3 + u ^ 2) ^ z.re ≤ (16 : ℝ) := by
    calc (3 + u ^ 2) ^ z.re ≤ (3 + u ^ 2) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 hre
      _ ≤ (4 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow hc0.le hc4 (by norm_num)
      _ = 16 := by norm_num
  have h2 : Real.log (3 + u ^ 2) ≤ 4 := (Real.log_le_sub_one_of_pos hc0).trans (by linarith)
  calc (3 + u ^ 2) ^ z.re * Real.log (3 + u ^ 2) ≤ 16 * 4 :=
        mul_le_mul h1 h2 (Real.log_nonneg hc1) (by norm_num)
    _ = 64 := by norm_num

theorem hasDerivAt_archimedeanFactor :
    HasDerivAt archimedeanFactor (∫ u in (-1 : ℝ)..1, integrandDeriv 1 u) 1 := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (-1 : ℝ)) (b := 1) (x₀ := (1 : ℂ)) (bound := fun _ => (64 : ℝ))
    (F := fun z u => (((3 + u ^ 2 : ℝ)) : ℂ) ^ z) (F' := integrandDeriv) (ball_mem_nhds 1 one_pos)
    (Filter.Eventually.of_forall fun z => (continuous_integrand z).aestronglyMeasurable)
    ((continuous_integrand 1).intervalIntegrable _ _)
    (continuous_integrandDeriv 1).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u hu z hz => integrandDeriv_bound hz (by
      rw [Set.uIoc_of_le (by norm_num)] at hu
      exact abs_le.mpr ⟨hu.1.le, hu.2⟩))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun u _ z _ => hasDerivAt_integrand z u)
  exact h.2

theorem derivative_real :
    (∫ u in (-1 : ℝ)..1, integrandDeriv 1 u) =
      (((∫ u in (-1 : ℝ)..1, (3 + u ^ 2) * Real.log (3 + u ^ 2) : ℝ)) : ℂ) := by
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have hc0 : (0 : ℝ) ≤ 3 + u ^ 2 := by positivity
  simp only [integrandDeriv, Complex.cpow_one]
  rw [← Complex.ofReal_log hc0]
  push_cast; ring

theorem «eqn:monicArchimedeanMoments» :
    CubicTargets.Counting.GeneralMonic.MonicArchimedeanMomentsClaim :=
  ⟨GeneralMonicIntegrals.integral_g₁, GeneralMonicIntegrals.integral_g₂⟩

end Cubic.Counting.MonicArchimedeanMoments
