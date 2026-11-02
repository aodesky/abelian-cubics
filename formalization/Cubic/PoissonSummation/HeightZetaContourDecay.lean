import Cubic.PoissonSummation.HeightZetaResidue
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Vanishing of the upper semicircle in the height-zeta contour

The rational archimedean factor has quadratic decay for large complex `t`.
The finite transform is bounded throughout the closed upper half-plane.
The actual parametrized upper-semicircle integral is therefore bounded by
`C/R` and tends to zero. Integrability along sufficiently large arcs is proved
separately, so the estimate does not rely on totalized integrals of bad functions.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaContourDecay

open MeasureTheory Filter Complex HeightZetaResidue FiniteEulerProduct
open scoped Topology

private theorem frequency_norm_ge_one : 1 ≤ ‖(2 * Real.pi * I : ℂ)‖ := by
  have hp := Real.two_le_pi
  norm_num [norm_mul, abs_of_pos Real.pi_pos]
  linarith

/-- A convenient sufficient radius; optimizing it is irrelevant to the limit. -/
def radius (s₀ σ : ℂ) : ℝ := 1 + 2 * (‖s₀‖ + ‖2 * σ‖) + ‖upperPole s₀‖

theorem radius_pos (s₀ σ : ℂ) : 0 < radius s₀ σ := by
  unfold radius
  positivity

theorem archimedean_bound (s₀ σ t : ℂ) (ht : radius s₀ σ ≤ ‖t‖) :
    ‖archimedeanContinuation s₀ σ t‖ ≤ 4 * ‖s₀ + 2 * σ‖ / ‖t‖ ^ 2 := by
  have ht0 : 0 < ‖t‖ := (radius_pos s₀ σ).trans_le ht
  have ha : 2 * ‖s₀‖ ≤ ‖t‖ := by
    dsimp [radius] at ht
    linarith [norm_nonneg (2 * σ), norm_nonneg (upperPole s₀)]
  have hb : 2 * ‖2 * σ‖ ≤ ‖t‖ := by
    dsimp [radius] at ht
    linarith [norm_nonneg s₀, norm_nonneg (upperPole s₀)]
  have hk : ‖t‖ ≤ ‖(2 * Real.pi * I) * t‖ := by
    rw [norm_mul]
    nlinarith [frequency_norm_ge_one]
  have h₁ : ‖t‖ / 2 ≤ ‖s₀ + 2 * Real.pi * I * t‖ := by
    have hh := norm_sub_norm_le ((2 * Real.pi * I) * t) (-s₀)
    simp only [norm_neg, sub_neg_eq_add, add_comm _ s₀] at hh
    linarith
  have h₂ : ‖t‖ / 2 ≤ ‖2 * σ - 2 * Real.pi * I * t‖ := by
    have hh := norm_sub_norm_le ((2 * Real.pi * I) * t) (2 * σ)
    rw [norm_sub_rev] at hh
    linarith
  have hd : ‖t‖ ^ 2 / 4 ≤
      ‖s₀ + 2 * Real.pi * I * t‖ * ‖2 * σ - 2 * Real.pi * I * t‖ := by
    have hh := mul_le_mul h₁ h₂ (by positivity : 0 ≤ ‖t‖ / 2) (norm_nonneg _)
    nlinarith
  calc
    ‖archimedeanContinuation s₀ σ t‖ = ‖s₀ + 2 * σ‖ /
        (‖s₀ + 2 * Real.pi * I * t‖ * ‖2 * σ - 2 * Real.pi * I * t‖) := by
      simp only [archimedeanContinuation, norm_div, norm_mul]
    _ ≤ ‖s₀ + 2 * σ‖ / (‖t‖ ^ 2 / 4) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hd
    _ = _ := by ring

/-- The same counterclockwise upper arc as in the paper: `t=R exp(iθ)`, `0≤θ≤π`. -/
def upperArc (s₀ σ : ℂ) (R : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    deriv (circleMap 0 R) θ * fullContinuation s₀ σ (circleMap 0 R θ)

private theorem upperArc_im_nonneg {R θ : ℝ} (hR : 0 ≤ R) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    0 ≤ (circleMap 0 R θ).im := by
  simpa [circleMap, exp_mul_I, mul_im] using
    mul_nonneg hR (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)

theorem upperArc_integrable (s₀ σ : ℂ) (hσ : 1 < σ.re) (R : ℝ) (hR : radius s₀ σ ≤ R) :
    IntervalIntegrable (fun θ => deriv (circleMap 0 R) θ *
      fullContinuation s₀ σ (circleMap 0 R θ)) volume 0 Real.pi := by
  have hR0 : 0 < R := (radius_pos s₀ σ).trans_le hR
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le Real.pi_pos.le]
  apply ContinuousOn.mul (f := fun θ => deriv (circleMap 0 R) θ)
  · have hc : Continuous (fun θ => deriv (circleMap 0 R) θ) := by
      simp only [deriv_circleMap]
      fun_prop
    exact hc.continuousOn
  · intro θ hθ
    have hne : circleMap 0 R θ ≠ upperPole s₀ := by
      apply circleMap_ne_mem_ball
      simp only [Metric.mem_ball, dist_zero_right]
      dsimp [radius] at hR
      linarith [norm_nonneg s₀, norm_nonneg (2 * σ)]
    exact ((differentiableAt_fullContinuation s₀ σ _ hσ
      (upperArc_im_nonneg hR0.le hθ) hne).continuousAt.comp
        (by fun_prop)).continuousWithinAt

theorem upperArc_norm_bound (s₀ σ : ℂ) (C : ℝ)
    (hbound : ∀ t : ℂ, 0 ≤ t.im → ‖value (complexSpectralParameter σ t)‖ ≤ C)
    (R : ℝ) (hR : radius s₀ σ ≤ R) :
    ‖upperArc s₀ σ R‖ ≤ (4 * ‖s₀ + 2 * σ‖ * C * Real.pi) / R := by
  have hR0 : 0 < R := (radius_pos s₀ σ).trans_le hR
  have hb : ∀ θ ∈ Set.uIoc 0 Real.pi,
      ‖deriv (circleMap 0 R) θ * fullContinuation s₀ σ (circleMap 0 R θ)‖ ≤
        4 * ‖s₀ + 2 * σ‖ * C / R := by
    intro θ hθ
    rw [Set.uIoc_of_le Real.pi_pos.le] at hθ
    have hi := hbound (circleMap 0 R θ) (upperArc_im_nonneg hR0.le ⟨hθ.1.le, hθ.2⟩)
    have ha := archimedean_bound s₀ σ (circleMap 0 R θ)
      (by simpa only [norm_circleMap_zero, abs_of_pos hR0] using hR)
    rw [norm_circleMap_zero, abs_of_pos hR0] at ha
    simp only [norm_mul, deriv_circleMap, norm_circleMap_zero, abs_of_pos hR0, norm_I,
      mul_one, fullContinuation]
    calc
      R * (‖archimedeanContinuation s₀ σ (circleMap 0 R θ)‖ *
          ‖value (complexSpectralParameter σ (circleMap 0 R θ))‖) ≤
        R * ((4 * ‖s₀ + 2 * σ‖ / R ^ 2) * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul ha hi (norm_nonneg _) (by positivity)) hR0.le
      _ = _ := by field_simp
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [upperArc, sub_zero, abs_of_pos Real.pi_pos, div_mul_eq_mul_div] using hh

/-- The upper semicircle contribution vanishes in the paper's initial parameter region. -/
theorem upperArc_tendsto_zero (s₀ σ : ℂ) (hσ : 1 < σ.re) :
    Tendsto (upperArc s₀ σ) atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := upper_half_plane_bound σ hσ
  apply squeeze_zero_norm' (a := fun R : ℝ => (4 * ‖s₀ + 2 * σ‖ * C * Real.pi) / R)
  · filter_upwards [eventually_ge_atTop (radius s₀ σ)] with R hR
    exact upperArc_norm_bound s₀ σ C hbound R hR
  · exact tendsto_const_nhds.div_atTop tendsto_id

end Cubic.PoissonSummation.HeightZetaContourDecay
