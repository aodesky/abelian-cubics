import Cubic.PoissonSummation.ArchimedeanFourier
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The height translation estimate in `lemma:heightZetaConvergence`

The height here is the existing exponential of the fan's support function.
Its logarithmic absolute value has slopes `-Re(s₀)` and `2 Re(σ)`, giving the
paper's exact constant `max (Re(s₀)) (2 Re(σ))`. The bound also applies to a
translated height multiplied by an arbitrary fixed complex finite-place factor.
Identifying the adelic summands with these expressions remains a separate step.
-/

noncomputable section

namespace Cubic.PoissonSummation.ArchimedeanFourier

/-- The real logarithm of the absolute height, including both sides of the origin. -/
theorem log_norm_inverseHeight (s₀ σ : ℂ) (h₀ : 0 ≤ s₀.re) (hσ : 0 ≤ σ.re) (u : ℝ) :
    Real.log ‖inverseHeight s₀ σ u‖ = min (-s₀.re * u) (2 * σ.re * u) := by
  rcases le_total 0 u with hu | hu
  · have h : -s₀.re * u ≤ 2 * σ.re * u := by nlinarith
    rw [min_eq_left h]
    simp [inverseHeight_nonneg s₀ σ hu, Complex.norm_exp]
  · have h : 2 * σ.re * u ≤ -s₀.re * u := by nlinarith
    rw [min_eq_right h]
    simp [inverseHeight_nonpos s₀ σ hu, Complex.norm_exp]

/-- The two slopes give the exact Lipschitz constant used in the paper. -/
theorem abs_log_norm_inverseHeight_sub_le (s₀ σ : ℂ)
    (h₀ : 0 ≤ s₀.re) (hσ : 0 ≤ σ.re) (u v : ℝ) :
    |Real.log ‖inverseHeight s₀ σ u‖ - Real.log ‖inverseHeight s₀ σ v‖| ≤
      max s₀.re (2 * σ.re) * |u - v| := by
  have ha : LipschitzWith ⟨s₀.re, h₀⟩ (fun x : ℝ => -s₀.re * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg h₀]
  have hb : LipschitzWith ⟨2 * σ.re, by positivity⟩ (fun x : ℝ => 2 * σ.re * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hσ]
  simpa only [log_norm_inverseHeight s₀ σ h₀ hσ, Real.dist_eq, NNReal.coe_max]
    using (ha.min hb).dist_le_mul u v

/-- Comparison at any two logarithmic coordinates; no base point is assumed summable. -/
theorem norm_inverseHeight_le (s₀ σ : ℂ) (h₀ : 0 ≤ s₀.re) (hσ : 0 ≤ σ.re) (u v : ℝ) :
    ‖inverseHeight s₀ σ u‖ ≤
      Real.exp (max s₀.re (2 * σ.re) * |u - v|) * ‖inverseHeight s₀ σ v‖ := by
  have hu : 0 < ‖inverseHeight s₀ σ u‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hv : 0 < ‖inverseHeight s₀ σ v‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hlog := (le_abs_self _).trans (abs_log_norm_inverseHeight_sub_le s₀ σ h₀ hσ u v)
  calc
    _ = Real.exp (Real.log ‖inverseHeight s₀ σ u‖) := (Real.exp_log hu).symm
    _ ≤ Real.exp (max s₀.re (2 * σ.re) * |u - v| +
        Real.log ‖inverseHeight s₀ σ v‖) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log hv]

/-- Translation does not change the comparison constant; the fixed factor may include a cutoff. -/
theorem norm_mul_inverseHeight_translate_le (s₀ σ : ℂ)
    (h₀ : 0 ≤ s₀.re) (hσ : 0 ≤ σ.re) (c : ℂ) (r u v : ℝ) :
    ‖c * inverseHeight s₀ σ (r + u)‖ ≤
      Real.exp (max s₀.re (2 * σ.re) * |u - v|) *
        ‖c * inverseHeight s₀ σ (r + v)‖ := by
  have h := norm_inverseHeight_le s₀ σ h₀ hσ (r + u) (r + v)
  simp only [add_sub_add_left_eq_sub] at h
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖c‖ * (Real.exp (max s₀.re (2 * σ.re) * |u - v|) *
        ‖inverseHeight s₀ σ (r + v)‖) := mul_le_mul_of_nonneg_left h (norm_nonneg c)
    _ = _ := by ring

end Cubic.PoissonSummation.ArchimedeanFourier
