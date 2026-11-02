import Cubic.BoxAsymptotic.SmoothWeightBounded
import Cubic.BoxAsymptotic.SmoothMellinInversion
import Cubic.Analysis.VerticalContourShift

/-! Qualitative rapid decay needed to justify a contour shift for a fixed
angular mode. The bounded derivatives used here may depend on the weight and
mode; the uniform final error uses `SmoothTransformBounds.decay_bound` with
one fixed derivative budget instead. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothContourDecay

open MeasureTheory Complex Set
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothWeightData
open scoped ContDiff

theorem integrable_of_tall_decay {f : ℝ → ℂ} {C : ℝ}
    (hf : Continuous f) (hC : 0 ≤ C)
    (hb : ∀ t, 1 ≤ |t| → ‖f t‖ ≤ C / (1 + |t|) ^ 2) : Integrable f := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (-1 : ℝ) 1))
  apply SmoothMellinInversion.integrable_of_squared_decay hf.aestronglyMeasurable
    (C := C + 4 * max B 0) (by positivity)
  intro t
  by_cases ht : 1 ≤ |t|
  · exact (hb t ht).trans (div_le_div_of_nonneg_right
      (le_add_of_nonneg_right (by positivity)) (by positivity))
  · have ht' : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp (by linarith)
    have hBt : ‖f t‖ ≤ max B 0 := (hB t ht').trans (le_max_left _ _)
    rw [le_div_iff₀ (by positivity)]
    have ht2 : (1 + |t|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg t]
    calc
      _ ≤ max B 0 * 4 := mul_le_mul hBt ht2 (by positivity) (by positivity)
      _ ≤ _ := by nlinarith

theorem transform_t_decay {w : ℝ × ℝ → ℝ} {X Θ θ₀ M : ℝ} {j : ℕ}
    (hw : ContDiff ℝ ∞ w) (hX : 1 ≤ X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M (2 * j))
    (k : ℤ) (s : ℂ) (hσ : 0 ≤ s.re) (hσ' : s.re ≤ 2) :
    ‖transform w k s‖ ≤ ((60 / Real.pi) * 4 ^ j) * M * X ^ (2 : ℕ) * Θ /
      (1 + |s.im|) ^ j := by
  have ht := SmoothTransformBounds.decay_bound hw (by linarith) hΘ hM hp hs hb k s hσ hσ'
  have ha : 1 ≤ (1 + |(k : ℝ)| * Θ) ^ j :=
    one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  have hx : X ^ s.re ≤ X ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hX hσ'
  calc
    _ ≤ ((60 / Real.pi) * 4 ^ j) * M * X ^ s.re * Θ /
        ((1 + |(k : ℝ)| * Θ) ^ j * (1 + |s.im|) ^ j) := ht
    _ ≤ ((60 / Real.pi) * 4 ^ j) * M * X ^ s.re * Θ / (1 + |s.im|) ^ j := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact le_mul_of_one_le_left (by positivity) ha
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity)) hΘ.le)
      (by positivity)

/-- The actual weighted integrand has a uniform quadratic decay across a fixed
strip once the arithmetic factor has polynomial growth there. -/
theorem product_decay {w : ℝ × ℝ → ℝ} {X Θ θ₀ β C : ℝ} {F : ℂ → ℂ} {N : ℕ}
    (hw : ContDiff ℝ ∞ w) (hX : 1 ≤ X) (hΘ : 0 < Θ) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hF : ∀ s : ℂ, β ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖F s‖ ≤ C * (1 + |s.im|) ^ N) (k : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, β ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖F s * transform w k s‖ ≤ B / (1 + |s.im|) ^ 2 := by
  have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  obtain ⟨M, hM, hb⟩ := SmoothWeightBounded.derivative_bounds hw hp hrad Θ (2 * (N + 2))
  let W := ((60 / Real.pi) * 4 ^ (N + 2)) * M * X ^ (2 : ℕ) * Θ
  refine ⟨C * W, by dsimp [W]; positivity, fun s hlo hhi ht => ?_⟩
  have hT := transform_t_decay hw hX hΘ hM hp hs hb k s (hβ.trans hlo) hhi
  rw [norm_mul]
  calc
    _ ≤ (C * (1 + |s.im|) ^ N) * (W / (1 + |s.im|) ^ (N + 2)) :=
      mul_le_mul (hF s hlo hhi ht) hT (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; field_simp

end Cubic.BoxAsymptotic.SmoothContourDecay
