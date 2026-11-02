import Cubic.BoxAsymptotic.SmoothTransformBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Mellin inversion for the test weights, with vertical integrability deduced
from the stated derivative bounds rather than retained as an assumption. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothMellinInversion

open MeasureTheory Complex Set
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothWeightData
open scoped ContDiff

theorem integrable_of_squared_decay {f : ℝ → ℂ} {C : ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C / (1 + |t|) ^ 2) : Integrable f := by
  refine (integrable_inv_one_add_sq.const_mul C).mono' hf ?_
  filter_upwards [] with t
  calc
    ‖f t‖ ≤ C / (1 + |t|) ^ 2 := hb t
    _ ≤ C / (1 + t ^ 2) := by
      apply div_le_div_of_nonneg_left hC (by positivity)
      nlinarith [abs_nonneg t, sq_abs t]
    _ = C * (1 + t ^ 2)⁻¹ := div_eq_mul_inv _ _

theorem vertical_integrable {w : ℝ × ℝ → ℝ} {X Θ θ₀ M σ : ℝ}
    (hw : ContDiff ℝ ∞ w) (hX : 0 < X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M 4)
    (k : ℤ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 2) :
    VerticalIntegrable (transform w k) σ := by
  have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  have ht := (transform_entire hw.continuous (by linarith : 0 < X / 2) hrad k).continuous
  apply integrable_of_squared_decay
    (C := ((60 / Real.pi) * 4 ^ (2 : ℕ)) * M * X ^ σ * Θ /
      (1 + |(k : ℝ)| * Θ) ^ 2)
    ((ht.comp (by fun_prop)).aestronglyMeasurable) (by positivity)
  intro t
  have h := SmoothTransformBounds.decay_bound (j := 2) hw hX hΘ hM hp hs hb k
    ((σ : ℂ) + t * I) (by simpa using hσ) (by simpa using hσ')
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add, div_div] using h

theorem inversion {w : ℝ × ℝ → ℝ} {X Θ θ₀ M σ : ℝ}
    (hw : ContDiff ℝ ∞ w) (hX : 0 < X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M 4)
    (k : ℤ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 2) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (transform w k) x = angularCoefficient w k x := by
  have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  exact Cubic.Analysis.CompactMellin.inversion
    (angularCoefficient_continuous hw.continuous k) (by linarith : 0 < X / 2)
    (angularCoefficient_support hrad k) σ
    (vertical_integrable hw hX hΘ hM hp hs hb k hσ hσ') hx

end Cubic.BoxAsymptotic.SmoothMellinInversion
