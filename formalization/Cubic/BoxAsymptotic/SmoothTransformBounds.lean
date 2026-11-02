import Cubic.BoxAsymptotic.SmoothAngularBounds
import Cubic.BoxAsymptotic.SmoothTransformDerivatives

/-! Uniform bounds for the actual test-weight transform. The angular length
contributes `Θ`, and the radial integral contributes `X^σ`. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothTransformBounds

open Set Complex MeasureTheory
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothWeightData
open Cubic.BoxAsymptotic.SmoothWeightCalculus
open Cubic.BoxAsymptotic.SmoothTransformDerivatives
open scoped ContDiff

theorem radial_power_bound {X x σ : ℝ} (hX : 0 < X)
    (hlo : X / 4 ≤ x) (hhi : x ≤ 4 * X) (hσ : 0 ≤ σ) (hσ' : σ ≤ 2) :
    x ^ (σ - 1) ≤ 4 * X ^ (σ - 1) := by
  have hx : 0 < x := by linarith
  have hu : 0 < x / X := div_pos hx hX
  have hu0 : 1 / 4 ≤ x / X := (le_div_iff₀ hX).mpr (by linarith)
  have hu4 : x / X ≤ 4 := (div_le_iff₀ hX).mpr hhi
  have hp : (x / X) ^ (σ - 1) ≤ 4 := by
    rcases le_total 1 (x / X) with hu1 | hu1
    · exact (Real.rpow_le_self_of_one_le hu1 (by linarith)).trans hu4
    · have h := Real.rpow_le_rpow_of_exponent_ge hu hu1 (show -1 ≤ σ - 1 by linarith)
      rw [Real.rpow_neg_one] at h
      apply h.trans
      rw [← one_div, div_le_iff₀ hu]
      linarith
  calc
    _ = X ^ (σ - 1) * (x / X) ^ (σ - 1) := by
      rw [← Real.mul_rpow hX.le hu.le, mul_div_cancel₀ _ hX.ne']
    _ ≤ X ^ (σ - 1) * 4 := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hX.le _)
    _ = _ := by ring

theorem basic_bound {w : ℝ × ℝ → ℝ} {X Θ θ₀ M : ℝ}
    (hX : 0 < X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hb : ∀ p, |w p| ≤ M)
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (k : ℤ) (s : ℂ) (hσ : 0 ≤ s.re) (hσ' : s.re ≤ 2) :
    ‖transform w k s‖ ≤ (60 / Real.pi) * M * X ^ s.re * Θ := by
  have hsrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  have hsang : Function.support w ⊆ {p | |wrap (p.2 - θ₀)| ≤ 4 * Θ} :=
    fun p h => (hs h).2.2
  have hcoef := SmoothAngularBounds.coefficient_norm_le hΘ hM hp hb hsang k
  rw [transform, Cubic.Analysis.CompactMellin.eq_interval (by linarith : 0 < X / 2)
    (angularCoefficient_support hsrad k) (by linarith : X / 4 < X / 2) le_rfl]
  have hab : X / 4 ≤ 4 * X := by linarith
  have hbound : ∀ x ∈ Set.uIoc (X / 4) (4 * X),
      ‖(x : ℂ) ^ (s - 1) * angularCoefficient w k x‖ ≤
        (4 * X ^ (s.re - 1)) * ((4 / Real.pi) * M * Θ) := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul (radial_power_bound hX hx.1.le hx.2 hσ hσ') (hcoef x)
      (norm_nonneg _) (by positivity)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
  calc
    _ ≤ (4 * X ^ (s.re - 1)) * ((4 / Real.pi) * M * Θ) * (4 * X - X / 4) := h
    _ = _ := by
      rw [Real.rpow_sub hX, Real.rpow_one]
      field_simp
      ring

theorem mixed_bound {w : ℝ × ℝ → ℝ} {X Θ θ₀ M : ℝ} {J : ℕ}
    (hw : ContDiff ℝ ∞ w) (hX : 0 < X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M J)
    (k : ℤ) (s : ℂ) (hσ : 0 ≤ s.re) (hσ' : s.re ≤ 2)
    (j ℓ : ℕ) (hjℓ : j + ℓ ≤ J) :
    ‖s‖ ^ j * (Θ * |(k : ℝ)|) ^ ℓ * ‖transform w k s‖ ≤
      (60 / Real.pi) * M * X ^ s.re * Θ := by
  have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  have h := basic_bound hX hΘ hM (mixed_periodic hp Θ j ℓ)
    (hb j ℓ hjℓ) (mixed_support hw
      (SmoothArcGeometry.support_region_closed _ _ _ _) hs Θ j ℓ) k s hσ hσ'
  rw [mixed_identity hw (by linarith) (by linarith) hrad hp] at h
  simpa only [norm_mul, norm_pow, norm_neg, norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hΘ, Complex.norm_intCast] using h

theorem one_add_power {u : ℝ} (hu : 0 ≤ u) (j : ℕ) :
    (1 + u) ^ j ≤ 2 ^ j * u ^ (if 1 ≤ u then j else 0) := by
  split_ifs with h
  · calc
      _ ≤ (2 * u) ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
      _ = _ := mul_pow _ _ _
  · simp only [pow_zero, mul_one]
    exact pow_le_pow_left₀ (by positivity) (by linarith) j

/-- Four mixed estimates, according to whether each frequency is at least one,
give decay in `1+u` and `1+v` without division by a possibly zero frequency. -/
theorem joint_decay_bound {u v N B : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hN : 0 ≤ N) (j : ℕ)
    (h : ∀ r ℓ : ℕ, r ≤ j → ℓ ≤ j → u ^ r * v ^ ℓ * N ≤ B) :
    (1 + u) ^ j * (1 + v) ^ j * N ≤ 4 ^ j * B := by
  let r := if 1 ≤ u then j else 0
  let ℓ := if 1 ≤ v then j else 0
  have hr : r ≤ j := by dsimp [r]; split_ifs <;> omega
  have hℓ : ℓ ≤ j := by dsimp [ℓ]; split_ifs <;> omega
  calc
    _ ≤ (2 ^ j * u ^ r) * (2 ^ j * v ^ ℓ) * N :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (one_add_power hu j) (one_add_power hv j) (by positivity) (by positivity)) hN
    _ = 4 ^ j * (u ^ r * v ^ ℓ * N) := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h r ℓ hr hℓ) (by positivity)

/-- The uniform transform estimate in the proof of `lem:smooth`; total derivative
order `2j` suffices for decay of order `j` in both frequency variables. -/
theorem decay_bound {w : ℝ × ℝ → ℝ} {X Θ θ₀ M : ℝ} {j : ℕ}
    (hw : ContDiff ℝ ∞ w) (hX : 0 < X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M (2 * j))
    (k : ℤ) (s : ℂ) (hσ : 0 ≤ s.re) (hσ' : s.re ≤ 2) :
    ‖transform w k s‖ ≤
      ((60 / Real.pi) * 4 ^ j) * M * X ^ s.re * Θ /
        ((1 + |(k : ℝ)| * Θ) ^ j * (1 + |s.im|) ^ j) := by
  have h := joint_decay_bound (norm_nonneg s) (mul_nonneg hΘ.le (abs_nonneg _))
    (norm_nonneg (transform w k s)) j (fun r ℓ hr hℓ =>
      mixed_bound hw hX hΘ hM hp hs hb k s hσ hσ' r ℓ (by omega))
  have hpos : 0 < (1 + |(k : ℝ)| * Θ) ^ j * (1 + |s.im|) ^ j := by positivity
  rw [le_div_iff₀ hpos]
  calc
    _ ≤ (1 + ‖s‖) ^ j * (1 + Θ * |(k : ℝ)|) ^ j * ‖transform w k s‖ := by
      have ht := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |s.im|)
        (show 1 + |s.im| ≤ 1 + ‖s‖ by linarith [Complex.abs_im_le_norm s]) j
      calc
        _ = (1 + |s.im|) ^ j * (1 + Θ * |(k : ℝ)|) ^ j * ‖transform w k s‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ht (by positivity)) (norm_nonneg _)
    _ ≤ 4 ^ j * ((60 / Real.pi) * M * X ^ s.re * Θ) := h
    _ = _ := by ring

end Cubic.BoxAsymptotic.SmoothTransformBounds
