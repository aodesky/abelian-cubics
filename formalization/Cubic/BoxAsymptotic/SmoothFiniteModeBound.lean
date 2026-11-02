import Cubic.BoxAsymptotic.SmoothMomentBound

/-! The finitely many small frequencies use polynomial growth, including the
zero mode. The normalized derivative budget absorbs that growth without
changing the radial factor `X^(1/2+η)`. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothFiniteModeBound

open Complex Set
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothTransformData Cubic.BoxAsymptotic.SmoothWeightData
open Cubic.Analysis.MellinDirichletPairing
open scoped ContDiff

theorem pairing_bound {w : ℝ × ℝ → ℝ} {F : ℤ → ℂ → ℂ} (S : Finset ℤ)
    {X Θ θ₀ M η C : ℝ} {N j : ℕ}
    (hw : ContDiff ℝ ∞ w) (hX : 0 < X) (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1)
    (hM : 0 ≤ M) (hη : 0 < η) (hη' : η ≤ 1 / 4) (hC : 0 ≤ C)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M (2 * j)) (hj : N + 2 ≤ j)
    (hc : ∀ k ∈ S, Continuous (fun t : ℝ => F k ((1 / 2 + η : ℝ) + t * I)))
    (hg : ∀ t : ℝ, (∑ k ∈ S, ‖F k ((1 / 2 + η : ℝ) + t * I)‖) ≤
      C * η⁻¹ ^ 4 * (1 + |t|) ^ N) :
    (∑ k ∈ S, ‖pairing (1 / 2 + η) (F k) (transform w k)‖) ≤
      ((60 / Real.pi) * 4 ^ j) * M * X ^ (1 / 2 + η) * C * η⁻¹ ^ 4 := by
  let W := ((60 / Real.pi) * 4 ^ j) * M * X ^ (1 / 2 + η)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  apply Cubic.Analysis.VerticalPairingBound.finite_sum _ _ _ _ (by positivity)
  · intro k hk
    have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
      fun p h => ⟨(hs h).1, (hs h).2.1⟩
    exact (hc k hk).mul ((transform_entire hw.continuous
      (by linarith : 0 < X / 2) hrad k).continuous.comp (by fun_prop))
  · intro t
    have hT (k : ℤ) : ‖transform w k ((1 / 2 + η : ℝ) + t * I)‖ ≤
        W / (1 + |t|) ^ j := by
      have h := SmoothTransformBounds.decay_bound hw hX hΘ hM hp hs hb k
        ((1 / 2 + η : ℝ) + t * I) (by simp; linarith) (by simp; linarith)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add] at h
      refine h.trans ?_
      calc
        _ ≤ W / ((1 + |(k : ℝ)| * Θ) ^ j * (1 + |t|) ^ j) :=
          div_le_div_of_nonneg_right (mul_le_of_le_one_right hW hΘ') (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left hW (by positivity)
          (le_mul_of_one_le_left (by positivity)
            (one_le_pow₀ (by nlinarith [mul_nonneg (abs_nonneg (k : ℝ)) hΘ.le] :
              (1 : ℝ) ≤ 1 + |(k : ℝ)| * Θ)))
    calc
      _ ≤ ∑ k ∈ S, ‖F k ((1 / 2 + η : ℝ) + t * I)‖ * (W / (1 + |t|) ^ j) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hT k) (norm_nonneg _)
      _ = (∑ k ∈ S, ‖F k ((1 / 2 + η : ℝ) + t * I)‖) * (W / (1 + |t|) ^ j) :=
        (Finset.sum_mul ..).symm
      _ ≤ (C * η⁻¹ ^ 4 * (1 + |t|) ^ N) * (W / (1 + |t|) ^ j) :=
        mul_le_mul_of_nonneg_right (hg t) (by positivity)
      _ = (W * C * η⁻¹ ^ 4) * ((1 + |t|) ^ N / (1 + |t|) ^ j) := by ring
      _ ≤ (W * C * η⁻¹ ^ 4) * (1 / (1 + |t|) ^ 2) :=
        mul_le_mul_of_nonneg_left (SmoothMomentKernel.polynomial_decay
          (by linarith [abs_nonneg t]) hj) (by positivity)
      _ = _ := by dsimp [W]; ring

end Cubic.BoxAsymptotic.SmoothFiniteModeBound
