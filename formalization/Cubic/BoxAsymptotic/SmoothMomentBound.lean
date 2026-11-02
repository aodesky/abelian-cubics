import Cubic.BoxAsymptotic.SmoothMomentKernel
import Cubic.Analysis.VerticalPairingBound

/-! Applying the first angular moment to each dyadic range, with the actual
Fourier--Mellin weight. All logarithms are absorbed before integration in the
vertical parameter, leaving the uniformly summable angular kernel. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothMomentBound

open Complex MeasureTheory Set
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums
open Cubic.BoxAsymptotic.SmoothTransformData Cubic.BoxAsymptotic.SmoothWeightData
open Cubic.Analysis.MellinDirichletPairing
open scoped ContDiff

theorem block_integrand {w : ℝ × ℝ → ℝ} {F : ℤ → ℂ → ℂ}
    {X Θ θ₀ M K η C D t : ℝ} {A j : ℕ}
    (hw : ContDiff ℝ ∞ w) (hX : 0 < X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hK : 2 ≤ K) (hη : 0 < η) (hη' : η ≤ 1 / 4) (hC : 0 ≤ C)
    (hD : 1 ≤ D) (hDΘ : 1 ≤ D * Θ) (hL : 1 ≤ Real.log (2 * D))
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M (2 * j)) (hj : 2 * A + 2 ≤ j)
    (hfirst : (∑ k ∈ signedModes K, ‖F k ((1 / 2 + η : ℝ) + t * I)‖) ≤
      C * η⁻¹ ^ 4 * momentScale A K t) :
    (∑ k ∈ signedModes K, ‖F k ((1 / 2 + η : ℝ) + t * I) *
      transform w k ((1 / 2 + η : ℝ) + t * I)‖) ≤
        (((60 / Real.pi) * 4 ^ j) * M * X ^ (1 / 2 + η) * C * η⁻¹ ^ 4 *
          Real.log (2 * D) ^ A * (Θ * K / (1 + K * Θ) ^ 2)) / (1 + |t|) ^ 2 := by
  let W := ((60 / Real.pi) * 4 ^ j) * M * X ^ (1 / 2 + η) * Θ
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hu : 0 < 1 + K * Θ := by positivity
  have ht : 0 < 1 + |t| := by positivity
  have hT (k : ℤ) (hk : k ∈ signedModes K) :
      ‖transform w k ((1 / 2 + η : ℝ) + t * I)‖ ≤
        W / ((1 + K * Θ) ^ j * (1 + |t|) ^ j) := by
    have hk' := (mem_signedModes (by linarith : 0 ≤ K)).mp hk
    have h := SmoothTransformBounds.decay_bound hw hX hΘ hM hp hs hb k
      ((1 / 2 + η : ℝ) + t * I) (by simp; linarith) (by simp; linarith)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add] at h
    apply h.trans
    apply div_le_div_of_nonneg_left hW (by positivity)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hu.le (by nlinarith [hk'.1]) j) (by positivity)
  have hsum : (∑ k ∈ signedModes K, ‖F k ((1 / 2 + η : ℝ) + t * I) *
      transform w k ((1 / 2 + η : ℝ) + t * I)‖) ≤
      (C * η⁻¹ ^ 4 * momentScale A K t) *
        (W / ((1 + K * Θ) ^ j * (1 + |t|) ^ j)) := by
    calc
      _ ≤ ∑ k ∈ signedModes K, ‖F k ((1 / 2 + η : ℝ) + t * I)‖ *
          (W / ((1 + K * Θ) ^ j * (1 + |t|) ^ j)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hT k hk) (norm_nonneg _)
      _ = (∑ k ∈ signedModes K, ‖F k ((1 / 2 + η : ℝ) + t * I)‖) *
          (W / ((1 + K * Θ) ^ j * (1 + |t|) ^ j)) := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hfirst (by positivity)
  calc
    _ ≤ (C * η⁻¹ ^ 4 * momentScale A K t) *
        (W / ((1 + K * Θ) ^ j * (1 + |t|) ^ j)) := hsum
    _ = (C * η⁻¹ ^ 4 * K * W) *
        ((1 + |t|) ^ A * Real.log (2 * K + 2 * |t|) ^ A /
          ((1 + K * Θ) ^ j * (1 + |t|) ^ j)) := by unfold momentScale; ring
    _ ≤ (C * η⁻¹ ^ 4 * K * W) *
        (Real.log (2 * D) ^ A / ((1 + K * Θ) ^ 2 * (1 + |t|) ^ 2)) :=
      mul_le_mul_of_nonneg_left (SmoothMomentKernel.decay hK hΘ hD hDΘ hL hj) (by positivity)
    _ = _ := by dsimp [W]; field_simp

theorem block_pairing {w : ℝ × ℝ → ℝ} {F : ℤ → ℂ → ℂ}
    {X Θ θ₀ M K η C D : ℝ} {A j : ℕ}
    (hw : ContDiff ℝ ∞ w) (hX : 0 < X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hK : 2 ≤ K) (hη : 0 < η) (hη' : η ≤ 1 / 4) (hC : 0 ≤ C)
    (hD : 1 ≤ D) (hDΘ : 1 ≤ D * Θ) (hL : 1 ≤ Real.log (2 * D))
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M (2 * j)) (hj : 2 * A + 2 ≤ j)
    (hc : ∀ k ∈ signedModes K, Continuous (fun t : ℝ => F k ((1 / 2 + η : ℝ) + t * I)))
    (hfirst : ∀ t : ℝ, (∑ k ∈ signedModes K, ‖F k ((1 / 2 + η : ℝ) + t * I)‖) ≤
      C * η⁻¹ ^ 4 * momentScale A K t) :
    (∑ k ∈ signedModes K, ‖pairing (1 / 2 + η) (F k) (transform w k)‖) ≤
      ((60 / Real.pi) * 4 ^ j) * M * X ^ (1 / 2 + η) * C * η⁻¹ ^ 4 *
        Real.log (2 * D) ^ A * (Θ * K / (1 + K * Θ) ^ 2) := by
  apply Cubic.Analysis.VerticalPairingBound.finite_sum _ _ _ _ (by positivity)
  · intro k hk
    have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
      fun p h => ⟨(hs h).1, (hs h).2.1⟩
    exact (hc k hk).mul ((transform_entire hw.continuous (by linarith : 0 < X / 2) hrad k).continuous.comp
      (by fun_prop))
  · intro t
    exact block_integrand hw hX hΘ hM hK hη hη' hC hD hDΘ hL hp hs hb hj (hfirst t)

end Cubic.BoxAsymptotic.SmoothMomentBound
