import Cubic.BoxAsymptotic.DyadicSieveScale
import Cubic.BoxAsymptotic.HeckeNormWeights

/-! Combining the forward and dual mean squares. Cubic decay of the weights
absorbs the dual coefficient growth and yields the summable dyadic majorant.
-/

namespace Cubic.BoxAsymptotic.MixedDyadicBound

open Cubic.BoxAsymptotic.AngularMomentDyadic

theorem norm_add_sq (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hn := norm_add_le x y
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem sum_bound {ι : Type*} (S : Finset ι) (f g p : ι → ℂ) {F G P : ℝ}
    (hp : ∀ i ∈ S, ‖p i‖ ≤ P)
    (hf : (∑ i ∈ S, ‖f i‖ ^ 2) ≤ F) (hg : (∑ i ∈ S, ‖g i‖ ^ 2) ≤ G) :
    (∑ i ∈ S, ‖f i + p i * g i‖ ^ 2) ≤ 2 * F + 2 * P ^ 2 * G := by
  calc
    _ ≤ ∑ i ∈ S, (2 * ‖f i‖ ^ 2 + (2 * P ^ 2) * ‖g i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := norm_add_sq (f i) (p i * g i)
      rw [norm_mul, mul_pow] at h
      have hP := pow_le_pow_left₀ (norm_nonneg _) (hp i hi) 2
      nlinarith [mul_le_mul_of_nonneg_right hP (sq_nonneg ‖g i‖)]
    _ = 2 * (∑ i ∈ S, ‖f i‖ ^ 2) + (2 * P ^ 2) * ∑ i ∈ S, ‖g i‖ ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hf (by norm_num))
      (mul_le_mul_of_nonneg_left hg (by positivity))

theorem dyadic_bound {ι : Type*} (S : Finset ι) (f g p : ι → ℂ)
    {K Y D Cs Cp η : ℝ} (hK : 0 ≤ K) (hKY : K ≤ 2 * Y) (hY : 2 ≤ Y)
    (hCs : 0 ≤ Cs) (hη : 0 ≤ η) (hη' : η ≤ 1) (j : ℕ)
    (hp : ∀ i ∈ S, ‖p i‖ ≤ Cp * Y ^ (-2 * η))
    (hf : (∑ i ∈ S, ‖f i‖ ^ 2) ≤ (D * (1 / 8 : ℝ) ^ j) ^ 2 *
      (Cs * (K + (2 : ℝ) ^ j * Y) * Real.log (2 * ((2 : ℝ) ^ j * Y)) ^ 5))
    (hg : (∑ i ∈ S, ‖g i‖ ^ 2) ≤ (D * (1 / 8 : ℝ) ^ j) ^ 2 *
      (((2 : ℝ) ^ j * Y) ^ η) ^ 2 *
      (Cs * (K + (2 : ℝ) ^ j * Y) * Real.log (2 * ((2 : ℝ) ^ j * Y)) ^ 5)) :
    (∑ i ∈ S, ‖f i + p i * g i‖ ^ 2) ≤
      (6 * D ^ 2 * Cs * (1 + Cp ^ 2)) * weight j ^ 2 * Y * Real.log (2 * Y) ^ 6 := by
  let R := (K + (2 : ℝ) ^ j * Y) * Real.log (2 * ((2 : ℝ) ^ j * Y)) ^ 5
  have htwo : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hlog : 0 ≤ Real.log (2 * ((2 : ℝ) ^ j * Y)) :=
    Real.log_nonneg (by nlinarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hdual := HeckeNormWeights.dual_prefactor (by linarith : 1 ≤ Y) hη hη' j
  have hd : (Cp * Y ^ (-2 * η)) ^ 2 * (((2 : ℝ) ^ j * Y) ^ η) ^ 2 ≤
      Cp ^ 2 * ((2 : ℝ) ^ j) ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity) hdual 2
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg Cp)
    convert hm using 1
    ring
  have hb := sum_bound S f g p hp hf hg
  have hRs := Cubic.BoxAsymptotic.DyadicSieveScale.dyadic_sieve_scale hKY hY j
  let T := 2 * D ^ 2 * Cs * (1 + Cp ^ 2)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpre : 1 + (Cp * Y ^ (-2 * η)) ^ 2 * (((2 : ℝ) ^ j * Y) ^ η) ^ 2 ≤
      (1 + Cp ^ 2) * ((2 : ℝ) ^ j) ^ 2 := by nlinarith
  have hfac : 0 ≤ 2 * D ^ 2 * ((1 / 8 : ℝ) ^ j) ^ 2 * Cs * R := by positivity
  calc
    _ ≤ (2 * D ^ 2 * ((1 / 8 : ℝ) ^ j) ^ 2 * Cs * R) *
        (1 + (Cp * Y ^ (-2 * η)) ^ 2 * (((2 : ℝ) ^ j * Y) ^ η) ^ 2) := by
      convert hb using 1
      dsimp [R]
      ring
    _ ≤ (2 * D ^ 2 * ((1 / 8 : ℝ) ^ j) ^ 2 * Cs * R) *
        ((1 + Cp ^ 2) * ((2 : ℝ) ^ j) ^ 2) := mul_le_mul_of_nonneg_left hpre hfac
    _ = T * ((1 / 8 : ℝ) ^ j * 2 ^ j) ^ 2 * R := by dsimp [T]; ring
    _ ≤ T * ((1 / 8 : ℝ) ^ j * 2 ^ j) ^ 2 *
        (3 * (4 : ℝ) ^ j * ((j : ℝ) + 1) ^ 6 * Y * Real.log (2 * Y) ^ 6) :=
      mul_le_mul_of_nonneg_left hRs (by positivity)
    _ = T * (((1 / 8 : ℝ) ^ j * 2 ^ j) ^ 2 * (3 * (4 : ℝ) ^ j * ((j : ℝ) + 1) ^ 6)) *
        Y * Real.log (2 * Y) ^ 6 := by ring
    _ = _ := by rw [Cubic.BoxAsymptotic.DyadicSieveScale.combine_decay]; dsimp [T]; ring

end Cubic.BoxAsymptotic.MixedDyadicBound
