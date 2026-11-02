import Cubic.Analysis.GaussianResidue
import CubicTargets.Counting.CriticalMeanSquare
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Integrating the direct Gaussian residue bound in `lemma:xiMeanValue`.
The central interval contributes `O(U log² U)` by `eqn:criticalMeanSquare`;
the complementary Gaussian tails contribute `O(1)`. Only at the last step
is `log² U` bounded by `O_η(U^η)`.
-/

noncomputable section

namespace Cubic.Analysis.GaussianMeanValue
open Complex Set Filter Topology MeasureTheory
open Cubic.Counting.HeightCoefficientData Cubic.Analysis.MeanValueExtension
open scoped Interval

/-- Retain Gaussian decay in both `U` and `v` outside the central interval. -/
lemma gauss_window_le {U : ℝ} (hU : 2 ≤ U) (f : ℝ → ℝ) (v : ℝ) (hz : 0 ≤ f v) :
    f v * ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2) ≤
      Real.sqrt Real.pi * (Icc (U / 2) (4 * U)).indicator f v +
        8 * (f v * Real.exp (-(1 / 32) * v ^ 2)) := by
  have hU0 : 0 ≤ U := by linarith
  by_cases hv : v ∈ Icc (U / 2) (4 * U)
  · rw [indicator_of_mem hv]
    have hW : ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2) ≤ Real.sqrt Real.pi := by
      simp_rw [show ∀ t : ℝ, (v - t) ^ 2 = (t - v) ^ 2 by intro t; ring]
      rw [← integral_gauss_shift v]
      exact intervalIntegral_le_integral (integrable_gauss_shift v)
        (fun t => (Real.exp_pos _).le) (by linarith)
    nlinarith [mul_nonneg hz (Real.exp_pos (-(1 / 32) * v ^ 2)).le]
  · rw [indicator_of_notMem hv, mul_zero, zero_add]
    have hfar : ∀ t ∈ Icc U (2 * U), Real.exp (-(v - t) ^ 2) ≤
        Real.exp (-(1 / 32) * U ^ 2) * Real.exp (-(1 / 32) * v ^ 2) := by
      intro t ht
      have hd : (U + |v|) / 4 ≤ |v - t| := by
        simp only [mem_Icc, not_and_or, not_le] at hv
        rcases hv with hv | hv
        · rw [abs_of_neg (show v - t < 0 by linarith [ht.1])]
          rcases le_or_gt 0 v with h0 | h0
          · rw [abs_of_nonneg h0]; linarith [ht.1]
          · rw [abs_of_neg h0]; linarith [ht.1]
        · rw [abs_of_pos (show 0 < v - t by linarith [ht.2]),
            abs_of_pos (show 0 < v by linarith)]
          linarith [ht.2]
      have hd2 := pow_le_pow_left₀ (by positivity : 0 ≤ (U + |v|) / 4) hd 2
      rw [sq_abs] at hd2
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_abs v, mul_nonneg hU0 (abs_nonneg v), sq_nonneg U, sq_nonneg v]
    have hW : ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2) ≤
        U * (Real.exp (-(1 / 32) * U ^ 2) * Real.exp (-(1 / 32) * v ^ 2)) := by
      calc _ ≤ ∫ _t in U..2 * U,
            Real.exp (-(1 / 32) * U ^ 2) * Real.exp (-(1 / 32) * v ^ 2) :=
          intervalIntegral.integral_mono_on (by linarith)
            ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(v - t) ^ 2)).intervalIntegrable _ _)
            intervalIntegrable_const hfar
        _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hdecay : U * Real.exp (-(1 / 32) * U ^ 2) ≤ 8 := by
      have h1 := Real.add_one_le_exp (U ^ 2 / 32)
      have h2 : U ≤ 8 * Real.exp (U ^ 2 / 32) := by
        nlinarith [sq_nonneg (U - 2)]
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(U ^ 2 / 32))).le
      have he : Real.exp (U ^ 2 / 32) * Real.exp (-(U ^ 2 / 32)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      rw [mul_assoc, he, mul_one] at h3
      convert h3 using 1 <;> congr 2 <;> ring
    calc f v * ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2)
        ≤ f v * (U * (Real.exp (-(1 / 32) * U ^ 2) * Real.exp (-(1 / 32) * v ^ 2))) :=
          mul_le_mul_of_nonneg_left hW hz
      _ = (U * Real.exp (-(1 / 32) * U ^ 2)) *
          (f v * Real.exp (-(1 / 32) * v ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdecay (by positivity)

/-- The current paper's uniform mean-value bound, using its direct residue proof. -/
theorem mean_value_strip (hCrit : CubicTargets.Counting.CriticalMeanSquare.Claim)
    (hG : Growth) (δ : ℝ) (hδ : 0 < δ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → ∀ U : ℝ, 2 ≤ U →
      ∫ t in U..2 * U, ‖zetaE (σ + t * Complex.I)‖ ^ 2 ≤ K * U ^ (1 + η) := by
  obtain ⟨K₀, hK₀, hpt⟩ := GaussianResidue.pointwise_nonneg hG δ hδ
  obtain ⟨C, hC0, hC⟩ := hCrit
  obtain ⟨M, -, hM⟩ := norm_zetaE_half_le hG
  set Z : ℝ → ℝ := fun v => ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2 with hZdef
  have hZc : Continuous Z := continuous_zetaE_half.norm.pow 2
  have hZ0 : ∀ v, 0 ≤ Z v := fun v => by positivity
  have hZM : ∀ v, |Z v| ≤ M * (1 + |v|) ^ 8 := fun v => by
    rw [abs_of_nonneg (hZ0 v)]; exact (hM v).2
  have hgauss := integrable_mul_gauss hZc hZM (b := 1 / 32) (by norm_num)
  set Mint := ∫ v : ℝ, Z v * Real.exp (-(1 / 32) * v ^ 2)
  have hMint : 0 ≤ Mint := integral_nonneg fun v => mul_nonneg (hZ0 v) (Real.exp_pos _).le
  refine ⟨K₀ * (1 + Real.sqrt Real.pi * (36 * C * (2 / η) ^ 2) + 8 * Mint),
    fun σ hσ1 hσ2 U hU => ?_⟩
  obtain ⟨hI₂int, hZWint, hswap⟩ := gauss_average_swap hG hU
  have hU0 : 0 < U := by linarith
  have hlog : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  have hUp : U ≤ U ^ (1 + η) := by
    calc U = U ^ (1 : ℝ) := (Real.rpow_one U).symm
      _ ≤ U ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hUp1 : 1 ≤ U ^ (1 + η) := by linarith
  -- The critical-line integral over the central interval.
  have hnear : ∫ v in U / 2..4 * U, Z v ≤ 36 * C * U * (Real.log U) ^ 2 := by
    have hi := intervalIntegral.integral_mono_interval (f := Z) (μ := volume)
      (show 1 ≤ U / 2 by linarith) (show U / 2 ≤ 4 * U by linarith) le_rfl
      (Filter.Eventually.of_forall hZ0) (hZc.intervalIntegrable 1 (4 * U))
    have hc := hC (4 * U) (by linarith)
    have hl2 : Real.log 2 ≤ Real.log U := Real.log_le_log (by norm_num) hU
    have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hl4U : Real.log (4 * U) ≤ 3 * Real.log U := by
      rw [Real.log_mul (by norm_num) hU0.ne', hl4]
      linarith
    have hsq : (Real.log (4 * U)) ^ 2 ≤ 9 * (Real.log U) ^ 2 := by
      have := pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ 4 * U)) hl4U 2
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq (mul_nonneg hC0 hU0.le)
    exact hi.trans (hc.trans (by nlinarith))
  -- Fubini and the Gaussian window bound give a bounded tail contribution.
  have hI₂ : ∫ t in U..2 * U, (∫ v : ℝ, Real.exp (-(v - t) ^ 2) * Z v) ≤
      Real.sqrt Real.pi * (36 * C * U * (Real.log U) ^ 2) + 8 * Mint := by
    have hind : Integrable ((Icc (U / 2) (4 * U)).indicator Z) :=
      (hZc.integrableOn_Icc).integrable_indicator measurableSet_Icc
    rw [hswap]
    calc ∫ v : ℝ, Z v * ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2)
        ≤ ∫ v : ℝ, (Real.sqrt Real.pi * (Icc (U / 2) (4 * U)).indicator Z v +
            8 * (Z v * Real.exp (-(1 / 32) * v ^ 2))) :=
          integral_mono hZWint ((hind.const_mul _).add (hgauss.const_mul _))
            fun v => gauss_window_le hU Z v (hZ0 v)
      _ = Real.sqrt Real.pi * (∫ v in U / 2..4 * U, Z v) + 8 * Mint := by
          rw [integral_add (hind.const_mul _) (hgauss.const_mul _), integral_const_mul,
            integral_const_mul, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by linarith)]
      _ ≤ _ := by gcongr
  have hLint : IntervalIntegrable (fun t : ℝ => ‖zetaE (σ + t * Complex.I)‖ ^ 2) volume U
      (2 * U) := by
    refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
    rw [uIcc_of_le (by linarith)] at ht
    have hne : (σ : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [ht.1]
    exact ((continuousAt_zetaE hne).comp (f := fun t : ℝ => (σ : ℂ) + t * I)
      (by fun_prop)).norm.pow 2
  have hlogpow : (Real.log U) ^ 2 ≤ (2 / η) ^ 2 * U ^ η := by
    have hl := Real.log_le_rpow_div hU0.le (show 0 < η / 2 by linarith)
    have he : U ^ (η / 2) / (η / 2) = (2 / η) * U ^ (η / 2) := by field_simp
    rw [he] at hl
    have hsq : (U ^ (η / 2)) ^ 2 = U ^ η := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
      congr 1
      norm_num
    calc (Real.log U) ^ 2 ≤ ((2 / η) * U ^ (η / 2)) ^ 2 := pow_le_pow_left₀ hlog hl 2
      _ = (2 / η) ^ 2 * U ^ η := by rw [mul_pow, hsq]
  have hmain : U * (Real.log U) ^ 2 ≤ (2 / η) ^ 2 * U ^ (1 + η) := by
    calc _ ≤ U * ((2 / η) ^ 2 * U ^ η) := mul_le_mul_of_nonneg_left hlogpow hU0.le
      _ = _ := by rw [Real.rpow_add hU0, Real.rpow_one]; ring
  calc ∫ t in U..2 * U, ‖zetaE (σ + t * Complex.I)‖ ^ 2
      ≤ ∫ t in U..2 * U, K₀ * (1 + ∫ v : ℝ, Real.exp (-(v - t) ^ 2) * Z v) :=
        intervalIntegral.integral_mono_on (by linarith) hLint
          ((IntervalIntegrable.add intervalIntegrable_const hI₂int).const_mul K₀)
          fun t ht => hpt σ hσ1 hσ2 t (by linarith [ht.1])
    _ = K₀ * (U + ∫ t in U..2 * U, (∫ v : ℝ, Real.exp (-(v - t) ^ 2) * Z v)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add intervalIntegrable_const hI₂int,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ K₀ * (U + (Real.sqrt Real.pi * (36 * C * U * (Real.log U) ^ 2) + 8 * Mint)) := by
        gcongr
    _ ≤ K₀ * ((1 + Real.sqrt Real.pi * (36 * C * (2 / η) ^ 2) + 8 * Mint) * U ^ (1 + η)) := by
        apply mul_le_mul_of_nonneg_left _ hK₀
        have hm := mul_le_mul_of_nonneg_left hmain (show 0 ≤ Real.sqrt Real.pi * (36 * C) by positivity)
        have ht := mul_le_mul_of_nonneg_left hUp1 (show 0 ≤ 8 * Mint by positivity)
        nlinarith
    _ = K₀ * (1 + Real.sqrt Real.pi * (36 * C * (2 / η) ^ 2) + 8 * Mint) * U ^ (1 + η) := by ring

end Cubic.Analysis.GaussianMeanValue
