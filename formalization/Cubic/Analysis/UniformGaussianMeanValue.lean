import Cubic.Analysis.UniformGaussianKernel

/-! Full closed-strip mean square from the critical-line input. The reflected
Gaussian kernel supplies uniformity; the critical endpoint is estimated directly. -/
noncomputable section
namespace Cubic.Analysis.UniformGaussianMeanValue
open Complex Set Filter Topology MeasureTheory
open Cubic.Counting.HeightCoefficientData Cubic.Analysis.MeanValueExtension
open Cubic.Analysis.PoissonGaussianWeight
open scoped Interval

lemma weight_window_le {δ U : ℝ} (hδ : 0 < δ) (hU : 2 ≤ U)
    (f : ℝ → ℝ) (v : ℝ) (hz : 0 ≤ f v) :
    f v * (∫ t in U..2 * U, weight δ (v - t)) ≤
      Real.pi * (Icc (U / 2) (4 * U)).indicator f v +
        8 * (f v * Real.exp (-(1 / 32) * v ^ 2)) := by
  by_cases hv : v ∈ Icc (U / 2) (4 * U)
  · rw [indicator_of_mem hv]
    have hW : (∫ t in U..2 * U, weight δ (v - t)) ≤ Real.pi := by
      have he : ∀ t : ℝ, weight δ (v - t) = weight δ (t - v) := by
        intro t; simp only [weight]; congr 2 <;> ring
      simp_rw [he]
      exact (intervalIntegral_le_integral (integrable_weight hδ v)
        (fun t => nonneg hδ _) (by linarith)).trans (mass_le hδ v)
    nlinarith [mul_nonneg hz (Real.exp_pos (-(1 / 32) * v ^ 2)).le]
  · have hd : ∀ t ∈ Icc U (2 * U), 1 ≤ |v - t| := by
      intro t ht
      simp only [mem_Icc, not_and_or, not_le] at hv
      rcases hv with hv | hv
      · rw [abs_of_neg (by linarith [ht.1] : v - t < 0)]
        linarith [ht.1]
      · rw [abs_of_pos (by linarith [ht.2] : 0 < v - t)]
        linarith [ht.2]
    have hw : ∀ t ∈ Icc U (2 * U), weight δ (v - t) ≤ Real.exp (-(v - t) ^ 2) := by
      intro t ht
      have hsq : 1 ≤ (v - t) ^ 2 := by nlinarith [hd t ht, sq_abs (v - t)]
      have hden : δ ≤ δ ^ 2 + (v - t) ^ 2 := by nlinarith [sq_nonneg (δ - 1 / 2)]
      unfold weight
      exact mul_le_of_le_one_left (Real.exp_pos _).le
        ((div_le_one (denominator_pos hδ _)).mpr hden)
    have hW : (∫ t in U..2 * U, weight δ (v - t)) ≤
        ∫ t in U..2 * U, Real.exp (-(v - t) ^ 2) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (((PoissonGaussianWeight.continuous hδ).comp (by fun_prop)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(v - t) ^ 2)).intervalIntegrable _ _) hw
    have hg := GaussianMeanValue.gauss_window_le hU f v hz
    rw [indicator_of_notMem hv, mul_zero, zero_add] at hg ⊢
    exact (mul_le_mul_of_nonneg_left hW hz).trans hg

theorem mean_value_interior (hCrit : CubicTargets.Counting.CriticalMeanSquare.Claim)
    (hG : Growth) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 2 → ∀ U : ℝ, 2 ≤ U →
      ∫ t in U..2 * U, ‖zetaE (σ + t * Complex.I)‖ ^ 2 ≤ K * U ^ (1 + η) := by
  obtain ⟨K₀, hK₀, hpt⟩ := UniformGaussianKernel.pointwise_nonneg hG
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
  refine ⟨K₀ * (1 + Real.pi * (36 * C * (2 / η) ^ 2) + 8 * Mint),
    by positivity, fun σ hσ1 hσ2 U hU => ?_⟩
  obtain ⟨hI₂int, hZWint, hswap⟩ := average_swap hG (by linarith : 0 < σ - 1 / 2) hU
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
  have hI₂ : ∫ t in U..2 * U, (∫ v : ℝ, weight (σ - 1 / 2) (v - t) * Z v) ≤
      Real.pi * (36 * C * U * (Real.log U) ^ 2) + 8 * Mint := by
    have hind : Integrable ((Icc (U / 2) (4 * U)).indicator Z) :=
      (hZc.integrableOn_Icc).integrable_indicator measurableSet_Icc
    rw [hswap]
    calc ∫ v : ℝ, Z v * ∫ t in U..2 * U, weight (σ - 1 / 2) (v - t)
        ≤ ∫ v : ℝ, (Real.pi * (Icc (U / 2) (4 * U)).indicator Z v +
            8 * (Z v * Real.exp (-(1 / 32) * v ^ 2))) :=
          integral_mono hZWint ((hind.const_mul _).add (hgauss.const_mul _))
            fun v => weight_window_le (by linarith : 0 < σ - 1 / 2) hU Z v (hZ0 v)
      _ = Real.pi * (∫ v in U / 2..4 * U, Z v) + 8 * Mint := by
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
      ≤ ∫ t in U..2 * U, K₀ * (1 + ∫ v : ℝ, weight (σ - 1 / 2) (v - t) * Z v) :=
        intervalIntegral.integral_mono_on (by linarith) hLint
          ((IntervalIntegrable.add intervalIntegrable_const hI₂int).const_mul K₀)
          fun t ht => hpt σ hσ1 hσ2 t (by linarith [ht.1])
    _ = K₀ * (U + ∫ t in U..2 * U, (∫ v : ℝ, weight (σ - 1 / 2) (v - t) * Z v)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add intervalIntegrable_const hI₂int,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ K₀ * (U + (Real.pi * (36 * C * U * (Real.log U) ^ 2) + 8 * Mint)) := by
        gcongr
    _ ≤ K₀ * ((1 + Real.pi * (36 * C * (2 / η) ^ 2) + 8 * Mint) * U ^ (1 + η)) := by
        apply mul_le_mul_of_nonneg_left _ hK₀
        have hm := mul_le_mul_of_nonneg_left hmain (show 0 ≤ Real.pi * (36 * C) by positivity)
        have ht := mul_le_mul_of_nonneg_left hUp1 (show 0 ≤ 8 * Mint by positivity)
        nlinarith
    _ = K₀ * (1 + Real.pi * (36 * C * (2 / η) ^ 2) + 8 * Mint) * U ^ (1 + η) := by ring

lemma mean_value_critical (hCrit : CubicTargets.Counting.CriticalMeanSquare.Claim)
    (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℝ, 2 ≤ U →
      (∫ t in U..2 * U, ‖zetaE ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤ K * U ^ (1 + η) := by
  obtain ⟨C, hC0, hC⟩ := hCrit
  refine ⟨36 * C * (2 / η) ^ 2, by positivity, fun U hU => ?_⟩
  let Z : ℝ → ℝ := fun v => ‖zetaE ((1 / 2 : ℂ) + v * I)‖ ^ 2
  have hZc : Continuous Z := continuous_zetaE_half.norm.pow 2
  have hZ0 : ∀ v, 0 ≤ Z v := fun v => by positivity
  have hU0 : 0 < U := by linarith
  have hlog : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
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
  have hi := intervalIntegral.integral_mono_interval (f := Z) (μ := volume)
    (show U / 2 ≤ U by linarith) (show U ≤ 2 * U by linarith)
    (show 2 * U ≤ 4 * U by linarith) (Eventually.of_forall hZ0)
    (hZc.intervalIntegrable _ _)
  calc (∫ t in U..2 * U, Z t) ≤ 36 * C * U * (Real.log U) ^ 2 := hi.trans hnear
    _ ≤ 36 * C * (2 / η) ^ 2 * U ^ (1 + η) := by
      have hm := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 36 * C by positivity)
      nlinarith

/-- Uniformity includes the critical line; no extra analytic input is used. -/
theorem mean_value_strip (hCrit : CubicTargets.Counting.CriticalMeanSquare.Claim)
    (hG : Growth) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → ∀ U : ℝ, 2 ≤ U →
      (∫ t in U..2 * U, ‖zetaE ((σ : ℂ) + t * I)‖ ^ 2) ≤ K * U ^ (1 + η) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := mean_value_interior hCrit hG η hη
  obtain ⟨K₂, hK₂0, hK₂⟩ := mean_value_critical hCrit η hη
  refine ⟨max K₁ K₂, fun σ hσ hσ2 U hU => ?_⟩
  rcases eq_or_lt_of_le hσ with he | he
  · subst σ
    calc _ ≤ K₂ * U ^ (1 + η) := by simpa using hK₂ U hU
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right K₁ K₂) (by positivity)
  · exact (hK₁ σ he hσ2 U hU).trans
      (mul_le_mul_of_nonneg_right (le_max_left K₁ K₂) (by positivity))

end Cubic.Analysis.UniformGaussianMeanValue
