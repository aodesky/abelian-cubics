import CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare
import CubicTargets.Counting.CriticalMeanSquare
import Cubic.Analysis.MeanValueExtension

noncomputable section

namespace Cubic.Counting.CriticalMeanSquare
open Cubic.Counting.HeightCoefficientData Cubic.Analysis.MeanValueExtension
open Filter MeasureTheory

/-- Undo the source's normalization and extend its eventual bound to `T ≥ 2`. -/
theorem «eqn:criticalMeanSquare»
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.CriticalMeanSquare.Claim := by
  obtain ⟨C, hC⟩ := hCN
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hC
  let f : ℝ → ℝ := fun t => ‖zetaE ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2
  have hfc : Continuous f := continuous_zetaE_half.norm.pow 2
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (1 : ℝ) (max T₀ 2)) hfc.continuousOn
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2 : 0 < (Real.log 2) ^ 2 := sq_pos_of_pos hl
  refine ⟨|C| + |B| / (Real.log 2) ^ 2, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hpow : 0 ≤ T * (Real.log T) ^ 2 := by positivity
  by_cases hlarge : T₀ ≤ T
  · have hc := hT₀ T hlarge
    have hmul := mul_le_mul_of_nonneg_left hc hT0.le
    have heq : T * ((1 / T) * (∫ t in (1 : ℝ)..T, f t)) =
        ∫ t in (1 : ℝ)..T, f t := by field_simp
    change T * ((1 / T) * (∫ t in (1 : ℝ)..T, f t)) ≤ _ at hmul
    rw [heq] at hmul
    change (∫ t in (1 : ℝ)..T, f t) ≤ _
    calc _ ≤ T * (C * (Real.log T) ^ 2) := hmul
      _ ≤ (|C| + |B| / (Real.log 2) ^ 2) * T * (Real.log T) ^ 2 := by
        have hc' : C ≤ |C| + |B| / (Real.log 2) ^ 2 := by
          have : 0 ≤ |B| / (Real.log 2) ^ 2 := by positivity
          linarith [le_abs_self C]
        nlinarith [mul_le_mul_of_nonneg_right hc' hpow]
  · have hsmall : T ≤ max T₀ 2 := by linarith [le_max_left T₀ (2 : ℝ)]
    have hi : (∫ t in (1 : ℝ)..T, f t) ≤ |B| * T := by
      calc _ ≤ ∫ _t in (1 : ℝ)..T, |B| := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hfc.intervalIntegrable _ _) intervalIntegrable_const fun t ht => ?_
            have := hB t ⟨ht.1, ht.2.trans hsmall⟩
            have hf0 : 0 ≤ f t := by dsimp [f]; positivity
            rw [Real.norm_of_nonneg hf0] at this
            exact this.trans (le_abs_self B)
        _ = (T - 1) * |B| := by rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ |B| * T := by nlinarith [abs_nonneg B]
    have hlogs : (Real.log 2) ^ 2 ≤ (Real.log T) ^ 2 :=
      pow_le_pow_left₀ hl.le (Real.log_le_log (by norm_num) hT) 2
    have hb' : |B| ≤ (|B| / (Real.log 2) ^ 2) * (Real.log T) ^ 2 := by
      calc |B| = (|B| / (Real.log 2) ^ 2) * (Real.log 2) ^ 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogs (by positivity)
    change (∫ t in (1 : ℝ)..T, f t) ≤ _
    exact hi.trans (by
      nlinarith [mul_le_mul_of_nonneg_right hb' hT0.le,
        mul_nonneg (abs_nonneg C) hpow])

end Cubic.Counting.CriticalMeanSquare
