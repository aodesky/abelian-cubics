import CubicTargets.AllGaloisCounts.MarkedLinearFactorCount
import Cubic.AllGaloisCounts.MarkedRootLatticeSum
import Cubic.AllGaloisCounts.SliceRootSum
import Cubic.AllGaloisCounts.SliceTraceSum

/-! The complete marked-root asymptotic for real heights. The two uniform
trapezoidal sums retain the fractional-part boundary contribution. -/

noncomputable section

namespace Cubic.AllGaloisCounts.MarkedLinearFactorCount
open CountData MarkedLatticeData Filter Asymptotics
open Cubic.Counting.GeneralMonicCount (T card_T_le)

theorem first_sum_error {H : ℝ} (hH : 1 ≤ H) :
    |latticeSum H - H ^ 3 * ∑ a ∈ T H, g ((a : ℝ) / H)| ≤ 468 * H ^ 2 := by
  have hp : 0 < H := by linarith
  have hs : |(∑ a ∈ T H, ∑' r : ℤ, F (r / H) (a / H)) -
      ∑ a ∈ T H, H * g ((a : ℝ) / H)| ≤ 468 := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ a ∈ T H, |(∑' r : ℤ, F (r / H) (a / H)) - H * g ((a : ℝ) / H)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ T H, 156 / H := Finset.sum_le_sum (fun a ha =>
            SliceRootSum.estimate hH (MarkedRootLatticeSum.scaled_parameter hp ha))
      _ = ((T H).card : ℝ) * (156 / H) := by simp
      _ ≤ (3 * H) * (156 / H) := mul_le_mul_of_nonneg_right (card_T_le hH) (by positivity)
      _ = 468 := by field_simp; norm_num
  have he : latticeSum H - H ^ 3 * ∑ a ∈ T H, g ((a : ℝ) / H) =
      H ^ 2 * ((∑ a ∈ T H, ∑' r : ℤ, F (r / H) (a / H)) -
        ∑ a ∈ T H, H * g ((a : ℝ) / H)) := by
    rw [← Finset.mul_sum]
    unfold latticeSum
    ring
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg H)]
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg H)]

theorem estimate : ∃ K : ℝ, ∀ H : ℝ, 1 ≤ H →
    |(markedCount H : ℝ) - R H| ≤ K * H ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := SliceTraceSum.estimate
  refine ⟨486 + K, fun H hH => ?_⟩
  have hp : 0 < H := by linarith
  have hlast : |H ^ 3 * (∑ a ∈ T H, g ((a : ℝ) / H)) - R H| ≤ K * H ^ 2 := by
    have he : H ^ 3 * (∑ a ∈ T H, g ((a : ℝ) / H)) - R H =
        H ^ 3 * ((∑ a ∈ T H, g ((a : ℝ) / H)) -
          (H * markedVolume + (1 - 2 * Int.fract H) * markedBoundary)) := by unfold R; ring
    rw [he, abs_mul, abs_of_pos (pow_pos hp 3)]
    calc _ ≤ H ^ 3 * (K / H) := mul_le_mul_of_nonneg_left (hK H hH) (by positivity)
      _ = K * H ^ 2 := by field_simp
  have h1 := MarkedRootLatticeSum.estimate hH
  have h2 := first_sum_error hH
  calc |(markedCount H : ℝ) - R H| ≤
        |(markedCount H : ℝ) - latticeSum H| + |latticeSum H - R H| := abs_sub_le _ _ _
    _ ≤ |(markedCount H : ℝ) - latticeSum H| +
        (|latticeSum H - H ^ 3 * ∑ a ∈ T H, g ((a : ℝ) / H)| +
          |H ^ 3 * (∑ a ∈ T H, g ((a : ℝ) / H)) - R H|) :=
            add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ (486 + K) * H ^ 2 := by nlinarith

theorem «prop:markedLinearFactorCount» : CubicTargets.AllGaloisCounts.MarkedLinearFactorCount.Claim := by
  refine ⟨MarkedFactorization.markedSet_finite, ?_⟩
  obtain ⟨K, hK⟩ := estimate
  apply IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg H)] using hK H hH

end Cubic.AllGaloisCounts.MarkedLinearFactorCount
