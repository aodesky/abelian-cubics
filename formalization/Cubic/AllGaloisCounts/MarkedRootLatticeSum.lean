import CubicTargets.AllGaloisCounts.MarkedRootLatticeSum
import Cubic.AllGaloisCounts.MarkedParameterCount
import Cubic.AllGaloisCounts.SlicePieces

/-! The first lattice estimate in the marked-root proof: every interval
contributes its length with error at most one, over a bounded pair of indices. -/

noncomputable section

namespace Cubic.AllGaloisCounts.MarkedRootLatticeSum
open CountData HeightBox IntegerIntervalCount MarkedLatticeData MarkedParameterCount
open Cubic.Counting.GeneralMonicCount (T card_T_le)
open Filter Asymptotics

theorem scaled_parameter {H : ℝ} (hH : 0 < H) {a : ℤ} (ha : a ∈ T H) :
    (a : ℝ) / H ∈ Set.Icc (-1) 1 := by
  have ha' := Cubic.Counting.GeneralTraceDecomposition.abs_le_of_mem ha
  have hh : |(a : ℝ) / H| ≤ 1 := by
    rw [abs_div, abs_of_pos hH, div_le_one hH]
    exact ha'
  exact abs_le.mp hh

theorem root_tsum {H : ℝ} (hH : 0 < H) {a : ℤ} (ha : a ∈ T H) :
    (∑' r : ℤ, F (r / H) (a / H)) = ∑ r ∈ T (2 * H), F (r / H) (a / H) := by
  apply tsum_eq_sum
  intro r hr
  have habs : 2 * H < |(r : ℝ)| := by
    by_contra hn
    apply hr
    simpa only [T, Finset.mem_Icc, Set.mem_Icc] using
      (int_abs_iff r (2 * H)).mp (le_of_not_gt hn)
  apply SlicePieces.outside (scaled_parameter hH ha)
  rw [abs_div, abs_of_pos hH, le_div_iff₀ hH]
  nlinarith [vartheta_spec.2.1]

theorem latticeSum_finite {H : ℝ} (hH : 0 < H) :
    latticeSum H = ∑ a ∈ T H, ∑ r ∈ T (2 * H), H ^ 2 * F (r / H) (a / H) := by
  unfold latticeSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [root_tsum hH ha, Finset.mul_sum]

theorem estimate {H : ℝ} (hH : 1 ≤ H) :
    |(markedCount H : ℝ) - latticeSum H| ≤ 18 * H ^ 2 := by
  have hp : 0 < H := by linarith
  have hsum (a : ℤ) :
      |(∑ r ∈ T (2 * H), (Nat.card (vSet H a r) : ℝ)) -
        ∑ r ∈ T (2 * H), H ^ 2 * F (r / H) (a / H)| ≤ 6 * H := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ r ∈ T (2 * H),
          |(Nat.card (vSet H a r) : ℝ) - H ^ 2 * F (r / H) (a / H)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ T (2 * H), (1 : ℝ) := Finset.sum_le_sum (fun r _ => vSet_error hp a r)
      _ = ((T (2 * H)).card : ℝ) := by simp
      _ ≤ 6 * H := by nlinarith [card_T_le (show 1 ≤ 2 * H by linarith)]
  rw [marked_card hp.le, Nat.cast_sum, latticeSum_finite hp]
  simp only [Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ a ∈ T H,
        |(∑ r ∈ T (2 * H), (Nat.card (vSet H a r) : ℝ)) -
          ∑ r ∈ T (2 * H), H ^ 2 * F (r / H) (a / H)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ T H, 6 * H := Finset.sum_le_sum (fun a _ => hsum a)
    _ = ((T H).card : ℝ) * (6 * H) := by simp
    _ ≤ (3 * H) * (6 * H) := mul_le_mul_of_nonneg_right (card_T_le hH) (by positivity)
    _ = 18 * H ^ 2 := by ring

theorem «eqn:markedRootLatticeSum» : CubicTargets.AllGaloisCounts.MarkedRootLatticeSum.Claim := by
  apply IsBigO.of_bound 18
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg H)] using estimate hH

end Cubic.AllGaloisCounts.MarkedRootLatticeSum
