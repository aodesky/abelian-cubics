import Cubic.AllGaloisCounts.TrapezoidalGrid
import Cubic.AllGaloisCounts.SliceJunctionGrid

/-! The first uniform trapezoidal sum in the marked-root proof. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceRootSum
open CountData SlicePieces SliceCellEstimate MeasureTheory

theorem estimate {H y : ℝ} (hH : 1 ≤ H) (hy : y ∈ Set.Icc (-1) 1) :
    |(∑' r : ℤ, F (r / H) y) - H * g y| ≤ 156 / H := by
  have hp : 0 < H := by linarith
  let N : ℕ := ⌈2 * H⌉₊
  have hN : 2 * H ≤ (N : ℝ) := Nat.le_ceil _
  have hN' : (N : ℝ) < 2 * H + 1 := Nat.ceil_lt_add_one (by positivity)
  have hn0 : 0 ≤ (N : ℝ) / H := by positivity
  have hNt : vartheta ≤ (N : ℝ) / H := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [vartheta_spec.2.1]
  have hcard : ((Finset.Ico (-(N : ℤ)) N).card : ℝ) ≤ 6 * H := by
    rw [Int.card_Ico, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    linarith
  have hs : (∑' r : ℤ, F (r / H) y) =
      ∑ r ∈ Finset.Icc (-(N : ℤ)) N, F (r / H) y := by
    apply tsum_eq_sum
    intro r hr
    apply outside hy
    rw [abs_div, abs_of_pos hp, le_div_iff₀ hp]
    have hnr : (N : ℝ) < |(r : ℝ)| := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hr
      rcases hr with hr | hr
      · have hrr : (r : ℝ) < -(N : ℝ) := by exact_mod_cast hr
        linarith [neg_le_abs (r : ℝ)]
      · have hrr : (N : ℝ) < (r : ℝ) := by exact_mod_cast hr
        exact hrr.trans_le (le_abs_self _)
    nlinarith [vartheta_spec.2.1]
  have he1 : F (-(N : ℝ) / H) y = 0 := by
    apply outside hy
    simpa only [neg_div, abs_neg, abs_of_nonneg hn0] using hNt
  have he2 : F ((N : ℝ) / H) y = 0 :=
    outside hy (by simpa only [abs_of_nonneg hn0] using hNt)
  have hi : (∫ x in -(N : ℝ) / H..(N : ℝ) / H, F x y) = g y := by
    rw [intervalIntegral.integral_of_le (by rw [neg_div]; linarith)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply outside hy
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · have hnx : (N : ℝ) / H ≤ -x := by rw [neg_div] at hx; linarith
      exact hNt.trans (hnx.trans (neg_le_abs x))
    · exact hNt.trans (hx.le.trans (le_abs_self x))
  have hc := SliceJunctionGrid.sum_bound hH hy (Finset.Ico (-(N : ℤ)) N) hcard
  rw [TrapezoidalGrid.error_cells (continuous y hy), he1, he2, hi] at hc
  simp only [zero_add, zero_div, sub_zero] at hc
  rw [hs]
  have he : (∑ r ∈ Finset.Icc (-(N : ℤ)) N, F (r / H) y) - H * g y =
      H * ((1 / H) * (∑ r ∈ Finset.Icc (-(N : ℤ)) N, F (r / H) y) - g y) := by
    field_simp
  rw [he, abs_mul, abs_of_pos hp]
  calc _ ≤ H * (156 / H ^ 2) := mul_le_mul_of_nonneg_left hc hp.le
    _ = 156 / H := by field_simp

end Cubic.AllGaloisCounts.SliceRootSum
