import Cubic.AllGaloisCounts.SliceFubini
import Cubic.AllGaloisCounts.SlicePrimitive

/-! The elementary integrations in the volume computation, with the two
antiderivatives recorded in the manuscript's proof comments. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceVolume
open CountData SliceThresholds SliceYIntegral SliceFubini MeasureTheory

def upper (x : ℝ) : ℝ := x * (1 + x + x⁻¹ - (x ^ 2)⁻¹) ^ 2
def lower (x : ℝ) : ℝ := x * (1 - x + x⁻¹ + (x ^ 2)⁻¹) ^ 2
def upperPrimitive (x : ℝ) : ℝ :=
  x ^ 4 / 4 + 2 * x ^ 3 / 3 + 3 * x ^ 2 / 2 - Real.log x + 2 * x⁻¹ - x⁻¹ ^ 2 / 2
def lowerPrimitive (x : ℝ) : ℝ :=
  x ^ 4 / 4 - 2 * x ^ 3 / 3 - x ^ 2 / 2 + 3 * Real.log x - 2 * x⁻¹ - x⁻¹ ^ 2 / 2

theorem upper_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt upperPrimitive (upper x) x := by
  convert ((((((hasDerivAt_pow 4 x).div_const 4).add
    (((hasDerivAt_pow 3 x).const_mul 2).div_const 3)).add
      (((hasDerivAt_pow 2 x).const_mul 3).div_const 2)).sub
        (Real.hasDerivAt_log hx.ne')).add ((hasDerivAt_inv hx.ne').const_mul 2)).sub
          (((hasDerivAt_inv hx.ne').pow 2).div_const 2) using 1
  dsimp [upper]
  field_simp
  <;> ring

theorem lower_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt lowerPrimitive (lower x) x := by
  convert ((((((hasDerivAt_pow 4 x).div_const 4).sub
    (((hasDerivAt_pow 3 x).const_mul 2).div_const 3)).sub
      ((hasDerivAt_pow 2 x).div_const 2)).add
        ((Real.hasDerivAt_log hx.ne').const_mul 3)).sub ((hasDerivAt_inv hx.ne').const_mul 2)).sub
          (((hasDerivAt_inv hx.ne').pow 2).div_const 2) using 1
  dsimp [lower]
  field_simp
  <;> ring

theorem upper_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable upper volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  have h0 : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hc : ContinuousAt upper x := by unfold upper; fun_prop (disch := positivity)
  exact hc.continuousWithinAt

theorem lower_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable lower volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  have h0 : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hc : ContinuousAt lower x := by unfold lower; fun_prop (disch := positivity)
  exact hc.continuousWithinAt

theorem integral_upper {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, upper x) = upperPrimitive b - upperPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (upper_integrable ha hab)
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact upper_deriv (ha.trans_le hx.1)

theorem integral_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, lower x) = lowerPrimitive b - lowerPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (lower_integrable ha hab)
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact lower_deriv (ha.trans_le hx.1)

theorem volume_integrals : (∫ y in (-1 : ℝ)..1, g y) =
    8 - (∫ x in vartheta⁻¹..1, upper x) + ∫ x in (1 : ℝ)..vartheta, lower x := by
  have ht : 0 < vartheta := by linarith [vartheta_spec.1]
  have hi : 0 < vartheta⁻¹ := inv_pos.mpr ht
  have hi1 : vartheta⁻¹ ≤ 1 := inv_le_one_of_one_le₀ vartheta_spec.1.le
  have h1t : 1 ≤ vartheta := vartheta_spec.1.le
  have hfirst : (∫ x in (0 : ℝ)..vartheta⁻¹, J x) = 4 * vartheta⁻¹ := by
    calc _ = ∫ _ : ℝ in (0 : ℝ)..vartheta⁻¹, (4 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le hi.le]
          intro x hx
          exact rectangle hx.1 hx.2
      _ = _ := by simp; ring
  have hsecond : (∫ x in vartheta⁻¹..1, J x) =
      4 * (1 - vartheta⁻¹) - (∫ x in vartheta⁻¹..1, upper x) / 2 := by
    calc _ = ∫ x in vartheta⁻¹..1, 4 - upper x / 2 := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le hi1]
          intro x hx
          rw [upper_triangle hx.1 hx.2]
          unfold upper
          ring
      _ = _ := by
          rw [intervalIntegral.integral_sub intervalIntegrable_const
            ((upper_integrable hi hi1).div_const 2), intervalIntegral.integral_div]
          simp
          ring
  have hthird : (∫ x in (1 : ℝ)..vartheta, J x) =
      (∫ x in (1 : ℝ)..vartheta, lower x) / 2 := by
    calc _ = ∫ x in (1 : ℝ)..vartheta, lower x / 2 := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le h1t]
          intro x hx
          rw [lower_triangle hx.1 hx.2]
          unfold lower
          ring
      _ = _ := intervalIntegral.integral_div (2 : ℝ) lower
  rw [volume_half, ← intervalIntegral.integral_add_adjacent_intervals
    (J_intervalIntegrable 0 vartheta⁻¹) (J_intervalIntegrable vartheta⁻¹ vartheta),
    ← intervalIntegral.integral_add_adjacent_intervals
      (J_intervalIntegrable vartheta⁻¹ 1) (J_intervalIntegrable 1 vartheta),
    hfirst, hsecond, hthird]
  ring

theorem volume : (∫ y in (-1 : ℝ)..1, g y) = markedVolume := by
  have ht : 0 < vartheta := by linarith [vartheta_spec.1]
  have hi : 0 < vartheta⁻¹ := inv_pos.mpr ht
  have hi1 : vartheta⁻¹ ≤ 1 := inv_le_one_of_one_le₀ vartheta_spec.1.le
  rw [volume_integrals, integral_upper hi hi1,
    integral_lower (by norm_num) vartheta_spec.1.le]
  simp only [upperPrimitive, lowerPrimitive, one_pow, inv_one, inv_inv,
    Real.log_one, Real.log_inv]
  unfold markedVolume
  have h4i : vartheta⁻¹ ^ 4 = 2 * vartheta⁻¹ - 1 := by
    calc _ = (vartheta⁻¹ ^ 3) * vartheta⁻¹ := by ring
      _ = (2 - vartheta) * vartheta⁻¹ := by rw [theta_inverse_cube]
      _ = 2 * vartheta⁻¹ - 1 := by
        rw [sub_mul, mul_inv_cancel₀ ht.ne']
  rw [theta_fourth, h4i, theta_inverse_cube]
  have hi2 := theta_inverse_square
  have hi' := theta_inverse
  have ht3 := vartheta_spec.2.2
  rw [div_eq_mul_inv (11 : ℝ) (3 * vartheta), mul_inv_rev]
  nlinarith

end Cubic.AllGaloisCounts.SliceVolume
