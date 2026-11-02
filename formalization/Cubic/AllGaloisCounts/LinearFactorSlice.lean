import CubicTargets.AllGaloisCounts.LinearFactorSlice
import Mathlib.MeasureTheory.Group.Integral

/-! The actual interval length and the clipped expression in the proof of
`lemma:linearFactorSliceMoments`. -/

noncomputable section

namespace Cubic.AllGaloisCounts.LinearFactorSlice
open CountData MeasureTheory

theorem «eqn:linearFactorSlice» : CubicTargets.AllGaloisCounts.LinearFactorSlice.Claim := by
  exact ⟨fun y => by simp [F], fun x hx y => by simp only [F, if_neg hx]⟩

def psi (x y : ℝ) : ℝ := 1 + x⁻¹ - x ^ 2 - x * y

theorem length_formula {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    F x y = max (min (x ^ 2 + x * y + 1) |x|⁻¹ -
      max (x ^ 2 + x * y - 1) (-|x|⁻¹)) 0 := by
  rw [F, if_neg hx, Set.Icc_inter_Icc, Real.volume_real_Icc]

theorem lower_endpoint {x y : ℝ} (hx : 0 < x) (hy : -1 ≤ y) :
    -x⁻¹ ≤ x ^ 2 + x * y - 1 := by
  apply (mul_le_mul_iff_right₀ hx).mp
  rw [mul_neg, mul_inv_cancel₀ hx.ne']
  have h1 := mul_nonneg (sq_nonneg (x - 1)) (by linarith : 0 ≤ x + 1)
  have h2 := mul_nonneg (by linarith : 0 ≤ y + 1) (sq_nonneg x)
  nlinarith

theorem clipped {x y : ℝ} (hx : 0 < x) (hy : -1 ≤ y) :
    F x y = min 2 (max 0 (psi x y)) := by
  rw [length_formula hx.ne', abs_of_pos hx, max_eq_left (lower_endpoint hx hy),
    ← min_sub_sub_right]
  have h1 : x ^ 2 + x * y + 1 - (x ^ 2 + x * y - 1) = 2 := by ring
  have h2 : x⁻¹ - (x ^ 2 + x * y - 1) = psi x y := by unfold psi; ring
  rw [h1, h2, max_min_distrib_right]
  norm_num [max_comm]

theorem reflect (x y : ℝ) : F (-x) y = F x (-y) := by
  by_cases hx : x = 0
  · simp [hx, F]
  · simp [F, hx, neg_sq, neg_mul, mul_neg]

theorem g_even : Function.Even g := by
  intro y
  simp only [g, ← reflect]
  exact integral_neg_eq_self (fun x : ℝ => F x y) volume

theorem inverse_square_bound {x : ℝ} (hx : 0 < x) : 3 ≤ (x ^ 2)⁻¹ + 2 * x := by
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hx)).mp
  rw [mul_add, mul_inv_cancel₀ (pow_ne_zero 2 hx.ne')]
  nlinarith [mul_nonneg (sq_nonneg (x - 1)) (by linarith : 0 ≤ 2 * x + 1)]

theorem psi_deriv {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (fun x : ℝ => psi x y) (-(x ^ 2)⁻¹ - 2 * x - y) x := by
  convert (((hasDerivAt_inv hx.ne').const_add 1).sub (hasDerivAt_pow 2 x)).sub
    ((hasDerivAt_id x).mul_const y) using 1 <;> simp [psi]

theorem psi_deriv_bound {x y : ℝ} (hx : 0 < x) (hy : -1 ≤ y) :
    -(x ^ 2)⁻¹ - 2 * x - y ≤ -2 := by
  linarith [inverse_square_bound hx]

end Cubic.AllGaloisCounts.LinearFactorSlice
