import Cubic.AllGaloisCounts.SlicePieces
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Uniform derivative and Lipschitz bounds for the clipped slices. All
nonconstant pieces lie in `1/2 <= |x| <= 2`. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceUniformBounds
open CountData LinearFactorSlice SliceThresholds SlicePieces

theorem half_le_theta_inv : (1 / 2 : ℝ) ≤ vartheta⁻¹ := by
  have ht : 0 < vartheta := by linarith [vartheta_spec.1]
  apply (le_inv_comm₀ (by norm_num : (0 : ℝ) < 1 / 2) ht).mpr
  norm_num
  exact vartheta_spec.2.1.le

theorem first_derivative_bound {x y : ℝ} (hx : x ∈ Set.Icc (1 / 2) 2)
    (hy : y ∈ Set.Icc (-1) 1) : |-(x ^ 2)⁻¹ - 2 * x - y| ≤ 9 := by
  have hp : 0 < x := by linarith [hx.1]
  have hi : x⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hp).mpr (by linarith [hx.1])
  have hi0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hp.le
  have hi2 : (x ^ 2)⁻¹ ≤ 4 := by rw [← inv_pow]; nlinarith
  rw [abs_of_nonpos (by linarith [psi_deriv_bound hp hy.1])]
  linarith [hx.2, hy.2]

theorem psi_lipschitz {y : ℝ} (hy : y ∈ Set.Icc (-1) 1)
    {x z : ℝ} (hx : x ∈ Set.Icc (1 / 2) 2) (hz : z ∈ Set.Icc (1 / 2) 2) :
    |psi x y - psi z y| ≤ 9 * |x - z| := by
  have hd (w : ℝ) (hw : w ∈ Set.Icc (1 / 2 : ℝ) 2) :
      HasDerivWithinAt (fun x => psi x y) (-(w ^ 2)⁻¹ - 2 * w - y)
        (Set.Icc (1 / 2) 2) w :=
    (psi_deriv (show 0 < w by linarith [hw.1]) y).hasDerivWithinAt
  have hb (w : ℝ) (hw : w ∈ Set.Icc (1 / 2 : ℝ) 2) :
      ‖-(w ^ 2)⁻¹ - 2 * w - y‖ ≤ 9 := by
    rw [Real.norm_eq_abs]
    exact first_derivative_bound hw hy
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (1 / 2 : ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hz hx

def clamp (x : ℝ) : ℝ := max (1 / 2) (min 2 x)

theorem clamp_mem (x : ℝ) : clamp x ∈ Set.Icc (1 / 2) 2 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clamp_lipschitz (x z : ℝ) : |clamp x - clamp z| ≤ |x - z| := by
  have h : LipschitzWith 1 clamp := (LipschitzWith.id.const_min 2).const_max (1 / 2)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul x z

theorem clipped_lipschitz (u v : ℝ) :
    |min 2 (max 0 u) - min 2 (max 0 v)| ≤ |u - v| := by
  have h : LipschitzWith 1 (fun u : ℝ => min 2 (max 0 u)) :=
    (LipschitzWith.id.const_max 0).const_min 2
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul u v

def positiveSlice (y x : ℝ) : ℝ := F (clamp x) y

theorem positive_eq {y x : ℝ} (hy : y ∈ Set.Icc (-1) 1) (hx : 0 ≤ x) :
    positiveSlice y x = F x y := by
  have hlo : (1 / 2 : ℝ) ≤ minus y := half_le_theta_inv.trans (bounds hy).1
  have hhi : plus y ≤ 2 := (bounds hy).2.2.2.trans vartheta_spec.2.1.le
  unfold positiveSlice
  by_cases hl : x ≤ 1 / 2
  · have he : clamp x = 1 / 2 := by
      unfold clamp
      rw [max_eq_left ((min_le_right _ _).trans hl)]
    rw [he, before hy (by norm_num) hlo, before hy hx (hl.trans hlo)]
  · by_cases hr : 2 ≤ x
    · have he : clamp x = 2 := by unfold clamp; rw [min_eq_left hr]; norm_num
      rw [he, after hy hhi, after hy (hhi.trans hr)]
    · have he : clamp x = x := by
        unfold clamp
        rw [min_eq_right (le_of_not_ge hr), max_eq_right (le_of_not_ge hl)]
      rw [he]

theorem positive_const {y x : ℝ} (hy : y ∈ Set.Icc (-1) 1) (hx : x ≤ 0) :
    positiveSlice y x = 2 := by
  have he : clamp x = 1 / 2 := by
    unfold clamp
    rw [max_eq_left ((min_le_right _ _).trans (by linarith))]
  rw [positiveSlice, he]
  exact before hy (by norm_num) (half_le_theta_inv.trans (bounds hy).1)

theorem positive_lipschitz {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) (x z : ℝ) :
    |positiveSlice y x - positiveSlice y z| ≤ 9 * |x - z| := by
  have hx : 0 < clamp x := by linarith [(clamp_mem x).1]
  have hz : 0 < clamp z := by linarith [(clamp_mem z).1]
  rw [positiveSlice, positiveSlice, clipped hx hy.1, clipped hz hy.1]
  exact (clipped_lipschitz _ _).trans
    ((psi_lipschitz hy (clamp_mem x) (clamp_mem z)).trans
      (mul_le_mul_of_nonneg_left (clamp_lipschitz x z) (by norm_num)))

theorem slice_sum {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) (x : ℝ) :
    F x y = positiveSlice y x + positiveSlice (-y) (-x) - 2 := by
  by_cases hx : 0 ≤ x
  · rw [positive_eq hy hx, positive_const (neg_parameter hy) (by linarith)]
    ring
  · rw [positive_const hy (le_of_not_ge hx), positive_eq (neg_parameter hy) (by linarith),
      reflect, neg_neg]
    ring

theorem lipschitz {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) (x z : ℝ) :
    |F x y - F z y| ≤ 18 * |x - z| := by
  rw [slice_sum hy x, slice_sum hy z]
  have he : positiveSlice y x + positiveSlice (-y) (-x) - 2 -
      (positiveSlice y z + positiveSlice (-y) (-z) - 2) =
      (positiveSlice y x - positiveSlice y z) +
        (positiveSlice (-y) (-x) - positiveSlice (-y) (-z)) := by ring
  rw [he]
  have h1 := positive_lipschitz hy x z
  have h2 := positive_lipschitz (neg_parameter hy) (-x) (-z)
  rw [neg_sub_neg, abs_sub_comm z x] at h2
  linarith [abs_add_le (positiveSlice y x - positiveSlice y z)
    (positiveSlice (-y) (-x) - positiveSlice (-y) (-z))]

theorem second_derivative {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (fun x : ℝ => -(x ^ 2)⁻¹ - 2 * x - y) (2 * x⁻¹ ^ 3 - 2) x := by
  convert ((((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx.ne')).neg).sub
    ((hasDerivAt_id x).const_mul 2)).sub_const y using 1
  field_simp
  <;> ring

theorem second_derivative_bound {x : ℝ} (hx : x ∈ Set.Icc (1 / 2) 2) :
    |2 * x⁻¹ ^ 3 - 2| ≤ 18 := by
  have hp : 0 < x := by linarith [hx.1]
  have hi : x⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hp).mpr (by linarith [hx.1])
  have hi0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hp.le
  have hi3 := pow_le_pow_left₀ hi0 hi 3
  rw [abs_le]
  constructor <;> nlinarith [pow_nonneg hi0 3]

end Cubic.AllGaloisCounts.SliceUniformBounds
