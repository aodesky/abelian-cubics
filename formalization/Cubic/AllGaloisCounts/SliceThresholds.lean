import Cubic.AllGaloisCounts.LinearFactorSlice
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The two positive level crossings of the clipped slice. They are defined
by their equations, with existence and uniqueness proved on an open interval
containing the paper's closed parameter interval. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceThresholds
open CountData LinearFactorSlice

theorem strictAnti_psi {y : ℝ} (hy : -2 < y) :
    StrictAntiOn (fun x : ℝ => psi x y) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (psi_deriv hx y).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := (interior_subset hx)
    rw [(psi_deriv hx' y).deriv]
    linarith [inverse_square_bound hx']

theorem crossing_exists {y t : ℝ} (hy : y ∈ Set.Ioo (-2) 2) (ht : t ∈ Set.Icc 0 2) :
    ∃ x : ℝ, x ∈ Set.Icc (1 / 4) 4 ∧ psi x y = t := by
  have hc : ContinuousOn (fun x : ℝ => psi x y) (Set.Icc (1 / 4) 4) := by
    intro x hx
    exact (psi_deriv (by linarith [hx.1]) y).continuousAt.continuousWithinAt
  apply intermediate_value_Icc' (by norm_num : (1 / 4 : ℝ) ≤ 4) hc
  simp only [Set.mem_Icc, psi]
  norm_num
  constructor <;> linarith [hy.1, hy.2, ht.1, ht.2]

def crossing (t y : ℝ) : ℝ :=
  if h : y ∈ Set.Ioo (-2) 2 ∧ t ∈ Set.Icc 0 2 then
    Classical.choose (crossing_exists h.1 h.2) else 1

theorem crossing_spec {y t : ℝ} (hy : y ∈ Set.Ioo (-2) 2) (ht : t ∈ Set.Icc 0 2) :
    crossing t y ∈ Set.Icc (1 / 4) 4 ∧ psi (crossing t y) y = t := by
  rw [crossing, dif_pos ⟨hy, ht⟩]
  exact Classical.choose_spec (crossing_exists hy ht)

theorem crossing_pos {y t : ℝ} (hy : y ∈ Set.Ioo (-2) 2) (ht : t ∈ Set.Icc 0 2) :
    0 < crossing t y := by linarith [(crossing_spec hy ht).1.1]

theorem crossing_unique {y t x : ℝ} (hy : y ∈ Set.Ioo (-2) 2) (ht : t ∈ Set.Icc 0 2)
    (hx : 0 < x) (he : psi x y = t) : x = crossing t y :=
  (strictAnti_psi hy.1).injOn hx (crossing_pos hy ht) (he.trans (crossing_spec hy ht).2.symm)

def minus (y : ℝ) : ℝ := crossing 2 y
def plus (y : ℝ) : ℝ := crossing 0 y

theorem theta_inverse : vartheta⁻¹ = vartheta ^ 2 - vartheta - 1 := by
  apply inv_eq_of_mul_eq_one_right
  nlinarith [vartheta_spec.2.2]

theorem theta_fourth : vartheta ^ 4 = 2 * vartheta ^ 3 - 1 := by
  linear_combination (vartheta - 1) * vartheta_spec.2.2

theorem theta_inverse_square : vartheta ^ 2 + vartheta⁻¹ ^ 2 = 2 * vartheta := by
  rw [theta_inverse]
  nlinarith [theta_fourth]

theorem theta_inverse_cube : vartheta⁻¹ ^ 3 = 2 - vartheta := by
  have hn : vartheta ≠ 0 := by linarith [vartheta_spec.1]
  apply (mul_right_inj' (pow_ne_zero 3 hn)).mp
  rw [← mul_pow, mul_inv_cancel₀ hn, one_pow]
  nlinarith [theta_fourth]

theorem endpoints : minus 1 = vartheta⁻¹ ∧ plus 1 = 1 ∧
    minus (-1) = 1 ∧ plus (-1) = vartheta := by
  have hp : 0 < vartheta := by linarith [vartheta_spec.1]
  have hne := hp.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Eq.symm
    apply crossing_unique (by norm_num) (by norm_num) (inv_pos.mpr hp)
    dsimp [psi]
    rw [inv_inv]
    nlinarith [theta_inverse, theta_inverse_square]
  · apply Eq.symm
    apply crossing_unique (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 1)
    norm_num [psi]
  · apply Eq.symm
    apply crossing_unique (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 1)
    norm_num [psi]
  · apply Eq.symm
    apply crossing_unique (by norm_num) (by norm_num) hp
    rw [psi, theta_inverse]
    ring

theorem order {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) : minus y < plus y := by
  have hy' : y ∈ Set.Ioo (-2) 2 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h0 := crossing_pos hy' (show (0 : ℝ) ∈ Set.Icc 0 2 by norm_num)
  have h2 := crossing_pos hy' (show (2 : ℝ) ∈ Set.Icc 0 2 by norm_num)
  have e0 := (crossing_spec hy' (show (0 : ℝ) ∈ Set.Icc 0 2 by norm_num)).2
  have e2 := (crossing_spec hy' (show (2 : ℝ) ∈ Set.Icc 0 2 by norm_num)).2
  by_contra hn
  have hle : plus y ≤ minus y := le_of_not_gt hn
  have h := (strictAnti_psi hy'.1).antitoneOn h0 h2 hle
  rw [e0, e2] at h
  norm_num at h

end Cubic.AllGaloisCounts.SliceThresholds
