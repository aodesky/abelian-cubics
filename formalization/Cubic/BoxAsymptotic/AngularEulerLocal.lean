import Cubic.PoissonSummation.LatticeSeries
import Mathlib.Algebra.Ring.GeomSum

/-! Summing the split angular Euler factor.  A recurrence proves the formula
also when the character value is `1` or `-1`, without division by their
potentially vanishing difference.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularEulerLocal

def symmetricSum (a b : ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (n + 1), a ^ r * b ^ (n - r)

theorem symmetricSum_zero (a b : ℂ) : symmetricSum a b 0 = 1 := by
  simp [symmetricSum]

theorem symmetricSum_succ (a b : ℂ) (n : ℕ) :
    symmetricSum a b (n + 1) = a * symmetricSum a b n + b ^ (n + 1) := by
  rw [symmetricSum, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero,
    Nat.add_sub_add_right, pow_succ]
  rw [symmetricSum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem cube_recurrence (a b : ℂ) (hab : a * b = 1) (j : ℕ) :
    symmetricSum a b (3 * (j + 1)) = a ^ 3 * symmetricSum a b (3 * j) +
      (a + b + b ^ 3) * (b ^ 3) ^ j := by
  have haab : a ^ 2 * b = a := by rw [pow_two, mul_assoc, hab, mul_one]
  have habb : a * b ^ 2 = b := by rw [pow_two, ← mul_assoc, hab, one_mul]
  rw [show 3 * (j + 1) = 3 * j + 1 + 1 + 1 by omega,
    symmetricSum_succ, symmetricSum_succ, symmetricSum_succ]
  simp only [pow_add, pow_one, pow_mul]
  calc
    _ = a ^ 3 * symmetricSum a b (3 * j) +
        (a ^ 2 * b + a * b ^ 2 + b ^ 3) * b ^ (3 * j) := by ring
    _ = _ := by rw [haab, habb, pow_mul]

theorem norm_symmetricSum {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (n : ℕ) :
    ‖symmetricSum a b n‖ ≤ (n : ℝ) + 1 := by
  calc
    _ ≤ ∑ r ∈ Finset.range (n + 1), ‖a ^ r * b ^ (n - r)‖ := norm_sum_le _ _
    _ = _ := by simp [norm_pow, ha, hb]

theorem summable_cube {a b x : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hx : ‖x‖ < 1) :
    Summable (fun j => symmetricSum a b (3 * j) * x ^ j) := by
  apply Summable.of_norm
  apply (Cubic.PoissonSummation.LatticeSeries.hasSum_split_geometric ‖x‖
    (by simpa using hx)).summable.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro j
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_symmetricSum ha hb (3 * j))
    (pow_nonneg (norm_nonneg x) j)

theorem one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have he : z = 1 := (sub_eq_zero.mp h).symm
  simp [he] at hz

theorem split_hasSum {a b x : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : a * b = 1) (hx : ‖x‖ < 1) :
    HasSum (fun j => symmetricSum a b (3 * j) * x ^ j)
      ((1 + (a + b) * x) / ((1 - a ^ 3 * x) * (1 - b ^ 3 * x))) := by
  have hs := summable_cube ha hb hx
  have ha3 : ‖a ^ 3 * x‖ < 1 := by simpa [norm_mul, norm_pow, ha] using hx
  have hb3 : ‖b ^ 3 * x‖ < 1 := by simpa [norm_mul, norm_pow, hb] using hx
  set D := ∑' j, symmetricSum a b (3 * j) * x ^ j
  have ht : HasSum (fun j => symmetricSum a b (3 * (j + 1)) * x ^ (j + 1))
      (a ^ 3 * x * D + (a + b + b ^ 3) * x * (1 - b ^ 3 * x)⁻¹) := by
    convert (hs.hasSum.mul_left (a ^ 3 * x)).add
      ((hasSum_geometric_of_norm_lt_one hb3).mul_left ((a + b + b ^ 3) * x)) using 1
    funext j
    rw [cube_recurrence a b hab, pow_succ, mul_pow]
    ring
  have he := hs.hasSum.unique (ht.zero_add
    (f := fun j => symmetricSum a b (3 * j) * x ^ j))
  simp only [Nat.mul_zero, symmetricSum_zero, pow_zero, mul_one] at he
  change D = 1 + (a ^ 3 * x * D + (a + b + b ^ 3) * x * (1 - b ^ 3 * x)⁻¹) at he
  have hd : D = (1 + (a + b) * x) / ((1 - a ^ 3 * x) * (1 - b ^ 3 * x)) := by
    apply (eq_div_iff (mul_ne_zero (one_sub_ne_zero ha3) (one_sub_ne_zero hb3))).mpr
    have hb0 := one_sub_ne_zero hb3
    have he' : D - (1 + a ^ 3 * x * D) =
        ((a + b + b ^ 3) * x) / (1 - b ^ 3 * x) := by
      linear_combination he
    have hm := (eq_div_iff hb0).mp he'
    linear_combination hm
  rw [← hd]
  exact hs.hasSum

theorem correction_identity {a b x : ℂ} (hab : a * b = 1) :
    (1 + (a + b) * x) * ((1 - a * x) * (1 - b * x)) =
      1 - (a ^ 2 + 1 + b ^ 2) * x ^ 2 + (a + b) * x ^ 3 := by
  have haab : a ^ 2 * b = a := by rw [pow_two, mul_assoc, hab, mul_one]
  have habb : a * b ^ 2 = b := by rw [pow_two, ← mul_assoc, hab, one_mul]
  calc
    _ = 1 - (a ^ 2 + a * b + b ^ 2) * x ^ 2 +
        (a ^ 2 * b + a * b ^ 2) * x ^ 3 := by ring
    _ = _ := by rw [hab, haab, habb]

end Cubic.BoxAsymptotic.AngularEulerLocal
