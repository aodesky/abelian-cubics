import Cubic.Counting.QuadraticLDerivativeApproximation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries

/-!
# A summable bound for the corrected finite Dirichlet sums

Successive approximants cancel the constant and linear Taylor terms in the
positive real base of `x^(-s)`. Two applications of the vector-valued mean
value inequality bound the remaining increment by a second derivative.
All estimates retain the complex parameter and its real part explicitly.
-/

noncomputable section

namespace Cubic.Counting.QuadraticLIncrementBound

open Set QuadraticLDerivativeApproximation

/-- A coarse first-order Taylor bound on an interval of length five. -/
theorem remainder_bound {f f' f'' : ℝ → ℂ} {a M : ℝ} (hM : 0 ≤ M)
    (h₁ : ∀ t ∈ Icc a (a + 5), HasDerivAt f (f' t) t)
    (h₂ : ∀ t ∈ Icc a (a + 5), HasDerivAt f' (f'' t) t)
    (hb : ∀ t ∈ Icc a (a + 5), ‖f'' t‖ ≤ M)
    (y : ℝ) (hy : y ∈ Icc a (a + 5)) :
    ‖f y - f a - ((y - a : ℝ) : ℂ) * f' a‖ ≤ 25 * M := by
  have hfirst (t : ℝ) (ht : t ∈ Icc a (a + 5)) : ‖f' t - f' a‖ ≤ 5 * M := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun x hx => (h₂ x hx).hasDerivWithinAt)
      (fun x hx => hb x (Ico_subset_Icc_self hx)) t ht
    nlinarith [ht.2]
  let R : ℝ → ℂ := fun t => f t - f a - ((t - a : ℝ) : ℂ) * f' a
  have hR (t : ℝ) (ht : t ∈ Icc a (a + 5)) : HasDerivAt R (f' t - f' a) t := by
    have hl : HasDerivAt (fun x : ℝ => ((x - a : ℝ) : ℂ) * f' a) (f' a) t := by
      simpa using (((hasDerivAt_id' t).sub_const a).ofReal_comp.mul_const (f' a))
    exact ((h₁ t ht).sub_const (f a)).fun_sub hl
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hR t ht).hasDerivWithinAt)
    (fun t ht => hfirst t (Ico_subset_Icc_self ht)) y hy
  simp only [R, sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at h
  nlinarith [hy.2]

theorem power_derivative (r : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x := by
  by_cases hr : r = 0
  · subst r
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hr

theorem inverse_power_second_derivative (s : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1))
      (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
  convert (power_derivative (-s - 1) x hx).const_mul (-s) using 1
  rw [show -s - 1 - 1 = -s - 2 by ring]
  ring

theorem second_derivative_bound (s : ℂ) (x y σ B : ℝ)
    (hx : 1 ≤ x) (hxy : x ≤ y) (hσ : -1 < σ) (hs : σ ≤ s.re)
    (hB : ‖s * (s + 1)‖ ≤ B) :
    ‖s * (s + 1) * (y : ℂ) ^ (-s - 2)‖ ≤ B * x ^ (-σ - 2) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  have hre : (-s - 2).re = -s.re - 2 := by simp
  rw [hre]
  calc
    _ ≤ ‖s * (s + 1)‖ * x ^ (-s.re - 2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
    _ ≤ B * x ^ (-σ - 2) := by
      exact mul_le_mul hB (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
        (Real.rpow_nonneg hx0.le _) ((norm_nonneg _).trans hB)

/-- Exact cancellation of the low-order terms in each increment. -/
theorem approximation_increment (n : ℕ) (s : ℂ) :
    approximation (n + 1) s - approximation n s =
      (3 * ((n : ℂ) + 1) + 4) ^ (-s) - (3 * ((n : ℂ) + 1) + 5) ^ (-s) +
        ((3 * ((n : ℂ) + 1) + 3) ^ (-s) - (3 * ((n : ℂ) + 1)) ^ (-s)) / 3 := by
  simp only [approximation, show n + 1 + 2 = (n + 2) + 1 by omega,
    Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [show 3 * ((n : ℂ) + 2) + 1 = 3 * ((n : ℂ) + 1) + 4 by ring,
    show 3 * ((n : ℂ) + 2) + 2 = 3 * ((n : ℂ) + 1) + 5 by ring,
    show 3 * ((n : ℂ) + 1 + 1) = 3 * ((n : ℂ) + 1) + 3 by ring]
  ring

theorem increment_bound (n : ℕ) (s : ℂ) (σ B : ℝ) (hσ : -1 < σ)
    (hs : σ ≤ s.re) (hB : ‖s * (s + 1)‖ ≤ B) :
    ‖approximation (n + 1) s - approximation n s‖ ≤
      75 * B * ((n : ℝ) + 1) ^ (-σ - 2) := by
  let x : ℝ := 3 * ((n : ℝ) + 1)
  let M : ℝ := B * x ^ (-σ - 2)
  let f : ℝ → ℂ := fun y => (y : ℂ) ^ (-s)
  let f' : ℝ → ℂ := fun y => -s * (y : ℂ) ^ (-s - 1)
  let f'' : ℝ → ℂ := fun y => s * (s + 1) * (y : ℂ) ^ (-s - 2)
  let R : ℝ → ℂ := fun y => f y - f x - ((y - x : ℝ) : ℂ) * f' x
  have hx : 1 ≤ x := by dsimp [x]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hM : 0 ≤ M := mul_nonneg hB0 (Real.rpow_nonneg (by linarith) _)
  have hR (y : ℝ) (hy : y ∈ Icc x (x + 5)) : ‖R y‖ ≤ 25 * M := by
    exact remainder_bound hM
      (fun t ht => power_derivative (-s) t (by linarith [ht.1]))
      (fun t ht => inverse_power_second_derivative s t (by linarith [ht.1]))
      (fun t ht => second_derivative_bound s x t σ B hx ht.1 hσ hs hB) y hy
  have h4 := hR (x + 4) (by constructor <;> linarith)
  have h5 := hR (x + 5) (by constructor <;> linarith)
  have h3 := hR (x + 3) (by constructor <;> linarith)
  have he : approximation (n + 1) s - approximation n s =
      R (x + 4) - R (x + 5) + R (x + 3) / 3 := by
    rw [approximation_increment]
    dsimp [R, f, f', x]
    push_cast
    ring
  rw [he]
  have hb : ‖R (x + 4) - R (x + 5) + R (x + 3) / 3‖ ≤ 75 * M := by
    have htriangle := norm_add_le (R (x + 4) - R (x + 5)) (R (x + 3) / 3)
    have hsub := norm_sub_le (R (x + 4)) (R (x + 5))
    rw [norm_div, Complex.norm_ofNat] at htriangle
    linarith
  refine hb.trans ?_
  dsimp [M]
  have hx' : (n : ℝ) + 1 ≤ x := by dsimp [x]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hp := Real.rpow_le_rpow_of_nonpos (show 0 < (n : ℝ) + 1 by positivity)
    hx' (show -σ - 2 ≤ 0 by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hp hB0]

theorem summable_majorant (σ B : ℝ) (hσ : -1 < σ) :
    Summable (fun n : ℕ => 75 * B * ((n : ℝ) + 1) ^ (-σ - 2)) := by
  have h := (Real.summable_nat_rpow.mpr (show -σ - 2 < -1 by linarith))
  have ht := (summable_nat_add_iff 1).mpr h
  simpa only [Nat.cast_add, Nat.cast_one] using ht.mul_left (75 * B)

end Cubic.Counting.QuadraticLIncrementBound
