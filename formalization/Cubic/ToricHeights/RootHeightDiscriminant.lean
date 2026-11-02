import Cubic.Counting.PolynomialCountData
import Mathlib.Algebra.CubicDiscriminant

/-!
# The discriminant estimate in `lemma:rootVsToric`

This follows the paper's square completion, with `A * sqrt A` in place of
`A^(3/2)`. The integer zero case is treated separately. The conclusion uses the
coefficient height, including its real cube-root exponent.
-/

noncomputable section

namespace Cubic.ToricHeights.RootHeightDiscriminant

open Cubic.Counting.PolynomialCountData

theorem discriminant_formula (a b : ℝ) :
    (⟨1, -1, a, b⟩ : Cubic ℝ).discr = a ^ 2 - 4 * a ^ 3 + (4 - 18 * a) * b - 27 * b ^ 2 := by
  simp only [Cubic.discr]
  ring

/-- Completing the square and comparing with `A^(3/2)`, exactly as in the paper. -/
theorem constant_bound (A b : ℝ) (hA : 1 ≤ A)
    (hd : 27 * b ^ 2 - (18 * A + 4) * b ≤ A ^ 2 + 4 * A ^ 3) :
    |b| ≤ A * Real.sqrt A := by
  have hA0 : 0 ≤ A := by linarith
  have hs : 1 ≤ Real.sqrt A := by
    have := Real.sq_sqrt hA0
    nlinarith [Real.sqrt_nonneg A]
  have ht0 : 0 ≤ 1 + 3 * A := by positivity
  have ht : Real.sqrt (1 + 3 * A) ≤ 2 * Real.sqrt A := by
    nlinarith [Real.sq_sqrt hA0, Real.sq_sqrt ht0,
      Real.sqrt_nonneg (1 + 3 * A)]
  have hsquare : (54 * b - (18 * A + 4)) ^ 2 ≤
      (4 * (1 + 3 * A) * Real.sqrt (1 + 3 * A)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht0]
    nlinarith [hd]
  have hab := abs_le_of_sq_le_sq hsquare (by positivity)
  have htriangle : 54 * |b| ≤ |54 * b - (18 * A + 4)| + (18 * A + 4) := by
    calc
      _ = |54 * b| := by rw [abs_mul]; norm_num
      _ = |(54 * b - (18 * A + 4)) + (18 * A + 4)| := by ring_nf
      _ ≤ |54 * b - (18 * A + 4)| + |18 * A + 4| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg (show 0 ≤ 18 * A + 4 by positivity)]
  have hlarge : 4 * (1 + 3 * A) * Real.sqrt (1 + 3 * A) ≤ 32 * A * Real.sqrt A := by
    have h := mul_le_mul (show 1 + 3 * A ≤ 4 * A by linarith) ht
      (Real.sqrt_nonneg _) (by positivity : 0 ≤ 4 * A)
    nlinarith
  have hlinear : 18 * A + 4 ≤ 22 * A * Real.sqrt A := by
    have := mul_le_mul_of_nonneg_left hs hA0
    nlinarith
  linarith

theorem zero_constant (b : ℤ) (hd : 0 ≤ (4 : ℝ) * b - 27 * (b : ℝ) ^ 2) : b = 0 := by
  have hb0 : (0 : ℝ) ≤ b := by nlinarith [sq_nonneg (b : ℝ)]
  have hb1 : (b : ℝ) < 1 := by nlinarith
  have : 0 ≤ b ∧ b < 1 := by exact_mod_cast And.intro hb0 hb1
  omega

theorem cube_root_le_sqrt (A b : ℝ) (hA : 0 ≤ A) (hb : |b| ≤ A * Real.sqrt A) :
    |b| ^ (1 / 3 : ℝ) ≤ Real.sqrt A := by
  have hp : A * Real.sqrt A = (Real.sqrt A) ^ 3 := by
    rw [pow_succ, Real.sq_sqrt hA]
  rw [hp] at hb
  have h := Real.rpow_le_rpow (abs_nonneg b) hb (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have he : ((Real.sqrt A) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = Real.sqrt A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.sqrt_nonneg A)]
    norm_num
  exact h.trans_eq he

theorem rootHeight_eq_sqrt (a b : ℤ) (ha : a ≤ 0)
    (hd : 0 ≤ (a : ℝ) ^ 2 - 4 * (a : ℝ) ^ 3 +
      (4 - 18 * (a : ℝ)) * b - 27 * (b : ℝ) ^ 2) :
    rootHeight (traceOneCubic a b) = Real.sqrt (-(a : ℝ)) := by
  have haR : (a : ℝ) ≤ 0 := by exact_mod_cast ha
  have hb : |(b : ℝ)| ^ (1 / 3 : ℝ) ≤ Real.sqrt (-(a : ℝ)) := by
    by_cases ha0 : a = 0
    · subst a
      have hb0 : b = 0 := zero_constant b (by simpa using hd)
      simp [hb0]
    · have hA : (1 : ℝ) ≤ -(a : ℝ) := by
        have : a ≤ -1 := by omega
        exact_mod_cast (show (1 : ℤ) ≤ -a by omega)
      apply cube_root_le_sqrt _ _ (by linarith)
      apply constant_bound _ _ hA
      nlinarith [hd]
  have hc₁ : (traceOneCubic a b).coeff 1 = a := by
    simp only [traceOneCubic, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    norm_num
  have hc₀ : (traceOneCubic a b).coeff 0 = b := by
    simp only [traceOneCubic, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    norm_num
  rw [rootHeight, hc₁, hc₀, abs_of_nonpos haR, max_eq_left hb]

end Cubic.ToricHeights.RootHeightDiscriminant
