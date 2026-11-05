import Cubic.Counting.PolynomialCountData
import Mathlib.Analysis.MeanInequalities

/-!
# The AM–GM estimate in `lemma:rootVsToric`

The paper writes `a = -A` with `A ≥ 0`, compares coefficients in
`f = (t - r₁)(t - r₂)(t - r₃)` to get `r₁² + r₂² + r₃² = 1 + 2A` and
`r₁r₂r₃ = -b`, and applies AM–GM to the `rᵢ²`:
`b² ≤ ((1 + 2A)/3)³`. If `A ≥ 1` then `1 + 2A ≤ 3A`, so `|b|^{2/3} ≤ A`;
if `A = 0` then `b² ≤ 1/27`, so `b = 0`. Either way the root height is `√A`.
-/

noncomputable section

namespace Cubic.ToricHeights.RootHeightAMGM

open Cubic.Counting.PolynomialCountData

/-- AM–GM for the three nonnegative numbers `x², y², z²`, cubed. -/
theorem sq_prod_le (x y z : ℝ) :
    (x * y * z) ^ 2 ≤ ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ^ 3 := by
  have h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3)
    (by norm_num) (by norm_num) (by norm_num)
    (sq_nonneg x) (sq_nonneg y) (sq_nonneg z) (by norm_num)
  have hl : 0 ≤ (x ^ 2) ^ (1 / 3 : ℝ) * (y ^ 2) ^ (1 / 3 : ℝ) * (z ^ 2) ^ (1 / 3 : ℝ) := by
    positivity
  have hc := pow_le_pow_left₀ hl h 3
  have hcube : ∀ p : ℝ, 0 ≤ p → (p ^ (1 / 3 : ℝ)) ^ 3 = p := fun p hp => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp]
    norm_num
  rw [mul_pow, mul_pow, hcube _ (sq_nonneg x), hcube _ (sq_nonneg y),
    hcube _ (sq_nonneg z)] at hc
  calc (x * y * z) ^ 2 = x ^ 2 * y ^ 2 * z ^ 2 := by ring
    _ ≤ _ := hc
    _ = _ := by ring

/-- Comparing coefficients and applying AM–GM: `b² ≤ ((1 + 2A)/3)³` with `A = -a`. -/
theorem constant_sq_le (a b x y z : ℝ) (h₁ : x + y + z = 1)
    (h₂ : x * y + x * z + y * z = a) (h₃ : x * y * z = -b) :
    b ^ 2 ≤ ((1 + 2 * -a) / 3) ^ 3 := by
  have hsq : x ^ 2 + y ^ 2 + z ^ 2 = 1 + 2 * -a := by
    have : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (x * y + x * z + y * z) := by ring
    rw [this, h₁, h₂]
    ring
  have h := sq_prod_le x y z
  rw [h₃, hsq] at h
  simpa only [neg_sq] using h

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

/-- The case `A ≥ 1`: `1 + 2A ≤ 3A`, so `b² ≤ A³`, i.e. `|b| ≤ A√A`. -/
theorem abs_le_of_large (A b : ℝ) (hA : 1 ≤ A) (hb : b ^ 2 ≤ ((1 + 2 * A) / 3) ^ 3) :
    |b| ≤ A * Real.sqrt A := by
  have hA0 : 0 ≤ A := by linarith
  have hle : (1 + 2 * A) / 3 ≤ A := by linarith
  have hcube : ((1 + 2 * A) / 3) ^ 3 ≤ A ^ 3 :=
    pow_le_pow_left₀ (by positivity) hle 3
  have hsq : (A * Real.sqrt A) ^ 2 = A ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hA0]
    ring
  exact abs_le_of_sq_le_sq (by rw [hsq]; linarith) (by positivity)

/-- The case `A = 0`: `b² ≤ 1/27` forces the integer `b` to vanish. -/
theorem zero_constant (b : ℤ) (hb : (b : ℝ) ^ 2 ≤ ((1 + 2 * -(0 : ℝ)) / 3) ^ 3) : b = 0 := by
  have h : (b : ℝ) ^ 2 < 1 := by norm_num at hb; linarith
  have h' : b ^ 2 < 1 := by exact_mod_cast h
  nlinarith [sq_nonneg b]

/-- The root height of `t³ - t² + at + b` is `√(-a)` under the AM–GM bound. -/
theorem rootHeight_eq_sqrt (a b : ℤ) (ha : a ≤ 0)
    (hb : (b : ℝ) ^ 2 ≤ ((1 + 2 * -(a : ℝ)) / 3) ^ 3) :
    rootHeight (traceOneCubic a b) = Real.sqrt (-(a : ℝ)) := by
  have haR : (a : ℝ) ≤ 0 := by exact_mod_cast ha
  have hcr : |(b : ℝ)| ^ (1 / 3 : ℝ) ≤ Real.sqrt (-(a : ℝ)) := by
    by_cases ha0 : a = 0
    · subst a
      have hb0 : b = 0 := zero_constant b (by simpa using hb)
      simp [hb0]
    · have hA : (1 : ℝ) ≤ -(a : ℝ) := by
        exact_mod_cast (show (1 : ℤ) ≤ -a by omega)
      exact cube_root_le_sqrt _ _ (by linarith) (abs_le_of_large _ _ hA hb)
  have hc₁ : (traceOneCubic a b).coeff 1 = a := by
    simp only [traceOneCubic, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    norm_num
  have hc₀ : (traceOneCubic a b).coeff 0 = b := by
    simp only [traceOneCubic, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    norm_num
  rw [rootHeight, hc₁, hc₀, abs_of_nonpos haR, max_eq_left hcr]

end Cubic.ToricHeights.RootHeightAMGM
