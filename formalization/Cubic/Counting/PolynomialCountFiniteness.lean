import Cubic.Counting.PolynomialCountData
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Finiteness of the polynomial count

The coefficient-height bound puts the two integer coefficients in finite
intervals. This proves finiteness for every real bound, including negative
bounds, independently of the torus correspondence or counting formulas.
-/

noncomputable section

namespace Cubic.Counting.PolynomialCountFiniteness

open Polynomial PolynomialCountData Set

theorem traceOneCubic_coeff_one (a b : ℤ) : (traceOneCubic a b).coeff 1 = a := by
  simp only [traceOneCubic, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

theorem traceOneCubic_coeff_zero (a b : ℤ) : (traceOneCubic a b).coeff 0 = b := by
  simp only [traceOneCubic, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

theorem coefficient_bounds (a b : ℤ) (H : ℝ) (h : rootHeight (traceOneCubic a b) ≤ H) :
    |(a : ℝ)| ≤ H ^ 2 ∧ |(b : ℝ)| ≤ H ^ 3 := by
  rw [rootHeight, traceOneCubic_coeff_one, traceOneCubic_coeff_zero, max_le_iff] at h
  have hH : 0 ≤ H := (Real.sqrt_nonneg _).trans h.1
  constructor
  · calc
      _ = (Real.sqrt |(a : ℝ)|) ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
      _ ≤ H ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hH).mpr h.1
  · have hp := pow_le_pow_left₀ (Real.rpow_nonneg (abs_nonneg (b : ℝ)) _) h.2 3
    have he : (|(b : ℝ)| ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = |(b : ℝ)| := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg (b : ℝ))]
      norm_num
    rwa [he] at hp

theorem boundedPolynomials_finite (H : ℝ) : (boundedPolynomials H).Finite := by
  let S : Set (ℤ × ℤ) := Icc (-⌈H ^ 2⌉) ⌈H ^ 2⌉ ×ˢ Icc (-⌈H ^ 3⌉) ⌈H ^ 3⌉
  have hS : S.Finite := (finite_Icc _ _).prod (finite_Icc _ _)
  apply (hS.image (fun ab => traceOneCubic ab.1 ab.2)).subset
  rintro f ⟨⟨⟨a, b, rfl⟩, _⟩, hh⟩
  obtain ⟨ha, hb⟩ := coefficient_bounds a b H hh
  have haI : |a| ≤ ⌈H ^ 2⌉ := by exact_mod_cast ha.trans (Int.le_ceil _)
  have hbI : |b| ≤ ⌈H ^ 3⌉ := by exact_mod_cast hb.trans (Int.le_ceil _)
  exact ⟨(a, b), ⟨abs_le.mp haI, abs_le.mp hbI⟩, rfl⟩

end Cubic.Counting.PolynomialCountFiniteness
