import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Analysis.Calculus.MeanValue

/-! The two local trapezoidal estimates used in the paper: a cubic error
on a smooth cell and a quadratic error on a cell containing a junction. -/

namespace Cubic.AllGaloisCounts.TrapezoidalEstimate
open MeasureTheory Set

theorem smooth_cell {f f' f'' : ℝ → ℝ} {a b M : ℝ} (hab : a < b) (hM : 0 ≤ M)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hdd : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Icc a b)) (hb : ∀ x ∈ Icc a b, |f'' x| ≤ M) :
    |(b - a) / 2 * (f a + f b) - ∫ x in a..b, f x| ≤ (b - a) ^ 3 * M / 12 := by
  have he : EqOn (derivWithin f (Icc a b)) f' (Icc a b) := by
    intro x hx
    exact (hd x hx).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab x hx)
  have hd2 (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt (derivWithin f (Icc a b)) (f'' x) (Icc a b) x :=
    (hdd x hx).hasDerivWithinAt.congr (fun y hy => he hy) (he hx)
  have he2 : EqOn (iteratedDerivWithin 2 f (Icc a b)) f'' (Icc a b) := by
    intro x hx
    simpa only [iteratedDerivWithin_succ', iteratedDerivWithin_zero] using
      (hd2 x hx).derivWithin (uniqueDiffOn_Icc hab x hx)
  have hi : IntervalIntegrable (iteratedDerivWithin 2 f (Icc a b)) volume a b := by
    apply (hc.intervalIntegrable_of_Icc hab.le).congr
    intro x hx
    apply Eq.symm
    apply he2
    rw [uIoc_of_le hab.le] at hx
    exact ⟨hx.1.le, hx.2⟩
  have hbound (x : ℝ) : |iteratedDerivWithin 2 f (Icc a b) x| ≤ M := by
    by_cases hx : x ∈ Icc a b
    · rw [he2 hx]
      exact hb x hx
    · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure
        (by rwa [closure_Icc]), abs_zero]
      exact hM
  have h := trapezoidal_error_le
    (f := f) (a := a) (b := b) (ζ := M)
    (by rw [uIcc_of_lt hab]; exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (by rw [uIcc_of_lt hab]; exact fun x hx => (hd2 x hx).differentiableWithinAt)
    (by simpa only [uIcc_of_lt hab] using hi)
    (by simpa only [uIcc_of_lt hab] using hbound) (show 0 < (1 : ℕ) by decide)
  simpa only [trapezoidal_error, trapezoidal_integral_one, Nat.cast_one, one_pow, mul_one,
    abs_of_pos (sub_pos.mpr hab)] using h

theorem lipschitz_cell {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x - f y| ≤ L * |x - y|) :
    |(b - a) / 2 * (f a + f b) - ∫ x in a..b, f x| ≤ L * (b - a) ^ 2 := by
  have hi : IntervalIntegrable f volume a b := hc.intervalIntegrable_of_Icc hab
  have he : (b - a) / 2 * (f a + f b) - ∫ x in a..b, f x =
      ∫ x in a..b, (f a + f b) / 2 - f x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [he]
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : |(f a + f b) / 2 - f x| ≤ L * (b - a) := by
    have h1 := hlip a ⟨le_rfl, hab⟩ x hx
    have h2 := hlip b ⟨hab, le_rfl⟩ x hx
    rw [abs_of_nonpos (by linarith [hx.1] : a - x ≤ 0)] at h1
    rw [abs_of_nonneg (by linarith [hx.2] : 0 ≤ b - x)] at h2
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => (f a + f b) / 2 - f x) (a := a) (b := b) (C := L * (b - a)) (by
      intro x hx
      rw [Real.norm_eq_abs]
      apply hpoint
      rw [uIoc_of_le hab] at hx
      exact ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  nlinarith

end Cubic.AllGaloisCounts.TrapezoidalEstimate
