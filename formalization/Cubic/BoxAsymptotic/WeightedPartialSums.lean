import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.Complex.Basic

/-! Abel summation with a uniform bound on the unweighted initial sums.
This is the step that permits approximate-functional-equation weights to vary
with the frequency. The derivative integral records their total variation. -/

noncomputable section

namespace Cubic.BoxAsymptotic.WeightedPartialSums

open MeasureTheory Finset

theorem integral_bound (c : ℕ → ℂ) {w : ℝ → ℂ} {a b M : ℝ}
    (ha : 0 ≤ a)
    (hw : IntegrableOn (deriv w) (Set.Icc a b))
    (hM : ∀ q : ℕ, q ≤ ⌊b⌋₊ → ‖∑ n ∈ Icc 0 q, c n‖ ≤ M) :
    ‖∫ x in Set.Ioc a b, deriv w x * ∑ n ∈ Icc 0 ⌊x⌋₊, c n‖ ≤
      M * ∫ x in Set.Ioc a b, ‖deriv w x‖ := by
  have hprod := (integrableOn_mul_sum_Icc c (m := 0) ha hw).mono_set Set.Ioc_subset_Icc_self
  have hder : IntegrableOn (fun x => ‖deriv w x‖) (Set.Ioc a b) :=
    (hw.mono_set Set.Ioc_subset_Icc_self).norm
  calc
    _ ≤ ∫ x in Set.Ioc a b, ‖deriv w x * ∑ n ∈ Icc 0 ⌊x⌋₊, c n‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Ioc a b, M * ‖deriv w x‖ := by
      apply setIntegral_mono_on hprod.norm (hder.const_mul M) measurableSet_Ioc
      intro x hx
      rw [norm_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM _ (Nat.floor_le_floor hx.2)) (norm_nonneg _)
    _ = _ := integral_const_mul M _

theorem interval_bound (c : ℕ → ℂ) {w : ℝ → ℂ} {a b M : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hwd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ w x)
    (hwi : IntegrableOn (deriv w) (Set.Icc a b))
    (hM : ∀ q : ℕ, q ≤ ⌊b⌋₊ → ‖∑ n ∈ Icc 0 q, c n‖ ≤ M) :
    ‖∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, w n * c n‖ ≤
      M * (‖w b‖ + ‖w a‖ + ∫ x in Set.Ioc a b, ‖deriv w x‖) := by
  rw [sum_mul_eq_sub_sub_integral_mul c ha hab hwd hwi]
  have h₁ := norm_sub_le (w b * ∑ n ∈ Icc 0 ⌊b⌋₊, c n)
    (w a * ∑ n ∈ Icc 0 ⌊a⌋₊, c n)
  have h₂ := norm_sub_le (w b * ∑ n ∈ Icc 0 ⌊b⌋₊, c n -
      w a * ∑ n ∈ Icc 0 ⌊a⌋₊, c n)
    (∫ x in Set.Ioc a b, deriv w x * ∑ n ∈ Icc 0 ⌊x⌋₊, c n)
  have h₃ := integral_bound c ha hwi hM
  have h₄ := mul_le_mul_of_nonneg_left (hM ⌊b⌋₊ le_rfl) (norm_nonneg (w b))
  have h₅ := mul_le_mul_of_nonneg_left (hM ⌊a⌋₊ (Nat.floor_le_floor hab)) (norm_nonneg (w a))
  simp only [norm_mul] at h₁
  nlinarith

theorem initial_bound (c : ℕ → ℂ) (hc : c 0 = 0) {w : ℝ → ℂ} {b M : ℝ}
    (hwd : ∀ x ∈ Set.Icc 1 b, DifferentiableAt ℝ w x)
    (hwi : IntegrableOn (deriv w) (Set.Icc 1 b))
    (hM : ∀ q : ℕ, q ≤ ⌊b⌋₊ → ‖∑ n ∈ Icc 0 q, c n‖ ≤ M) :
    ‖∑ n ∈ Icc 0 ⌊b⌋₊, w n * c n‖ ≤
      M * (‖w b‖ + ∫ x in Set.Ioc 1 b, ‖deriv w x‖) := by
  rw [sum_mul_eq_sub_integral_mul₀ c hc b hwd hwi]
  have h₁ := norm_sub_le (w b * ∑ n ∈ Icc 0 ⌊b⌋₊, c n)
    (∫ x in Set.Ioc 1 b, deriv w x * ∑ n ∈ Icc 0 ⌊x⌋₊, c n)
  have h₂ := integral_bound c zero_le_one hwi hM
  have h₃ := mul_le_mul_of_nonneg_left (hM ⌊b⌋₊ le_rfl) (norm_nonneg (w b))
  simp only [norm_mul] at h₁
  nlinarith

end Cubic.BoxAsymptotic.WeightedPartialSums
