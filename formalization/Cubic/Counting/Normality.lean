import Cubic.Counting.NormalityDeterminant
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Integral trace-one elements are normal

This file proves `lemma:integralTraceOneImpliesNormal`. The determinant
calculation `eqn:normalityDeterminant` has its own proof file,
`Cubic.Counting.NormalityDeterminant`. The integer obstruction is kept separate
from the linear algebra. The real determinant criterion is also used in the
proof of `lemma:cubicimpliesnormal` (`CubicImpliesNormal`).
-/

namespace Cubic.Counting

open Cubic.OrbitParametrization

/-- Non-normality implies vanishing of the determinant polynomial. -/
theorem conjugates_det_eq_zero_of_not_normal (α β γ : ℚ) (h : ¬ IsNormal α β γ) :
    (conjugates α β γ).det = 3 * α * β * γ - α ^ 3 - β ^ 3 - γ ^ 3 ∧
      3 * α * β * γ - α ^ 3 - β ^ 3 - γ ^ 3 = 0 := by
  refine ⟨conjugates_det α β γ, ?_⟩
  rw [← conjugates_det]
  exact Matrix.det_eq_zero_of_not_linearIndependent_rows h

/-- On the trace-one hyperplane, the determinant is `3a - 1`. -/
theorem conjugates_det_of_trace_one {R : Type*} [CommRing R] (α β γ : R)
    (htrace : α + β + γ = 1) :
    (conjugates α β γ).det = 3 * secondCoeff α β γ - 1 := by
  rw [conjugates_det]
  unfold secondCoeff
  calc
    _ = 3 * (α * β + β * γ + γ * α) * (α + β + γ) - (α + β + γ) ^ 3 := by ring
    _ = _ := by rw [htrace]; ring

/-- The sum-of-squares identity specialized to trace one. -/
theorem conjugates_det_sum_sq_of_trace_one {K : Type*} [Field K] [CharZero K]
    (α β γ : K) (htrace : α + β + γ = 1) :
    (conjugates α β γ).det =
      -(1 / 2) * ((α - β) ^ 2 + (β - γ) ^ 2 + (γ - α) ^ 2) := by
  rw [(conjugates_det_sum_squares α β γ).2.2, htrace, neg_div]

/-- The real determinant is strictly negative if the first two coordinates differ. -/
theorem conjugates_det_neg_of_trace_one (α β γ : ℝ) (htrace : α + β + γ = 1)
    (hne : α ≠ β) : (conjugates α β γ).det < 0 := by
  rw [conjugates_det_sum_sq_of_trace_one α β γ htrace]
  have hpos : 0 < (α - β) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  nlinarith [sq_nonneg (β - γ), sq_nonneg (γ - α)]

/-- The real linear-algebra ingredient in `lemma:cubicimpliesnormal`. -/
theorem linearIndependent_conjugates_of_trace_one (α β γ : ℝ)
    (htrace : α + β + γ = 1) (hne : α ≠ β) :
    LinearIndependent ℝ (conjugates α β γ) := by
  exact Matrix.linearIndependent_rows_of_det_ne_zero
    (ne_of_lt (conjugates_det_neg_of_trace_one α β γ htrace hne))

/-- The integer determinant cannot vanish, since it is `-1` modulo three. -/
theorem conjugates_det_ne_zero (α β γ : ℤ) (htrace : α + β + γ = 1) :
    (conjugates α β γ).det ≠ 0 := by
  rw [conjugates_det_of_trace_one α β γ htrace]
  omega

/-- The same obstruction after embedding the coordinates in `ℚ`. -/
theorem conjugates_det_rat_ne_zero (α β γ : ℤ) (htrace : α + β + γ = 1) :
    (conjugates (α : ℚ) (β : ℚ) (γ : ℚ)).det ≠ 0 := by
  have htraceQ : (α : ℚ) + β + γ = 1 := by exact_mod_cast htrace
  rw [conjugates_det_of_trace_one (α : ℚ) β γ htraceQ]
  have h := conjugates_det_ne_zero α β γ htrace
  rw [conjugates_det_of_trace_one α β γ htrace] at h
  unfold secondCoeff at *
  exact_mod_cast h

/-- `lemma:integralTraceOneImpliesNormal`: the three cyclic conjugates form
a linearly independent family in the split algebra `ℚ³`. -/
theorem «lemma:integralTraceOneImpliesNormal» (α β γ : ℤ)
    (htrace : α + β + γ = 1) : IsNormal (α : ℚ) β γ := by
  exact Matrix.linearIndependent_rows_of_det_ne_zero
    (conjugates_det_rat_ne_zero α β γ htrace)

end Cubic.Counting
