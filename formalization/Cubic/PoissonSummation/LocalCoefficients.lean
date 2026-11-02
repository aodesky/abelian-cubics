import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Prime-power coefficient calculations

The finite divisor sums in the proof of `thm:heightZetaFunctionFormula`, and the
elementary split-prime bound in `eqn:dSummatoryForGeneralTrace`.

For a split prime, `3^ω(p^j)` is `1` at `j = 0` and `3` otherwise. For an inert
prime, the weight is `(-1)^j`. The connection to global arithmetic functions is
proved in `CoefficientArithmetic`. The connection to height zeta coefficients is open.
-/

namespace Cubic.PoissonSummation

open Finset

/-- The exponent-level divisor weight at a split prime. -/
def splitDivisorWeight (j : ℕ) : ℕ := if j = 0 then 1 else 3

/-- Summing the split weights over divisors of `p^k` gives `3k + 1`. -/
theorem sum_splitDivisorWeight (k : ℕ) :
    ∑ j ∈ range (k + 1), splitDivisorWeight j = 3 * k + 1 := by
  induction k with
  | zero => simp [splitDivisorWeight]
  | succ k ih =>
    rw [sum_range_succ, ih]
    simp [splitDivisorWeight]
    omega

/-- An even number of alternating weights cancels in pairs. -/
theorem sum_inert_weights_even_length (k : ℕ) :
    ∑ j ∈ range (2 * k), (-1 : ℤ) ^ j = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, ih]
    simp [pow_succ, pow_mul]

/-- At an even exponent the inert coefficient is one. -/
theorem sum_inert_weights_even_exponent (k : ℕ) :
    ∑ j ∈ range (2 * k + 1), (-1 : ℤ) ^ j = 1 := by
  rw [sum_range_succ, sum_inert_weights_even_length]
  simp [pow_mul]

/-- At an odd exponent the inert coefficient is zero. -/
theorem sum_inert_weights_odd_exponent (k : ℕ) :
    ∑ j ∈ range (2 * k + 1 + 1), (-1 : ℤ) ^ j = 0 := by
  convert sum_inert_weights_even_length (k + 1) using 1

/-- The split local coefficient bound used in `eqn:dSummatoryForGeneralTrace`. -/
theorem split_coefficient_le_divisor_cube (k : ℕ) :
    3 * k + 1 ≤ (k + 1) ^ 3 := by
  nlinarith [Nat.zero_le (k ^ 3)]

end Cubic.PoissonSummation
