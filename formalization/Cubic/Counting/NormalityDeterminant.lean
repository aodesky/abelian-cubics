import Cubic.OrbitParametrization.TraceOne

/-!
# The determinant identity `eqn:normalityDeterminant`

This file contains the complete proof of the labelled determinant identity.
Its polynomial identities also support the separate integral trace-one normality
proof in `Cubic.Counting.Normality`.
-/

namespace Cubic.Counting

open Cubic.OrbitParametrization

/-- The determinant of the conjugate evaluation matrix is the negative of `Δ`. -/
theorem conjugates_det {R : Type*} [CommRing R] (α β γ : R) :
    (conjugates α β γ).det = 3 * α * β * γ - α ^ 3 - β ^ 3 - γ ^ 3 := by
  simp [conjugates, Matrix.det_fin_three]
  ring

/-- Factorization of the conjugate evaluation determinant. -/
theorem conjugates_det_factor {R : Type*} [CommRing R] (α β γ : R) :
    (conjugates α β γ).det =
      -(α + β + γ) * (α ^ 2 + β ^ 2 + γ ^ 2 - secondCoeff α β γ) := by
  rw [conjugates_det]
  unfold secondCoeff
  ring

/-- The earlier sum-of-squares form of the conjugate evaluation determinant. -/
theorem conjugates_det_sum_squares {K : Type*} [Field K] [CharZero K]
    (α β γ : K) :
    (conjugates α β γ).det = 3 * α * β * γ - α ^ 3 - β ^ 3 - γ ^ 3 ∧
    (conjugates α β γ).det =
      -(α + β + γ) * (α ^ 2 + β ^ 2 + γ ^ 2 - secondCoeff α β γ) ∧
    (conjugates α β γ).det =
      -(α + β + γ) / 2 * ((α - β) ^ 2 + (β - γ) ^ 2 + (γ - α) ^ 2) := by
  refine ⟨conjugates_det α β γ, conjugates_det_factor α β γ, ?_⟩
  rw [conjugates_det_factor]
  unfold secondCoeff
  ring

/-- Section 2's formula for the determinant of multiplication in the group algebra. -/
theorem groupAlgebraMulMatrix_det {R : Type*} [CommRing R] (α β γ : R) :
    (groupAlgebraMulMatrix α β γ).det = α ^ 3 + β ^ 3 + γ ^ 3 - 3 * α * β * γ := by
  simp [groupAlgebraMulMatrix, Matrix.det_fin_three]
  ring

/-- The sign relating the embedding matrix to the paper's multiplication determinant. -/
theorem conjugates_det_eq_neg_groupAlgebraMulMatrix_det
    {R : Type*} [CommRing R] (α β γ : R) :
    (conjugates α β γ).det = -(groupAlgebraMulMatrix α β γ).det := by
  rw [conjugates_det, groupAlgebraMulMatrix_det]
  ring

/-- `eqn:normalityDeterminant`: the multiplication determinant is `e₁(e₁² - 3e₂)`. -/
theorem «eqn:normalityDeterminant» {R : Type*} [CommRing R] (α β γ : R) :
    (groupAlgebraMulMatrix α β γ).det =
      (α + β + γ) * ((α + β + γ) ^ 2 - 3 * secondCoeff α β γ) := by
  rw [groupAlgebraMulMatrix_det]
  unfold secondCoeff
  ring

end Cubic.Counting
