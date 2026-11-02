import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# The first two coefficients of a cubic multiplication characteristic polynomial

The identities `Tr(x) = e₁` and `Tr(x²) = e₁² - 2e₂` hold in every
three-dimensional rational algebra, including the split algebra. We verify
them on a rational basis, without passing to complex embedding coordinates.
-/

noncomputable section

namespace Cubic.Counting.CubicTraceCoefficients
open Polynomial Matrix

theorem charpoly_three {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    A.charpoly = X ^ 3 - C A.trace * X ^ 2 +
      C (A 0 0 * A 1 1 + A 1 1 * A 2 2 + A 2 2 * A 0 0 -
        A 0 1 * A 1 0 - A 1 2 * A 2 1 - A 2 0 * A 0 2) * X - C A.det := by
  simp [Matrix.charpoly, Matrix.det_fin_three, Matrix.trace, Fin.sum_univ_three]
  ring

theorem trace_square {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    (A * A).trace = A.trace ^ 2 -
      2 * (A 0 0 * A 1 1 + A 1 1 * A 2 2 + A 2 2 * A 0 0 -
        A 0 1 * A 1 0 - A 1 2 * A 2 1 - A 2 0 * A 0 2) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem traces {R : Type*} [CommRing R] [Algebra ℚ R] [FiniteDimensional ℚ R]
    (b : Module.Basis (Fin 3) ℚ R) (x : R) (e₁ e₂ e₃ : ℚ)
    (hc : (LinearMap.mul ℚ R x).charpoly =
      X ^ 3 - C e₁ * X ^ 2 + C e₂ * X - C e₃) :
    Algebra.trace ℚ R x = e₁ ∧ Algebra.trace ℚ R (x ^ 2) = e₁ ^ 2 - 2 * e₂ := by
  let A := Algebra.leftMulMatrix b x
  have hp : A.charpoly = X ^ 3 - C e₁ * X ^ 2 + C e₂ * X - C e₃ := by
    rw [← hc]
    exact (LinearMap.mul ℚ R x).charpoly_toMatrix b
  rw [charpoly_three] at hp
  have h1 := congrArg (fun p : ℚ[X] => p.coeff 2) hp
  have h2 := congrArg (fun p : ℚ[X] => p.coeff 1) hp
  norm_num [coeff_X_pow] at h1 h2
  constructor
  · rw [Algebra.trace_eq_matrix_trace b]
    exact h1
  · rw [Algebra.trace_eq_matrix_trace b, map_pow, pow_two, trace_square]
    rw [h1, h2]

end Cubic.Counting.CubicTraceCoefficients
