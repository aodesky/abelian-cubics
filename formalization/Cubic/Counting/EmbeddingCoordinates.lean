import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! Complex embedding coordinates for a three-dimensional rational algebra.
These helpers are retained from the earlier normality proof. The current
`lemma:normalityCriterion` instead uses the rational trace Gram matrix. -/

noncomputable section

namespace Cubic.Counting.EmbeddingCoordinates
open Module Matrix
variable {M : Type*} [CommRing M] [Algebra ℚ M]
  (b : Basis (Fin 3) ℚ M) (φ : Fin 3 → M →ₐ[ℚ] ℂ)

def evaluation : (M →ₗ[ℚ] ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun f i := f (b i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_injective : Function.Injective (evaluation b) := by
  intro f g h
  exact b.ext (fun i => congrFun h i)

def matrix : Matrix (Fin 3) (Fin 3) ℂ := fun i j => φ i (b j)

theorem matrix_det_ne_zero (hφ : Function.Injective φ) : (matrix b φ).det ≠ 0 := by
  have h := ((linearIndependent_algHom_toLinearMap ℚ M ℂ).comp φ hφ).map'
    (evaluation b) (LinearMap.ker_eq_bot.mpr (evaluation_injective b))
  change LinearIndependent ℂ (matrix b φ).row at h
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp h))

theorem matrix_mul_coordinates (v : Fin 3 → M) :
    matrix b φ * (b.toMatrix v).map (algebraMap ℚ ℂ) =
      (fun i j => φ i (v j) : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  have h := congrArg (φ i) (b.sum_repr (v j))
  simp only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes] at h
  simpa only [Matrix.mul_apply, matrix, Matrix.map_apply, Basis.toMatrix_apply,
    mul_comm] using h

include b in
theorem linearIndependent_iff_det (hφ : Function.Injective φ) (v : Fin 3 → M) :
    LinearIndependent ℚ v ↔ Matrix.det (fun i j => φ i (v j) : Matrix (Fin 3) (Fin 3) ℂ) ≠ 0 := by
  have he : LinearIndependent ℚ v ↔ LinearIndependent ℚ (b.toMatrix v).col := by
    exact (b.equivFun.toLinearMap.linearIndependent_iff
      (LinearMap.ker_eq_bot.mpr b.equivFun.injective)).symm
  rw [he, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, ← matrix_mul_coordinates b φ v, Matrix.det_mul, mul_ne_zero_iff]
  have hd : ((b.toMatrix v).map (algebraMap ℚ ℂ)).det =
      algebraMap ℚ ℂ (b.toMatrix v).det := (algebraMap ℚ ℂ).map_det _ |>.symm
  rw [hd]
  simp only [map_ne_zero_iff _ (algebraMap ℚ ℂ).injective]
  exact ⟨fun h => ⟨matrix_det_ne_zero b φ hφ, h⟩, And.right⟩

variable [FiniteDimensional ℚ M]

include b in
theorem charpoly (hφ : Function.Injective φ) (x : M) :
    (LinearMap.mul ℚ M x).charpoly.map (algebraMap ℚ ℂ) =
      ∏ i : Fin 3, (Polynomial.X - Polynomial.C (φ i x)) := by
  let A := (LinearMap.mul ℚ M x).toMatrix b b
  have hm : matrix b φ * A.map (algebraMap ℚ ℂ) =
      Matrix.diagonal (fun i => φ i x) * matrix b φ := by
    have hA : A = b.toMatrix (fun j => x * b j) := by
      ext i j
      simp [A, LinearMap.toMatrix_apply, Basis.toMatrix_apply]
    rw [hA, matrix_mul_coordinates]
    ext i j
    simp only [Matrix.diagonal_mul, matrix, map_mul]
  have hu : IsUnit (matrix b φ) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (matrix_det_ne_zero b φ hφ))
  obtain ⟨U, hU⟩ := hu
  have hc : (U : Matrix (Fin 3) (Fin 3) ℂ) * A.map (algebraMap ℚ ℂ) *
      (↑(U⁻¹) : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.diagonal (fun i => φ i x) := by
    rw [hU, hm, ← hU, mul_assoc]
    simp
  rw [← Matrix.charpoly_diagonal, ← hc, Matrix.charpoly_units_conj,
    Matrix.charpoly_map]
  exact congrArg (Polynomial.map (algebraMap ℚ ℂ)) ((LinearMap.mul ℚ M x).charpoly_toMatrix b).symm

end Cubic.Counting.EmbeddingCoordinates
