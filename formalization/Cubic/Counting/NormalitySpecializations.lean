import Cubic.Counting.NormalityCriterion
import Cubic.OrbitParametrization.SplitAlgebra

/-! The integral trace-one specialization used in the polynomial count. -/

noncomputable section
namespace Cubic.Counting.NormalitySpecializations
open Polynomial Cubic.OrbitParametrization Cubic.OrbitParametrization.C3Algebra

theorem integral_trace_one (K : C3Alg) (x : K.carrier) (a b : ℤ)
    (hc : (LinearMap.mul ℚ K.carrier x).charpoly =
      X ^ 3 - X ^ 2 + C (a : ℚ) * X + C (b : ℚ)) : C3Algebra.IsNormal K x := by
  apply (NormalityCriterion.«lemma:normalityCriterion» K x 1 a (-b) (by simpa using hc)).mpr
  norm_num only [one_pow, one_mul]
  have h : (1 : ℤ) - 3 * a ≠ 0 := by omega
  exact_mod_cast h

theorem split_charpoly (x : ZMod 3 → ℚ) :
    (LinearMap.mul ℚ (ZMod 3 → ℚ) x).charpoly =
      X ^ 3 - C (x 0 + x 1 + x 2) * X ^ 2 +
        C (secondCoeff (x 0) (x 1) (x 2)) * X - C (x 0 * x 1 * x 2) := by
  let b := Pi.basisFun ℚ (ZMod 3)
  have hm : (LinearMap.mul ℚ (ZMod 3 → ℚ) x).toMatrix b b = Matrix.diagonal x := by
    ext i j
    simp [b, LinearMap.toMatrix_apply, Matrix.diagonal_apply, Pi.single_apply]
  rw [← (LinearMap.mul ℚ (ZMod 3 → ℚ) x).charpoly_toMatrix b, hm,
    Matrix.charpoly_diagonal]
  change (∏ i : Fin 3, (X - C (x i))) = _
  rw [Fin.prod_univ_three]
  simp only [secondCoeff, map_add, map_mul]
  ring

end Cubic.Counting.NormalitySpecializations
