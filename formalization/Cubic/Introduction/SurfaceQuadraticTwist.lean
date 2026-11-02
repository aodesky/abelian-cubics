import CubicTargets.Introduction.SurfaceQuadraticTwist
import Cubic.SurfaceGeometry.RationalFormSplitting

noncomputable section

namespace Cubic.Introduction.SurfaceQuadraticTwist

open Cubic.SurfaceGeometry RationalFormData QuadraticTwistData CubicData
attribute [-instance] DivisionRing.toRatAlgebra

theorem root_square (d : ℚ) : root d ^ 2 = algebraMap ℚ (Extension d) d := by
  ext <;> simp [root, pow_two, QuadraticAlgebra.omega]

theorem root_ne_zero (d : ℚ) : root d ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simp [root] at this

theorem root_conjugation (d : ℚ) : conjugation d (root d) = -root d := by
  ext <;> simp [conjugation, root]

/-- The coordinate change is linear, so it descends to projective coordinates. -/
def splitLinearEquiv {k : Type*} [Field k] [CharZero k] (r : k) (hr : r ≠ 0) :
    (Fin 4 → k) ≃ₗ[k] (Fin 4 → k) where
  toFun := splitChange r
  invFun := inverseSplitChange r
  left_inv := RationalFormSplitting.split_inverse r hr
  right_inv := RationalFormSplitting.inverse_split r hr
  map_add' x y := by ext i; fin_cases i <;> simp [splitChange] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [splitChange] <;> ring

theorem splitting_equation {k : Type*} [Field k] (d r : k) (hr : r ^ 2 = d)
    (x : Fin 4 → k) :
    splitCubic (splitChange r x) = twistCubic d x := by
  simp only [splitCubic, splitChange, twistCubic, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination -(x 0 * x 2 ^ 2) * hr

theorem conjugation_swap (d : ℚ) [Fact (¬ IsSquare d)] (x : Fin 4 → Extension d) :
    (fun i => conjugation d (splitChange (root d) x i)) =
      swapCoordinates (splitChange (root d) (fun i => conjugation d (x i))) := by
  funext i
  fin_cases i <;> simp [splitChange, swapCoordinates, root_conjugation] <;> ring

theorem «eqn:surfaceQuadraticTwist» : CubicTargets.Introduction.SurfaceQuadraticTwist.Claim := by
  intro d hd
  letI := hd
  refine ⟨QuadraticAlgebra.finrank_eq_two d 0, root_square d, root_conjugation d,
    ⟨splitLinearEquiv (root d) (root_ne_zero d), fun _ => rfl, fun _ => rfl⟩,
    splitting_equation _ _ (root_square d), conjugation_swap d, ?_⟩
  intro x
  simp [splitCubic, swapCoordinates]
  ring

end Cubic.Introduction.SurfaceQuadraticTwist
