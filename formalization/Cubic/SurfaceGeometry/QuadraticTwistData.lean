import Cubic.SurfaceGeometry.RationalFormData
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! The quadratic field, its conjugation, and the equation of the twist
by interchange of the two split coordinates. -/

noncomputable section

namespace Cubic.SurfaceGeometry.QuadraticTwistData

attribute [local instance] Classical.propDecidable
attribute [-instance] DivisionRing.toRatAlgebra

abbrev Extension (d : ℚ) := QuadraticAlgebra ℚ d 0

instance noRoot (d : ℚ) [h : Fact (¬ IsSquare d)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ d + 0 * r) :=
  ⟨fun r hr => h.out ⟨r, by simpa [pow_two] using hr.symm⟩⟩

def root (d : ℚ) : Extension d := QuadraticAlgebra.omega

def conjugation (d : ℚ) : Extension d ≃ₐ[ℚ] Extension d where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := star_add
  map_mul' x y := by rw [star_mul, mul_comm]
  commutes' q := by ext <;> simp

def twistCubic {R : Type*} [CommRing R] (d : R) (x : Fin 4 → R) : R :=
  x 0 * (x 1 ^ 2 - d * x 2 ^ 2) - x 3 ^ 3

def swapCoordinates {R : Type*} (x : Fin 4 → R) : Fin 4 → R :=
  ![x 0, x 2, x 1, x 3]

end Cubic.SurfaceGeometry.QuadraticTwistData
