import Cubic.OrbitParametrization.C3AlgebraBasic
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! The current normality criterion for an arbitrary element of a `C₃`-algebra.
The characteristic polynomial is that of multiplication by the element. -/

namespace CubicTargets.Counting.NormalityCriterion
open Polynomial Cubic.OrbitParametrization.C3Algebra

def Claim : Prop := ∀ (K : C3Alg) (x : K.carrier) (e₁ e₂ e₃ : ℚ),
  (LinearMap.mul ℚ K.carrier x).charpoly = X ^ 3 - C e₁ * X ^ 2 + C e₂ * X - C e₃ →
    (IsNormal K x ↔ e₁ * (e₁ ^ 2 - 3 * e₂) ≠ 0)

end CubicTargets.Counting.NormalityCriterion
