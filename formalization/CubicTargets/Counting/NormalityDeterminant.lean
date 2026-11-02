import Cubic.OrbitParametrization.TraceOne

/-! # Target for `eqn:normalityDeterminant`

The determinant of multiplication by `x + yσ + zσ²` is `e₁(e₁² - 3e₂)`.
The identity holds over every commutative ring, including split cubic algebras.
`secondCoeff x y z = xy + yz + zx`. -/

namespace CubicTargets.Counting.NormalityDeterminant

open Cubic.OrbitParametrization

def Claim : Prop := ∀ {R : Type} [CommRing R] (α β γ : R),
  (groupAlgebraMulMatrix α β γ).det =
    (α + β + γ) * ((α + β + γ) ^ 2 - 3 * secondCoeff α β γ)

end CubicTargets.Counting.NormalityDeterminant
