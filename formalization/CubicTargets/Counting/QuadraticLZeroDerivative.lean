import Cubic.Counting.AsymptoticConstantsData

/-!
# The derivative at zero in the Gamma evaluation

The value of `L'(0, χ₋₃)` used in the Gamma evaluation of the Euler–Kronecker
constant in `thm:asymptoticPolynomialCount`. The L-function is mathlib's analytic
continuation for the quadratic character modulo three. The identity is proved by
`Cubic.Counting.QuadraticLApproximationIdentification.zero_derivative`.
-/

namespace CubicTargets.Counting.QuadraticLZeroDerivative

open Cubic.PoissonSummation

def Claim : Prop := deriv (DirichletCharacter.LFunction QuadraticDirichletCharacter.character) 0 =
  -(Real.log 3 : ℂ) / 3 +
    (Real.log (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)) : ℂ)

end CubicTargets.Counting.QuadraticLZeroDerivative
