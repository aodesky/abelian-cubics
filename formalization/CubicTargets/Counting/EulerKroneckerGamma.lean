import Cubic.Counting.EulerKroneckerCalculation

/-!
# The Gamma evaluation of the Euler–Kronecker constant

A step of `thm:asymptoticPolynomialCount`, proved by
`Cubic.Counting.EulerKroneckerGamma.evaluation`.
Its left side is the constant characterized by the continuation of the Dedekind
zeta function of `ℚ(√-3)`.
-/

namespace CubicTargets.Counting.EulerKroneckerGamma

def Claim : Prop := Cubic.Counting.EulerKroneckerCalculation.value =
  (Cubic.Counting.AsymptoticConstantsData.classicalEulerKronecker : ℂ)

end CubicTargets.Counting.EulerKroneckerGamma
