import CubicTargets.QuadraticCorrespondence.CyclotomicParametrization
import Cubic.QuadraticCorrespondence.RationalCoefficientFormula

/-!
# `eqn:integralityConditionsUsingCyclo`

In `prop:cyclotomicParametrization`: for the element `u + vζ ∈ ℚ(√−3)^×` of a rational
point, the characteristic polynomial `f` has integral coefficients iff
`u² + v² − uv ∈ 1 + 3ℤ` and `(u² + v² − uv)(3 − 2u + v) ∈ 1 + 27ℤ`.

The element of a rational point is `RationalCoefficientFormula.parameterEquiv p`, the
rational map of the proposition's specified isomorphism
(`CyclotomicParametrization.rationalEquiv_specified`). `normForm u v = u² + v² − uv` and `traceForm u v = 2u − v` are the norm and trace
of `u + vζ`.
-/

namespace CubicTargets.QuadraticCorrespondence.IntegralityConditions

open CubicTargets.QuadraticCorrespondence.CyclotomicParametrization
open Cubic.QuadraticCorrespondence CyclotomicField CyclotomicCoefficients CorrespondencePolynomials

def Claim : Prop :=
  ∀ (p : Points ℚ) (u v : ℚ),
    (RationalCoefficientFormula.parameterEquiv p : E) = algebraMap ℚ E u + algebraMap ℚ E v * zeta →
    (HasIntegralCoefficients (characteristicPolynomial p) ↔
      (∃ m : ℤ, normForm u v = 1 + 3 * (m : ℚ)) ∧
      (∃ n : ℤ, normForm u v * (3 - traceForm u v) = 1 + 27 * (n : ℚ)))

end CubicTargets.QuadraticCorrespondence.IntegralityConditions
