import Cubic.PoissonSummation.PoissonIntegral
import Cubic.PoissonSummation.HeightZetaCompletion

/-!
# `thm:heightZetaFunctionFormula2`: the original height-series Euler formula

Apply the actual adelic Poisson lemma. The assembly then closes the upper
contour and evaluates its residue, cancels the dual scalar six against the
finite factor `1/6`, extracts the convergent Euler products, uses the rational
product formula to reach the full parameter region, and supplies meromorphic
continuation by the genuine Dirichlet L-function and correction products.
The only explicit assumption is the general Poisson summation input
`PoissonWithDualMeasure.BlackBox`.
The concrete full target has not been weakened or made conditional itself.
-/

namespace Cubic.PoissonSummation

/-- Every assertion of the full paper theorem for the original height series,
relative only to the assumed general harmonic-analysis input. -/
theorem «thm:heightZetaFunctionFormula2»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.PoissonSummation.HeightZetaFunctionFormula.Claim :=
  HeightZetaCompletion.claim_of_poisson («lemma:poissonIntegral» hPoisson)

end Cubic.PoissonSummation
