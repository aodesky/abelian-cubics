import CubicTargets.QuadraticCorrespondence.CyclotomicParametrization
import CubicTargets.ToricHeights.CanonicalHeight
import Cubic.QuadraticCorrespondence.RationalCoefficientFormula

/-!
# Concrete target for `prop:cyclotomicParametrization`

The schema `CyclotomicParametrization.Claim D` is parameterized by the geometric data `D`:
the `D₀`-integral rational locus and the toric height. Here both are fixed. The locus
is `AffineInvariantRing.IntegralPoint`, where every regular function of the integral
affine chart is integer-valued. The height is the adelic height `H(P, D₀)` at the
diagonal point, the object of `prop:canonicalHeight`. It is real at integral points
(`prop:canonicalHeight`), so its real part is recorded.

The identification of rational points of `T` with the pairs `(K/ℚ, x)` in the paper's
wording is `thm:modularInterpretation`. It is proved separately and is compatible with
`characteristicPolynomial`.
-/

namespace CubicTargets.QuadraticCorrespondence.CyclotomicParametrizationConcrete

open CubicTargets.QuadraticCorrespondence.CyclotomicParametrization
open Cubic.PoissonSummation Cubic.QuadraticCorrespondence

/-- The canonical geometric data. -/
noncomputable def canonicalGeometry : Geometry where
  integralLocus := {p | Cubic.ToricHeights.AffineInvariantRing.IntegralPoint p}
  height p := (AdelicHeightZetaData.height 1 0 (RationalAdelicEmbedding.diagonal p)).re

/-- The paper: "The elements `u + vζ` corresponding to `f` will be the roots of `g`." The
schema records that each such element is a root of `g`; this clause records the converse,
that every root of `g` in `E` is the element of a point with characteristic polynomial `f`. -/
def QuadraticRoots : Prop :=
  ∀ a b : ℚ, CorrespondencePolynomials.Admissible (CorrespondencePolynomials.cubic a b) →
    ∀ β : Cubic.QuadraticCorrespondence.CyclotomicField.E,
      Polynomial.eval β ((CorrespondencePolynomials.inverseQuadratic a b).map
        (algebraMap ℚ Cubic.QuadraticCorrespondence.CyclotomicField.E)) = 0 →
      ∃ p : Points ℚ, characteristicPolynomial p = CorrespondencePolynomials.cubic a b ∧
        (Cubic.QuadraticCorrespondence.RationalCoefficientFormula.parameterEquiv p :
          Cubic.QuadraticCorrespondence.CyclotomicField.E) = β

def Claim : Prop := CyclotomicParametrization.Claim canonicalGeometry ∧ QuadraticRoots

end CubicTargets.QuadraticCorrespondence.CyclotomicParametrizationConcrete
