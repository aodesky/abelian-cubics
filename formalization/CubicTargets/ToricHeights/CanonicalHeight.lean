import Cubic.ToricHeights.AffineInvariantRing
import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.QuadraticCorrespondence.CorrespondencePolynomials

/-!
# `prop:canonicalHeight`

Rational points of `T` are the rational points of the actual descended quotient
ring. `D₀`-integrality is the paper's definition: every regular function of the
integral affine chart is integer-valued (`AffineInvariantRing.IntegralPoint`).
The toric height is the independently defined adelic height of the divisor
`D₀`, i.e. parameters `(s₀,σ)=(1,0)`, at the diagonal point. Neither conclusion
is assumed in these definitions.
-/

namespace CubicTargets.ToricHeights.CanonicalHeight

open Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open Cubic.QuadraticCorrespondence.DescendedCoefficients
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open Cubic.ToricHeights Cubic.PoissonSummation

def Claim : Prop :=
  (∀ P : quotientFixedRing →ₐ[ℚ] ℚ,
    HasIntegralCoefficients (characteristicPolynomial P) ↔ AffineInvariantRing.IntegralPoint P) ∧
  (∀ P : quotientFixedRing →ₐ[ℚ] ℚ, AffineInvariantRing.IntegralPoint P →
    AdelicHeightZetaData.height 1 0 (RationalAdelicEmbedding.diagonal P) =
      (Real.sqrt (1 - 3 * (P linearCoefficient : ℝ)) : ℂ))

end CubicTargets.ToricHeights.CanonicalHeight
