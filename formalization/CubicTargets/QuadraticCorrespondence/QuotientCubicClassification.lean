import Cubic.QuadraticCorrespondence.DescendedCoefficients

/-!
# Algebraic classification of the quotient cubics

This is the classification clause of `prop:cyclotomicParametrization`, and supplies
the split/cyclic case division used in the paper's proof of `lemma:rootVsToric`. Its
proof is `Cubic.QuadraticCorrespondence.QuotientCubicClassification.claim`.
-/

namespace CubicTargets.QuadraticCorrespondence.QuotientCubicClassification

open Cubic.QuadraticCorrespondence

def Claim : Prop := ∀ P : CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ,
  CorrespondencePolynomials.Admissible (DescendedCoefficients.characteristicPolynomial P)

end CubicTargets.QuadraticCorrespondence.QuotientCubicClassification
