import Cubic.SurfaceGeometry.SymmetricVeroneseRelations
import Cubic.SurfaceGeometry.ThirdVeroneseGeneration

noncomputable section

namespace Cubic.SurfaceGeometry.VeronesePresentationData

open MvPolynomial InvariantCubicData

abbrev Coefficients := MvPolynomial (Fin 4) ℤ
abbrev PresentationRing := Polynomial Coefficients

/-- B,A,h,C in the coefficient ring, and D in the polynomial variable. -/
def quadratic : PresentationRing := Polynomial.X ^ 2 -
  Polynomial.C (X 0 - 3 * X 3) * Polynomial.X +
  Polynomial.C (X 2 + X 1 * X 3 - 6 * X 0 * X 3 + 9 * X 3 ^ 2)

def symmetricRelation : PresentationRing :=
  Polynomial.C SymmetricVeroneseRelations.multivariateRelation

def relations : Ideal PresentationRing := Ideal.span {symmetricRelation, quadratic}

def coefficientEvaluation : Coefficients →ₐ[ℤ] Cubic.ToricHeights.TernaryCyclicInvariants.TernaryRing :=
  symmetricEval.comp SymmetricVeroneseRelations.substitution

def evaluation : PresentationRing →ₐ[ℤ] Cubic.ToricHeights.TernaryCyclicInvariants.TernaryRing :=
  Polynomial.eval₂AlgHom' coefficientEvaluation
    Cubic.ToricHeights.TernaryCyclicInvariants.delta (fun _ => Commute.all _ _)

end Cubic.SurfaceGeometry.VeronesePresentationData
