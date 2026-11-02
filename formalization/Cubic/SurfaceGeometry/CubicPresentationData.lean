import Cubic.SurfaceGeometry.VeronesePresentationData
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

namespace Cubic.SurfaceGeometry.CubicPresentationData

open MvPolynomial InvariantCubicData VeronesePresentationData

abbrev CubicRing := MvPolynomial (Fin 4) ℤ

def cubic : CubicRing := CubicData.F (X 0) (X 1) (X 2) (X 3)

def cubicEvaluation : CubicRing →ₐ[ℤ] Cubic.ToricHeights.TernaryCyclicInvariants.TernaryRing :=
  aeval ![A, B, InvariantCubicData.C, D]

def embed : CubicRing →ₐ[ℤ] PresentationRing :=
  aeval ![Polynomial.C (X 1), Polynomial.C (X 0), Polynomial.C (X 3), Polynomial.X]

def hExpression : CubicRing := -X 3 ^ 2 + (X 1 - 3 * X 2) * X 3 -
  X 0 * X 2 + 6 * X 1 * X 2 - 9 * X 2 ^ 2

def eliminateCoefficients : Coefficients →ₐ[ℤ] CubicRing :=
  aeval ![X 1, X 0, hExpression, X 2]

def eliminate : PresentationRing →ₐ[ℤ] CubicRing :=
  Polynomial.eval₂AlgHom' eliminateCoefficients (X 3) (fun _ => Commute.all _ _)

end Cubic.SurfaceGeometry.CubicPresentationData
