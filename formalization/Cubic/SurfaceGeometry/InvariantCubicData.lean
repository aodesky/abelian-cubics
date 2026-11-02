import Cubic.ToricHeights.C3Invariants
import Cubic.SurfaceGeometry.CubicData
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

noncomputable section

namespace Cubic.SurfaceGeometry.InvariantCubicData

open MvPolynomial Cubic.ToricHeights.TernaryCyclicInvariants

abbrev SymmetricCoefficients := MvPolynomial (Fin 3) ℤ

def symmetricEval : SymmetricCoefficients →ₐ[ℤ] TernaryRing :=
  aeval (fun i : Fin 3 => e (i.val + 1))

def normalForm (p : SymmetricCoefficients × SymmetricCoefficients) : TernaryRing :=
  symmetricEval p.1 + symmetricEval p.2 * delta

def relationPolynomial : Polynomial SymmetricCoefficients :=
  Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1 - 3 * X 2) * Polynomial.X +
    Polynomial.C (X 1 ^ 3 + X 0 ^ 3 * X 2 - 6 * X 0 * X 1 * X 2 + 9 * X 2 ^ 2)

def A : TernaryRing := e 1 ^ 3
def B : TernaryRing := e 1 * e 2
def C : TernaryRing := e 3
def D : TernaryRing := delta

end Cubic.SurfaceGeometry.InvariantCubicData
