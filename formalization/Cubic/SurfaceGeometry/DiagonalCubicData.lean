import Cubic.SurfaceGeometry.RationalFormData
import Cubic.ToricHeights.TraceOneCharacters
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Div

noncomputable section

namespace Cubic.SurfaceGeometry.DiagonalCubicData

open MvPolynomial Cubic.QuadraticCorrespondence.CyclotomicField

def linearForms (x : Fin 3 → E) : Fin 3 → E :=
  ![x 0+x 1+x 2, x 0+zeta*x 1+zeta^2*x 2, x 0+zeta^2*x 1+zeta*x 2]

def inverseLinearForms (u : Fin 3 → E) : Fin 3 → E :=
  ![(u 0+u 1+u 2)/3, (u 0+zeta^2*u 1+zeta*u 2)/3,
    (u 0+zeta*u 1+zeta^2*u 2)/3]

def originalCubics (x : Fin 3 → E) : Fin 4 → E :=
  ![(x 0+x 1+x 2)^3, (x 0+x 1+x 2)*(x 0*x 1+x 0*x 2+x 1*x 2),
    x 0*x 1*x 2, x 0^2*x 1+x 1^2*x 2+x 2^2*x 0]

def diagonalCubics (u : Fin 3 → E) : Fin 4 → E :=
  ![u 0^3,u 1^3,u 2^3,u 0*u 1*u 2]

abbrev Ternary := MvPolynomial (Fin 3) E
abbrev FourVariables := MvPolynomial (Fin 4) E

/-- Variable order t,a,b,c, with t mapped to ℓ₀ℓ₁ℓ₂. -/
def substitution : FourVariables →ₐ[E] Ternary :=
  aeval ![X 0*X 1*X 2,X 0^3,X 1^3,X 2^3]

def substituteExponent (d : Fin 4 →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![3*d 1+d 0,3*d 2+d 0,3*d 3+d 0]

def relation : Polynomial Ternary := Polynomial.X^3-Polynomial.C (X 0*X 1*X 2)
def multivariateRelation : FourVariables := X 0^3-X 1*X 2*X 3
def coefficientSubstitution : Ternary →ₐ[E] Ternary := aeval ![X 0^3,X 1^3,X 2^3]
def polynomialSubstitution : Polynomial Ternary →ₐ[E] Ternary :=
  Polynomial.eval₂AlgHom' coefficientSubstitution (X 0*X 1*X 2) (fun _ => Commute.all _ _)

end Cubic.SurfaceGeometry.DiagonalCubicData
