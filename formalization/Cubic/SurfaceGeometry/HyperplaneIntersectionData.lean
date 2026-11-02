import Cubic.SurfaceGeometry.CubicData
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Span

/-! The generic line in the Grassmannian chart where projection to [B:C]
is an isomorphism: A=a₀C+a₁B and D=d₀C+d₁B. Its intersection with
the actual cubic on C=1 is a univariate quotient over the parameter field. -/

noncomputable section

namespace Cubic.SurfaceGeometry.HyperplaneIntersectionData

abbrev Parameters := MvPolynomial (Fin 4) ℚ
abbrev ParameterField := FractionRing Parameters

def parameter (i : Fin 4) : ParameterField := algebraMap Parameters _ (MvPolynomial.X i)

def sectionPolynomial : Polynomial ParameterField :=
  CubicData.F
    (Polynomial.C (parameter 0) + Polynomial.C (parameter 1) * Polynomial.X)
    Polynomial.X 1
    (Polynomial.C (parameter 2) + Polynomial.C (parameter 3) * Polynomial.X)

def infinityValue : ParameterField := CubicData.F (parameter 1) 1 0 (parameter 3)

abbrev IntersectionRing :=
  Polynomial ParameterField ⧸ Ideal.span {sectionPolynomial}

end Cubic.SurfaceGeometry.HyperplaneIntersectionData
