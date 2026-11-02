import Cubic.SurfaceGeometry.CubicPresentationData
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace Cubic.SurfaceGeometry.AffineModelData

open MvPolynomial CubicPresentationData

abbrev AffinePolynomial (R : Type*) [CommRing R] := MvPolynomial (Fin 3) R

def equation (R : Type*) [CommRing R] : AffinePolynomial R :=
  CubicData.affineRelation (X 0) (X 1) (X 2)

abbrev CoordinateRing (R : Type*) [CommRing R] :=
  AffinePolynomial R ⧸ Ideal.span {equation R}

def coordinate (R : Type*) [CommRing R] (i : Fin 3) : CoordinateRing R :=
  Ideal.Quotient.mk _ (X i)

/-- The A=1 representative of the standard projective chart D₊(A). -/
def normalizedChartIdeal : Ideal CubicRing := Ideal.span {cubic, X 0 - 1}

def dehomogenize : CubicRing →ₐ[ℤ] AffinePolynomial ℤ :=
  aeval ![1, X 0, -X 1, X 2]

def homogenizeCoordinates : AffinePolynomial ℤ →ₐ[ℤ] CubicRing :=
  aeval ![X 1, -X 2, X 3]

/-- Evaluation at the original trace-one invariant functions. -/
def invariantEvaluation : AffinePolynomial ℤ →ₐ[ℤ]
    Cubic.ToricHeights.AffineInvariantRing.ChartRing :=
  aeval ![Cubic.ToricHeights.AffineChartInvariants.e2,
    -Cubic.ToricHeights.AffineChartInvariants.e3,
    Cubic.ToricHeights.AffineChartInvariants.delta]

def Singular (k : Type*) [Field k] (x : Fin 4 → k) : Prop :=
  x ≠ 0 ∧ CubicData.F (x 0) (x 1) (x 2) (x 3) = 0 ∧
    ∀ i : Fin 4, eval x (pderiv i
      (CubicData.F (X 0) (X 1) (X 2) (X 3) : MvPolynomial (Fin 4) k)) = 0

end Cubic.SurfaceGeometry.AffineModelData
