import Cubic.SurfaceGeometry.CubicData
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! The two homogeneous cubic coordinate rings over ℤ[1/6], with the
paper's linear substitutions. Coefficients are expressed using 1/6 so
that no field structure or extra invertibility assumption is needed. -/

noncomputable section

namespace Cubic.SurfaceGeometry.LocalizedCubicData

open MvPolynomial

abbrev Base := Localization.Away (6 : ℤ)
instance : CommRing Base := inferInstance
def invSix : Base := IsLocalization.Away.invSelf (6 : ℤ)
abbrev Ambient := MvPolynomial (Fin 4) Base

def originalEquation : Ambient := CubicData.F (X 0) (X 1) (X 2) (X 3)
def normEquation : Ambient := CubicData.normCubic (fun i => X i)
abbrev OriginalCubicRing := Ambient ⧸ Ideal.span {originalEquation}
abbrev NormCubicRing := Ambient ⧸ Ideal.span {normEquation}

def coordinateForms : Fin 4 → Ambient :=
  ![X 0, X 0 - C (27 * invSix) * X 1 + C (81 * invSix) * X 2,
    3 * X 3 - C (9 * invSix) * X 1 + C (27 * invSix) * X 2, X 0 - 3 * X 1]

def inverseForms : Fin 4 → Ambient :=
  ![X 0, C (2 * invSix) * (X 0 - X 3),
    C (8 * invSix ^ 3) * (2 * X 1 + X 0 - 3 * X 3),
    C (4 * invSix ^ 2) * (3 * X 2 + X 0 - X 1)]

def normToOriginal : Ambient →ₐ[Base] Ambient := aeval coordinateForms
def originalToNorm : Ambient →ₐ[Base] Ambient := aeval inverseForms

end Cubic.SurfaceGeometry.LocalizedCubicData
