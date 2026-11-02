import Cubic.SurfaceGeometry.CubicData
import Cubic.SurfaceGeometry.ResolutionData
import Cubic.QuadraticCorrespondence.CyclotomicRestrictionScalars
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section

namespace Cubic.SurfaceGeometry.RationalFormData

open MvPolynomial Cubic.QuadraticCorrespondence.CyclotomicField
open scoped TensorProduct

def splitChange {k : Type*} [Field k] (r : k) (x : Fin 4 → k) : Fin 4 → k :=
  ![x 0, x 1 + r * x 2, x 1 - r * x 2, x 3]

def inverseSplitChange {k : Type*} [Field k] (r : k) (x : Fin 4 → k) : Fin 4 → k :=
  ![x 0, (x 1 + x 2) / 2, (x 1 - x 2) / (2 * r), x 3]

def SplitSingular (k : Type*) [Field k] (x : Fin 4 → k) : Prop :=
  x ≠ 0 ∧ CubicData.splitCubic x = 0 ∧
    ∀ i : Fin 4, eval x (pderiv i
      (CubicData.splitCubic (fun j => X j) : MvPolynomial (Fin 4) k)) = 0

def NormSingular (k : Type*) [Field k] (x : Fin 4 → k) : Prop :=
  x ≠ 0 ∧ CubicData.normCubic x = 0 ∧
    ∀ i : Fin 4, eval x (pderiv i
      (CubicData.normCubic (fun j => X j) : MvPolynomial (Fin 4) k)) = 0

def normVertex {k : Type*} [Field k] (r : k) : Fin 3 → (Fin 4 → k) :=
  ![![1,0,0,0], ![0,r,1,0], ![0,-r,1,0]]

def singularVector : Fin 3 → (Fin 4 → E) := normVertex sqrtNegThree

def splitVertex {k : Type*} [Field k] (i : Fin 3) (j : Fin 4) : k :=
  if j.val = i.val then 1 else 0

/-- The original three primitive rays, in the paper's (ω,γω) basis. -/
def originalRay (i : Fin 3) : ℤ × ℤ := ResolutionData.rays ⟨3 * i.val, by omega⟩

def principal : (ℚ × ℚ) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun m i := m.1 * (originalRay i).1 + m.2 * (originalRay i).2
  map_add' m n := by ext i; dsimp; ring
  map_smul' c m := by ext i; dsimp; ring

abbrev Picard := (Fin 3 → ℚ) ⧸ principal.range

/-- The actual x₃=1 chart of the norm cubic, over any rational algebra. -/
def TorusChart (R : Type*) [CommRing R] :=
  {x : Fin 3 → R // x 0 * (x 1 ^ 2 + 3 * x 2 ^ 2) = 1}

def quadraticElement {R : Type*} [CommRing R] [Algebra ℚ R] (a b : R) : E ⊗[ℚ] R :=
  (1 : E) ⊗ₜ[ℚ] a + sqrtNegThree ⊗ₜ[ℚ] b

/-- Multiplication of norm coordinates, obtained by multiplying a+b√−3. -/
def torusProduct {R : Type*} [CommRing R] (x y : Fin 3 → R) : Fin 3 → R :=
  ![x 0 * y 0, x 1 * y 1 - 3 * x 2 * y 2, x 1 * y 2 + x 2 * y 1]

/-- The coordinate chart centered at the i-th coordinate vertex. -/
def vertexChart {k : Type*} [Field k] (i : Fin 3) (u : Fin 3 → k) : Fin 4 → k :=
  ![![1,u 0,u 1,u 2], ![u 0,1,u 1,u 2], ![u 0,u 1,1,u 2]] i

def vertexCoordinates {k : Type*} [Field k] (i : Fin 3) (x : Fin 4 → k) : Fin 3 → k :=
  ![![x 1,x 2,x 3], ![x 0,x 2,x 3], ![x 0,x 1,x 3]] i

abbrev Ambient := MvPolynomial (Fin 4) ℚ

def rationalEquation : Ambient := CubicData.F (X 0) (X 1) (X 2) (X 3)
def normEquation : Ambient := CubicData.normCubic (fun i => X i)
abbrev RationalCubicRing := Ambient ⧸ Ideal.span {rationalEquation}
abbrev NormCubicRing := Ambient ⧸ Ideal.span {normEquation}

def coordinateForms : Fin 4 → Ambient :=
  ![X 0, X 0 - C (9 / 2) * X 1 + C (27 / 2) * X 2,
    3 * X 3 - C (3 / 2) * X 1 + C (9 / 2) * X 2, X 0 - 3 * X 1]

def inverseForms : Fin 4 → Ambient :=
  ![X 0, C (1 / 3) * (X 0 - X 3), C (1 / 27) * (2 * X 1 + X 0 - 3 * X 3),
    C (1 / 9) * (3 * X 2 + X 0 - X 1)]

def normToOriginal : Ambient →ₐ[ℚ] Ambient := aeval coordinateForms
def originalToNorm : Ambient →ₐ[ℚ] Ambient := aeval inverseForms

end Cubic.SurfaceGeometry.RationalFormData
