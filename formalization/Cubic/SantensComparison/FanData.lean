import Cubic.SurfaceGeometry.ResolutionData
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The lattices in the Santens appendix are computed from the already constructed
resolution fan. In particular, none of the Picard groups is defined by its claimed
rank or by a chosen isomorphic free module. -/

namespace Cubic.SantensComparison.FanData

open Cubic.SurfaceGeometry.ResolutionData

def conjugateRay : Fin 9 → Fin 9 := ![0,8,7,6,5,4,3,2,1]
def orbitIndex : Fin 9 → Fin 5 := ![0,1,2,3,4,4,3,2,1]
def orbitRepresentative (i : Fin 5) : Fin 9 := ⟨i.val, by omega⟩

/-- The four rays retained in `U`, in the order `v₁,v₂,e₁,e₂`. -/
def openRay : Fin 4 → Fin 9 := ![3,6,4,5]
def openConjugation : Fin 4 → Fin 4 := ![1,0,3,2]

def pairing (m : ℤ × ℤ) (i : Fin 9) : ℤ :=
  m.1 * (rays i).1 + m.2 * (rays i).2

def openPrincipal : (ℤ × ℤ) →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun m i := pairing m (openRay i)
  map_add' m n := by ext i; simp [pairing]; ring
  map_smul' c m := by ext i; simp [pairing]; ring

abbrev OpenPicard := (Fin 4 → ℤ) ⧸ openPrincipal.range

def openProjection : (Fin 4 → ℤ) →ₗ[ℤ] (ℤ × ℤ) where
  toFun d := (d 0 - 2 * d 2 + d 3, d 1 + d 2 - 2 * d 3)
  map_add' d e := by ext <;> simp <;> ring
  map_smul' c d := by ext <;> simp <;> ring

def conjugateOpenDivisor (d : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => d (openConjugation i)

/-- Invariant characters are integral multiples of the norm character `(1,1)`. -/
def invariantPrincipal : ℚ →ₗ[ℚ] (Fin 5 → ℚ) where
  toFun a i := a * ((rays (orbitRepresentative i)).1 +
    (rays (orbitRepresentative i)).2 : ℚ)
  map_add' a b := by ext i; dsimp; ring
  map_smul' a b := by ext i; dsimp; ring

abbrev ArithmeticPicard := (Fin 5 → ℚ) ⧸ invariantPrincipal.range

/-- Retaining the real face adds `v₀` to the four rays of `U`; its orbit
divisors are `D₀′,R,H′`. The map is the actual norm-character divisor. -/
def adelicRay : Fin 3 → Fin 9 := ![0,3,4]

def adelicPrincipal : ℤ →ₗ[ℤ] (Fin 3 → ℤ) where
  toFun a i := pairing (a,a) (adelicRay i)
  map_add' a b := by ext i; simp [pairing]; ring
  map_smul' a b := by ext i; simp [pairing]; ring

abbrev AdelicPicard := (Fin 3 → ℤ) ⧸ adelicPrincipal.range

def adelicProjection : (Fin 3 → ℤ) →ₗ[ℤ] (ℤ × ℤ) where
  toFun d := (d 0 + 2 * d 2, d 1 - d 2)
  map_add' d e := by ext <;> simp <;> ring
  map_smul' c d := by ext <;> simp <;> ring

def BoundaryFace (A : Finset (Fin 9)) : Prop :=
  (∀ i ∈ A, boundary i = 1) ∧ ∃ j, A ⊆ {j, next j}

def StableFace (A : Finset (Fin 9)) : Prop :=
  BoundaryFace A ∧ ∀ i, i ∈ A ↔ conjugateRay i ∈ A

def normCharacter : ℤ × ℤ := (1,1)

/-- The effective cone uses the images of the two retained orbit divisors.
The projection comes from the integral divisor quotient above. -/
def effectiveCone : Set (ℝ × ℝ) :=
  {d | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    d = a • (((adelicProjection ![0,1,0]).1 : ℝ),
          ((adelicProjection ![0,1,0]).2 : ℝ)) +
        b • (((adelicProjection ![0,0,1]).1 : ℝ),
          ((adelicProjection ![0,0,1]).2 : ℝ))}

def dualCone : Set (ℝ × ℝ) :=
  {z | ∀ d ∈ effectiveCone, 0 ≤ z.1 * d.1 + z.2 * d.2}

/-- Lebesgue measure in coordinates dual to the integral basis `D₀′,R`. -/
noncomputable def theta : ℝ :=
  ∫ z : ℝ × ℝ in dualCone, Real.exp (-z.1)

end Cubic.SantensComparison.FanData
