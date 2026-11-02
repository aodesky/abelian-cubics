import Cubic.QuadraticCorrespondence.IsoCocharLattices
import Cubic.ToricHeights.SupportFunction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Data.Fin.VecNotation

/-! The smooth subdivision in the appendix, in the basis `(ω,γω)`.
Intersection numbers are computed from neighboring primitive fan rays.
The Picard space is the divisor space modulo actual character divisors.
The divisor polytope uses its defining inequalities, independently of any
nefness, degree or bigness assertion. -/

namespace Cubic.SurfaceGeometry.ResolutionData

def rays : Fin 9 → ℤ × ℤ :=
  fun i => match i.val with
  | 0 => (-1,-1) | 1 => (0,-1) | 2 => (1,-1) | 3 => (2,-1)
  | 4 => (1,0) | 5 => (0,1) | 6 => (-1,2) | 7 => (-1,1) | _ => (-1,0)

def next (i : Fin 9) : Fin 9 := ⟨(i.val + 1) % 9, Nat.mod_lt _ (by decide)⟩
def prev (i : Fin 9) : Fin 9 := ⟨(i.val + 8) % 9, Nat.mod_lt _ (by decide)⟩

def det (v w : ℤ × ℤ) : ℤ := v.1 * w.2 - v.2 * w.1

def detReal (v w : ℝ × ℝ) : ℝ := v.1 * w.2 - v.2 * w.1
def realRay (i : Fin 9) : ℝ × ℝ := ((rays i).1, (rays i).2)

def Complete : Prop := ∀ v : ℝ × ℝ, ∃ i : Fin 9,
  0 ≤ detReal (realRay i) v ∧ 0 ≤ detReal v (realRay (next i))

def ambientRay (i : Fin 9) : ℚ × ℚ :=
  ((2 * (rays i).1 + (rays i).2 : ℚ) / 3,
    ((rays i).1 + 2 * (rays i).2 : ℚ) / 3)

def selfIntersection (i : Fin 9) : ℤ := -det (rays (prev i)) (rays (next i))

abbrev Divisor := Fin 9 → ℤ

def curveIntersection (D : Divisor) (i : Fin 9) : ℤ :=
  D i * selfIntersection i + D (prev i) + D (next i)

def intersection (D E : Divisor) : ℤ := ∑ i, E i * curveIntersection D i

def antiK : Divisor := fun _ => 1
def canonical : Divisor := fun i => -antiK i
def boundary : Divisor := fun i => if i.val ≤ 2 ∨ 7 ≤ i.val then 1 else 0
def pullbackThreeD0 : Divisor := fun i =>
  max 0 (max (-(rays i).1 - 2 * (rays i).2) (-2 * (rays i).1 - (rays i).2))
def logDivisor : Divisor := fun i => antiK i - boundary i

def boundaryOrder : Fin 5 → Fin 9 := ![7,8,0,1,2]

def intersectionMatrix (i j : Fin 9) : ℤ :=
  if i = j then selfIntersection i else if j = prev i ∨ j = next i then 1 else 0

def ampleDivisor : Divisor := fun i => if i.val % 3 = 0 then 3 else 2

/-- Nefness is tested on the generating invariant curves of the complete toric surface. -/
def Nef (D : Divisor) : Prop := ∀ i, 0 ≤ curveIntersection D i

def polytope (D : Divisor) : Set (ℝ × ℝ) :=
  {m | ∀ i, -(D i : ℝ) ≤ m.1 * (rays i).1 + m.2 * (rays i).2}

/-- A toric divisor is big when its polytope has nonempty interior. -/
def Big (D : Divisor) : Prop := (interior (polytope D)).Nonempty

def principal : (ℚ × ℚ) →ₗ[ℚ] (Fin 9 → ℚ) where
  toFun m i := m.1 * (rays i).1 + m.2 * (rays i).2
  map_add' m n := by ext i; dsimp; ring
  map_smul' c m := by ext i; dsimp; ring

abbrev Picard := (Fin 9 → ℚ) ⧸ principal.range

end Cubic.SurfaceGeometry.ResolutionData
