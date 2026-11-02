import Cubic.QuadraticCorrespondence.CharacterLattice
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.FinCases

/-!
# Character divisors and the invariant divisor parameter

The primitive boundary rays are represented in the enlarged
cocharacter lattice. Pairing with the original character pullback gives the
boundary orders; the norm character `(1,1)` has orders `(-2,1,1)`.

Invariant boundary divisors are pairs `(s₀,σ)` representing `(s₀,σ,σ)`.
We compute their quotient by invariant character divisors, over either `ℚ`
or `ℂ`. The normalized class coordinate is `s₀+2σ`: it sends `D₀` to one
and the anticanonical boundary sum to three.

This is an explicit character-divisor class calculation; it does not define
a scheme Picard group. `Cubic.PoissonSummation.HeightDivisorNormalization`
verifies descent and this normalization for the adelic height.
-/

noncomputable section

namespace Cubic.ToricHeights.DivisorParameters

open Cubic.QuadraticCorrespondence
open Cubic.OrbitParametrization.CocharacterLattice

/-- Boundary rays in the integral `(v₁,ω)` coordinates of the original lattice. -/
def ray (i : Fin 3) : ℤ × ℤ :=
  if i = 0 then (1, -3) else if i = 1 then (1, 0) else (-2, 3)

theorem ray_coordinates (i : Fin 3) : coordinates (ray i) =
    if i = 0 then (-1, -1) else if i = 1 then (1, 0) else (0, 1) := by
  fin_cases i <;> norm_num [ray, coordinates]

/-- Orders along the three rays obtained by the original character/cocharacter pairing. -/
def boundaryOrders (m : ℤ × ℤ) (i : Fin 3) : ℚ :=
  ((CharacterLattice.pullback m).1 : ℚ) * (coordinates (ray i)).1 +
    ((CharacterLattice.pullback m).2 : ℚ) * (coordinates (ray i)).2

theorem norm_character_orders (i : Fin 3) :
    boundaryOrders (1, 1) i = if i = 0 then -2 else 1 := by
  fin_cases i <;> norm_num [boundaryOrders, ray_coordinates, CharacterLattice.pullback]

theorem invariant_character_orders (k : ℤ) (i : Fin 3) :
    boundaryOrders (k, k) i = (k : ℚ) * boundaryOrders (1, 1) i := by
  fin_cases i <;> simp [boundaryOrders, ray_coordinates, CharacterLattice.pullback] <;> ring

variable (K : Type*) [Field K]

/-- The invariant divisor coefficients on the three boundary components. -/
def coefficients (d : K × K) (i : Fin 3) : K := if i = 0 then d.1 else d.2

/-- Invariant character divisors, with the sign of `div χ = -2D₀+D₁+D₂`. -/
def principal : K →ₗ[K] K × K where
  toFun a := (-2 * a, a)
  map_add' a b := by ext <;> simp [mul_add]
  map_smul' a b := by ext <;> simp [mul_left_comm]

def principalSubmodule : Submodule K (K × K) := (principal K).range

abbrev Class := (K × K) ⧸ principalSubmodule K

def classOf : (K × K) →ₗ[K] Class K := (principalSubmodule K).mkQ

def degree : (K × K) →ₗ[K] K where
  toFun d := d.1 + 2 * d.2
  map_add' d e := by dsimp; ring
  map_smul' a d := by dsimp; ring

theorem ker_degree : (degree K).ker = principalSubmodule K := by
  ext d
  constructor
  · intro hd
    refine ⟨d.2, ?_⟩
    change d.1 + 2 * d.2 = 0 at hd
    ext <;> dsimp [principal]
    · calc
        -2 * d.2 = -(2 * d.2) := by ring
        _ = d.1 := (eq_neg_of_add_eq_zero_left hd).symm
  · rintro ⟨a, rfl⟩
    change -2 * a + 2 * a = 0
    ring

theorem degree_surjective : Function.Surjective (degree K) :=
  fun a => ⟨(a, 0), by simp [degree]⟩

/-- The invariant character-divisor quotient is a line, with a proved normalization. -/
def classParameter : Class K ≃ₗ[K] K :=
  (Submodule.quotEquivOfEq _ _ (ker_degree K).symm).trans
    ((degree K).quotKerEquivOfSurjective (degree_surjective K))

@[simp]
theorem classParameter_classOf (d : K × K) :
    classParameter K (classOf K d) = d.1 + 2 * d.2 := by
  change (degree K).quotKerEquivOfSurjective (degree_surjective K)
    (Submodule.quotEquivOfEq _ _ (ker_degree K).symm (Submodule.Quotient.mk d)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

theorem same_class_iff (d e : K × K) :
    classOf K d = classOf K e ↔ d.1 + 2 * d.2 = e.1 + 2 * e.2 := by
  rw [← (classParameter K).injective.eq_iff]
  simp

@[simp]
theorem D0_parameter : classParameter K (classOf K (1, 0)) = 1 := by simp

theorem anticanonical_parameter : classParameter K (classOf K (1, 1)) = 3 := by
  simp
  ring

/-- The anticanonical boundary sum and `3D₀` differ by the norm-character divisor. -/
theorem three_D0_eq_anticanonical : classOf K (3, 0) = classOf K (1, 1) := by
  apply (same_class_iff K _ _).mpr
  dsimp
  ring

theorem rational_principal_coefficients (i : Fin 3) :
    coefficients ℚ (principal ℚ 1) i = boundaryOrders (1, 1) i := by
  rw [norm_character_orders]
  simp [coefficients, principal]

end Cubic.ToricHeights.DivisorParameters
