import Cubic.ToricHeights.TraceOneCharacters
import Cubic.QuadraticCorrespondence.CharacterLattice

/-!
# Concrete statement of `eqn:formulaForNormCharacter`

In the proof of `lemma:heightformula`:
```text
χ^{a'+b'}(u v₀' + v v₁' + w v₂') = vw/u² = (X+ζY+ζ²Z)(X+ζ²Y+ζZ)/(X+Y+Z)² = (e₁²-3e₂)/e₁².
```

## Correspondence

* `𝒢` is the unit group of the original cyclic group algebra
  `CyclicGroupAlgebra.GroupAlgebra K = K[C₃]`. Points are taken over an arbitrary field `K`
  of characteristic zero containing a root `ζ` of `X²+X+1` (e.g. `K = E`); `X, Y, Z` are the
  coefficients of `g = X·1 + Y·σ + Z·σ²`, `e₁ = X+Y+Z`, `e₂ = XY+YZ+ZX` (homogeneous).
* The idempotents are `v₀' = (1+σ+σ²)/3`, `v₁' = (1+ζ²σ+ζσ²)/3`, `v₂' = (1+ζσ+ζ²σ²)/3`
  (`idempotent₀/₁/₂`), and `u, v, w` are the coordinates of `g` in this basis (a hypothesis
  `g = u v₀' + v v₁' + w v₂'`, as in the display).
* `χ₁ = firstCharacter` and `χ₂ = secondCharacter` (evaluation at `ζ`, `ζ²`) on the
  augmentation-one units `𝒢₁ = traceOneUnits`; `χ^{v₁^∨} = χ₁`, `χ^{v₂^∨} = χ₂`.
  A lattice element `m = m₁a' + m₂b' ∈ M_E` has `v^∨`-coordinates
  `CharacterLattice.pullback m = (2m₁-m₂, -m₁+2m₂)` (`a' = 2v₁^∨-v₂^∨`, `b' = 2v₂^∨-v₁^∨`),
  so `χ^m = χ₁^{(pullback m).1} χ₂^{(pullback m).2}` (`character`). Characters of `𝒢₁` are
  evaluated on `𝒢` by pulling back along `g ↦ χ₀(g)⁻¹ g` (`normalize`), where `χ₀` is the
  augmentation, exactly as the paper specifies.
* `a'+b'` is `(1,1)`.
-/

noncomputable section

namespace CubicTargets.ToricHeights.FormulaForNormCharacter

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters
open Cubic.QuadraticCorrespondence

variable {K : Type} [Field K] [CharZero K]

/-- `v₀' = (1+σ+σ²)/3`. -/
def idempotent₀ : GroupAlgebra K := coordinates K (1 / 3) (1 / 3) (1 / 3)

/-- `v₁' = (1+ζ²σ+ζσ²)/3`. -/
def idempotent₁ (ζ : K) : GroupAlgebra K := coordinates K (1 / 3) (ζ ^ 2 / 3) (ζ / 3)

/-- `v₂' = (1+ζσ+ζ²σ²)/3`. -/
def idempotent₂ (ζ : K) : GroupAlgebra K := coordinates K (1 / 3) (ζ / 3) (ζ ^ 2 / 3)

/-- The projection `𝒢 → 𝒢₁`, `g ↦ χ₀(g)⁻¹ g`. -/
def normalize : (GroupAlgebra K)ˣ →* traceOneUnits K where
  toFun g := ⟨Units.map (algebraMap K (GroupAlgebra K)).toMonoidHom
      (Units.map (augmentation K).toMonoidHom g)⁻¹ * g, by
    apply Units.ext
    change augmentation K (algebraMap K (GroupAlgebra K)
      ((Units.map (augmentation K).toMonoidHom g)⁻¹ : Kˣ) * (g : GroupAlgebra K)) = 1
    rw [map_mul, AlgHom.commutes]
    exact (Units.map (augmentation K).toMonoidHom g).inv_mul⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    simp only [map_mul, mul_inv, Subgroup.coe_mul]
    rw [mul_mul_mul_comm]

/-- `χ^m` on `𝒢₁` for `m = m₁a' + m₂b'`. -/
def character (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) (m : ℤ × ℤ) : traceOneUnits K →* Kˣ :=
  firstCharacter ζ hζ ^ (CharacterLattice.pullback m).1 *
    secondCharacter ζ hζ ^ (CharacterLattice.pullback m).2

/-- `χ^m` evaluated on `𝒢` (pullback along `normalize`). -/
def groupCharacter (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) (m : ℤ × ℤ) : (GroupAlgebra K)ˣ →* Kˣ :=
  (character ζ hζ m).comp normalize

/-- `e₂ = XY + YZ + ZX`. -/
def e₂ (g : GroupAlgebra K) : K := g 0 * g 1 + g 1 * g 2 + g 2 * g 0

/-- `e₁ = X + Y + Z`. -/
def e₁ (g : GroupAlgebra K) : K := g 0 + g 1 + g 2

def Claim : Prop :=
  ∀ {K : Type} [Field K] [CharZero K] (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (g : (GroupAlgebra K)ˣ) (u v w : K),
    (g : GroupAlgebra K) = u • idempotent₀ + v • idempotent₁ ζ + w • idempotent₂ ζ →
    ((groupCharacter ζ hζ (1, 1) g : Kˣ) : K) = v * w / u ^ 2 ∧
    v * w / u ^ 2 =
      ((g : GroupAlgebra K) 0 + ζ * (g : GroupAlgebra K) 1 + ζ ^ 2 * (g : GroupAlgebra K) 2) *
        ((g : GroupAlgebra K) 0 + ζ ^ 2 * (g : GroupAlgebra K) 1 + ζ * (g : GroupAlgebra K) 2) /
        ((g : GroupAlgebra K) 0 + (g : GroupAlgebra K) 1 + (g : GroupAlgebra K) 2) ^ 2 ∧
    ((g : GroupAlgebra K) 0 + ζ * (g : GroupAlgebra K) 1 + ζ ^ 2 * (g : GroupAlgebra K) 2) *
        ((g : GroupAlgebra K) 0 + ζ ^ 2 * (g : GroupAlgebra K) 1 + ζ * (g : GroupAlgebra K) 2) /
        ((g : GroupAlgebra K) 0 + (g : GroupAlgebra K) 1 + (g : GroupAlgebra K) 2) ^ 2 =
      (e₁ (g : GroupAlgebra K) ^ 2 - 3 * e₂ (g : GroupAlgebra K)) / e₁ (g : GroupAlgebra K) ^ 2

end CubicTargets.ToricHeights.FormulaForNormCharacter
