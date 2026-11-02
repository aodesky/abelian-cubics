import Cubic.ToricHeights.DivisorParameters
import Mathlib.Algebra.BigOperators.Fin

/-!
# Concrete statement of `eqn:normCharacterDivisor`

In the proof of `lemma:simplifiedZ(s)`:
```text
div(χ^{a'+b'}) = Σ_{i=0}^{2} ⟨a'+b', v_i⟩ D_i = -2D₀ + D₁ + D₂.
```

## Model

* A divisor supported on the boundary is its coefficient vector `Fin 3 → ℚ` on
  `(D₀, D₁, D₂)`; `D i = Pi.single i 1`. (The coefficients below are integers.)
* The divisor of a character is given by the fan pairing (Fulton, *Introduction to toric
  varieties*, §3.3): `div(χ^u) := Σ_i ⟨u, v_i⟩ D_i`, with the primitive ray
  generators `v_i` of the fan (`DivisorParameters.ray`, expressed in the `(v₁, v₂)`-basis by
  `CocharacterLattice.coordinates`) and `u = m₁a' + m₂b'` expressed in the dual basis
  `(v₁^∨, v₂^∨)` by `CharacterLattice.pullback` (`a' = 2v₁^∨ - v₂^∨`, `b' = 2v₂^∨ - v₁^∨`).
  The pairing `⟨u, v_i⟩` is `DivisorParameters.boundaryOrders (m₁, m₂) i`. With this model the
  first equality of the display is the definition (Fulton's toric divisor formula, cited by the
  paper) and the content is the second.
* `a'+b'` is `(1, 1)`.
-/

noncomputable section

namespace CubicTargets.PoissonSummation.NormCharacterDivisor

open Cubic.ToricHeights.DivisorParameters

/-- The boundary divisor `D i`. -/
def boundaryDivisor (i : Fin 3) : Fin 3 → ℚ := Pi.single i 1

/-- `div(χ^u) = Σ_i ⟨u, v_i⟩ D_i` for `u = m₁a' + m₂b'`. -/
def characterDivisor (m : ℤ × ℤ) : Fin 3 → ℚ :=
  ∑ i, boundaryOrders m i • boundaryDivisor i

def Claim : Prop :=
  characterDivisor (1, 1) = (-2 : ℚ) • boundaryDivisor 0 + boundaryDivisor 1 + boundaryDivisor 2

end CubicTargets.PoissonSummation.NormCharacterDivisor
