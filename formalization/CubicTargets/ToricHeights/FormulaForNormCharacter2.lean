import CubicTargets.ToricHeights.FormulaForNormCharacter

/-!
# Concrete statement of `eqn:formulaForNormCharacter2`

In the proof of `lemma:heightformula`:
```text
χ^{2b'+a'}(u v₀' + v v₁' + w v₂') = w³/u³
    = (e₁³ - 9/2 e₁e₂ + 27/2 e₃ - √-27/2 √disc)/e₁³.
```
The objects `𝒢`, `v_i'`, `u, v, w`, `X, Y, Z`, `χ^m` are as in
`CubicTargets.ToricHeights.FormulaForNormCharacter`; `2b'+a'` is `(1,2)`,
`e₃ = XYZ` and `√disc = (X-Z)(Y-X)(Z-Y)` (the paper's definition). The TeX does not fix the
square root `√-27`; we use the project's `√-27 = 3(2ζ+1)` (`WeightVectors.sqrtNegTwentySeven`,
with `(2ζ+1)² = -3`). With the other root the display holds for the conjugate character
`χ^{2a'+b'}` instead.
-/

noncomputable section

namespace CubicTargets.ToricHeights.FormulaForNormCharacter2

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open CubicTargets.ToricHeights.FormulaForNormCharacter

/-- `e₃ = XYZ`. -/
def e₃ {K : Type} [Field K] (g : GroupAlgebra K) : K := g 0 * g 1 * g 2

/-- `√disc = (X-Z)(Y-X)(Z-Y)`. -/
def sqrtDisc {K : Type} [Field K] (g : GroupAlgebra K) : K :=
  (g 0 - g 2) * (g 1 - g 0) * (g 2 - g 1)

def Claim : Prop :=
  ∀ {K : Type} [Field K] [CharZero K] (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (g : (GroupAlgebra K)ˣ) (u v w : K),
    (g : GroupAlgebra K) = u • idempotent₀ + v • idempotent₁ ζ + w • idempotent₂ ζ →
    ((groupCharacter ζ hζ (1, 2) g : Kˣ) : K) = w ^ 3 / u ^ 3 ∧
    w ^ 3 / u ^ 3 =
      (e₁ (g : GroupAlgebra K) ^ 3 - 9 / 2 * e₁ (g : GroupAlgebra K) * e₂ (g : GroupAlgebra K) +
          27 / 2 * e₃ (g : GroupAlgebra K) -
          3 * (2 * ζ + 1) / 2 * sqrtDisc (g : GroupAlgebra K)) /
        e₁ (g : GroupAlgebra K) ^ 3

end CubicTargets.ToricHeights.FormulaForNormCharacter2
