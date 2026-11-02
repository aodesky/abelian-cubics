import CubicTargets.ToricHeights.HeightFormula

/-!
# Concrete statement of `eqn:weightVectors`

The display of `lemma:heightformula`:
```text
𝟏,   (1 - 3e₂e₁⁻²)𝟏,
(e₁³ - 9/2 e₁e₂ + 27/2 e₃ ± √-27/2 √disc) e₁⁻³ 𝟏,        √disc := (X-Z)(Y-X)(Z-Y),
```
asserted there to be weight vectors of `H⁰(S_E, 𝒪(3D₀))` with characters
`1, χ^{a'+b'}, χ^{2a'+b'}, χ^{2b'+a'}` respectively. The model (global sections as
`E[X,Y,Z]₃^{C₃} e₁⁻³`, `𝟏 = 1`, weight vectors via values at points of `T_E`, `√-27 = 3(2ζ+1)`)
is that of `CubicTargets.ToricHeights.HeightFormula`; see its
docstring. The spanning assertion belongs to `lemma:heightformula`.
-/

noncomputable section

namespace CubicTargets.ToricHeights.WeightVectorsDisplay

open CubicTargets.ToricHeights.HeightFormula

def Claim : Prop :=
  ∀ j, weightVector j ∈ globalSections ∧ IsWeightVector (weightVector j) (weightCharacter j)

end CubicTargets.ToricHeights.WeightVectorsDisplay
