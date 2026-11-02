import CubicTargets.ToricHeights.WeightVectorsDisplay
import Cubic.ToricHeights.HeightFormula

/-!
# Proof of `eqn:weightVectors`

Each displayed vector is `numerator j · e₁⁻³` (`HeightFormula.sectionOf_numerator`). Here
`numerator j` equals the invariant eigen-monomial `χ₀³, χ₀χ₁χ₂, χ₁³, χ₂³`
(`HeightFormula.numerator_eq_eigenMonomial`, the identities of
`eqn:formulaForNormCharacter(2)`), so it is a `C₃`-invariant cubic
(`HeightFormula.numerator_mem`). The vector is therefore the twist `χ^u 𝟏` of `𝟏`, and its
value at a point of `T_E` is the listed character (`HeightFormula.weightVector_character`).
-/

noncomputable section

namespace Cubic.ToricHeights.WeightVectorsDisplay

open CubicTargets.ToricHeights.HeightFormula
open Cubic.ToricHeights.HeightFormula

theorem «eqn:weightVectors» : CubicTargets.ToricHeights.WeightVectorsDisplay.Claim := fun j =>
  ⟨⟨numerator j, numerator_mem j, sectionOf_numerator j⟩, weightVector_character j⟩

end Cubic.ToricHeights.WeightVectorsDisplay
