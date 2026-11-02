import CubicTargets.ToricHeights.FormulaForNormCharacter2
import Cubic.ToricHeights.FormulaForNormCharacter
import Cubic.ToricHeights.WeightVectors

/-!
# Proof of `eqn:formulaForNormCharacter2`

As in the paper: `2b'+a' = 3v₂^∨`, so `χ^{2b'+a'}` pulls back to `χ₂³/χ₀³ = w³/u³`.
With `χ₁ = X+ζY+ζ²Z` and `χ₂ = X+ζ²Y+ζZ`,
`χ₁³ + χ₂³ = 2e₁³ - 9e₁e₂ + 27e₃` (`TraceOneCharacters.eigenvalue_cubes_sum`) and
`χ₁³ - χ₂³ = √-27 √disc` (`WeightVectors.eigenvalue_cubes_difference`), whence
`χ₂³ = e₁³ - 9/2 e₁e₂ + 27/2 e₃ - √-27/2 √disc`.
-/

noncomputable section

namespace Cubic.ToricHeights.FormulaForNormCharacter2

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters
open Cubic.QuadraticCorrespondence
open CubicTargets.ToricHeights.FormulaForNormCharacter
open CubicTargets.ToricHeights.FormulaForNormCharacter2
open Cubic.ToricHeights.FormulaForNormCharacter

theorem «eqn:formulaForNormCharacter2» :
    CubicTargets.ToricHeights.FormulaForNormCharacter2.Claim := by
  intro K _ _ ζ hζ g u v w hg
  obtain ⟨hu, hv, hw⟩ := idempotent_values ζ hζ (g : GroupAlgebra K) u v w hg
  have ha : augmentation K (g : GroupAlgebra K) = u := by
    rw [augmentation_coefficients, hu]
  refine ⟨?_, ?_⟩
  · rw [groupCharacter_val, first_normalize, second_normalize, ha, hw]
    simp only [CharacterLattice.pullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    norm_num
    simp only [mul_pow, zpow_ofNat]
    rw [inv_pow, div_eq_mul_inv, mul_comm]
  · have hs := eigenvalue_cubes_sum ζ hζ ((g : GroupAlgebra K) 0) ((g : GroupAlgebra K) 1)
      ((g : GroupAlgebra K) 2)
    have hd := WeightVectors.eigenvalue_cubes_difference ζ hζ ((g : GroupAlgebra K) 0)
      ((g : GroupAlgebra K) 1) ((g : GroupAlgebra K) 2)
    unfold Cubic.OrbitParametrization.secondCoeff at hs
    rw [← hu, ← hw]
    simp only [e₁, e₂, e₃, sqrtDisc]
    congr 1
    linear_combination (1 / 2 : K) * hs - (1 / 2 : K) * hd

end Cubic.ToricHeights.FormulaForNormCharacter2
