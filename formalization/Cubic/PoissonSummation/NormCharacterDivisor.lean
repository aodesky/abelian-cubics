import CubicTargets.PoissonSummation.NormCharacterDivisor

/-!
# Proof of `eqn:normCharacterDivisor`

As in the paper: `a'+b' = v₁^∨ + v₂^∨` pairs to `1` with `v₁, v₂` and to `-2` with
`v₀ = -v₁ - v₂` (`DivisorParameters.norm_character_orders`).
-/

noncomputable section

namespace Cubic.PoissonSummation.NormCharacterDivisor

open Cubic.ToricHeights.DivisorParameters
open CubicTargets.PoissonSummation.NormCharacterDivisor

theorem «eqn:normCharacterDivisor» : CubicTargets.PoissonSummation.NormCharacterDivisor.Claim := by
  unfold Claim characterDivisor
  simp only [Fin.sum_univ_three, norm_character_orders]
  simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, if_true, if_false,
    one_smul, add_assoc]

end Cubic.PoissonSummation.NormCharacterDivisor
