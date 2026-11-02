import Cubic.BoxAsymptotic.ZeroModeData
import Cubic.BoxAsymptotic.SmoothWeightData

/-!
# Full statement of `lem:smooth`

Unlike `SmoothSectorCounting`, which is the product-profile hypothesis used in the
existing conditional proof of `thm:main`, this target quantifies over arbitrary smooth
periodic weights, with universal constants and an explicit mixed-derivative bound.
The fixed support conventions are `X/2 ≤ n ≤ 4X` and `|wrap (θ-θ₀)| ≤ 4Θ`.
The coefficients refer to the independently defined zero-mode series and its numerator;
`eq:F0` certifies them. The conditional proof is in
`Cubic/BoxAsymptotic/SmoothSector.lean`; this module only defines its target.
-/

noncomputable section

namespace CubicTargets.BoxAsymptotic

open Cubic.BoxAsymptotic.ZeroModeData Cubic.BoxAsymptotic.SmoothWeightData
open scoped ContDiff

/-- Concrete target for the full smoothed sector estimate. `A`, `J`, and the implied
constant are chosen before the weight, scales, arc center, and derivative bound. -/
def SmoothSectorClaim : Prop :=
  ∃ A J : ℕ, ∃ Cst : ℝ, 0 < Cst ∧
    ∀ (X Θ θ₀ M : ℝ) (w : ℝ × ℝ → ℝ),
      2 ≤ X → 0 < Θ → Θ ≤ 1 → 0 ≤ M →
      ContDiff ℝ ∞ w →
      (∀ n θ : ℝ, w (n, θ + 2 * Real.pi) = w (n, θ)) →
      Function.support w ⊆
        {x | X / 2 ≤ x.1 ∧ x.1 ≤ 4 * X ∧ |wrap (x.2 - θ₀)| ≤ 4 * Θ} →
      normalizedDerivativeBound w Θ M J →
      |(∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (fun θ => w (n, θ))) -
          ∫ n in Set.Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi,
            w (n, θ) * (aStar * Real.log n + b₀) / (2 * Real.pi)| ≤
        Cst * M * Real.sqrt X * Real.log (2 * X + Θ⁻¹) ^ A

end CubicTargets.BoxAsymptotic
