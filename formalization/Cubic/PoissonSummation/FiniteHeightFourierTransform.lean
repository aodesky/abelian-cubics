import CubicTargets.PoissonSummation.FiniteHeightFourierTransform
import Cubic.PoissonSummation.HeightFourierPlaces

/-!
# `eqn:finiteHeightFourierTransform`

The proof follows the paper. At each place `w | v ≠ 3`, the hypotheses `HeightFourierPlaces.*Hyp`
come from `prop:basicfacts` and `prop:localIntegrality`. They give the exact sequence
`1 → K_v^max → T(ℚ_v) → N_w → 0`, the formula `H_v(x,-s) = q_v^{φ(ℓ_w x)}`, and the cone
description of `1_v^{D₀}`. Since `d^×x_v(K_v^max) = 1`, `ℓ_w` pushes `d^×x_v` forward to counting
measure on `N_w`. The integral is therefore the lattice sum
(`UnramifiedLocalFourier.hasSum_lattice`, the content of `eqn:localfourierassumovern`).
Its convergence uses only `Re σ > 0`.
-/

namespace Cubic.PoissonSummation.FiniteHeightFourierTransform

open UnramifiedLocalFourier HeightFourierPlaces
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology Cubic.ToricHeights.QuotientLocalHaar

theorem «eqn:finiteHeightFourierTransform» :
    CubicTargets.PoissonSummation.FiniteHeightFourierTransform.Claim where
  split_first p _ _ χ hχ ψ hψ s₀ σ h₀ hσ :=
    (placeConclusions (splitHyp_first p)).formula χ hχ ψ hψ s₀ σ h₀ hσ
  split_second p _ _ χ hχ ψ hψ s₀ σ h₀ hσ :=
    (placeConclusions (splitHyp_second p)).formula χ hχ ψ hψ s₀ σ h₀ hσ
  inert p _ _ χ hχ ψ hψ s₀ σ h₀ hσ :=
    (placeConclusions (inertHyp p)).formula χ hχ ψ hψ s₀ σ h₀ hσ

end Cubic.PoissonSummation.FiniteHeightFourierTransform
