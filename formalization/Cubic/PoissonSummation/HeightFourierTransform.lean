import Cubic.PoissonSummation.InfiniteHeightFourierTransform
import Cubic.PoissonSummation.FiniteHeightFourierTransform
import Cubic.PoissonSummation.HeightFourierPlaces
import Cubic.PoissonSummation.ArchimedeanHeightFourier

/-!
# `prop:heightFourierTransform`

## Correspondence with the paper's proof

* Infinite place (`ArchimedeanHeightFourier`).
  - `1_∞^{D₀} = 1`, and the height is `K_∞^max`-invariant.
  - Ramified `χ`: the transform vanishes by Schur's lemma (`fourier_eq_zero_of_ramified`).
  - Unramified `χ`: `χ = e(⟨ℓ_w, m⟩)` for a unique `m` (`exists_unique_m`).
  - The formula is `eqn:infiniteHeightFourierTransform`.
  - Departure: the paper takes existence and uniqueness of `m` as evident. Here they are proved:
    `χ` factors through `log|·|`, and continuous characters of `ℝ` are classified
    (`RealCharacter.exists_parameter`).
* Finite `v ≠ 3` (`UnramifiedLocalFourier`, `HeightFourierPlaces`).
  - `1_v^{D₀}` is `K_v^max`-invariant and equals the cone indicator (`prop:localIntegrality`).
  - Ramified `χ`: Schur's lemma (`fourier_eq_zero_of_ramified`).
  - Unramified `χ` factors through `ℓ_w` onto `N_w` (`exists_unique_descends`,
    using `prop:basicfacts`).
  - The lattice sum is `eqn:localfourierassumovern`, and the formula is
    `eqn:finiteHeightFourierTransform`.
* Absolute convergence and holomorphy for every unitary `χ`, on `Re s₁, Re s₂ > 0`.
  - Ramified `χ`: the transform is identically zero.
  - Unramified `χ`: the lattice sum is dominated on `{Re σ > a}` by the summable series
    `q_v^{-a(n₁+n₂)}`, so it converges locally uniformly
    (`Complex.differentiableOn_tsum_of_summable_norm`).
  - Departure: the paper states this without proof.
* `v = 3` (`HeightFourierPlaces`).
  - The support is `K_{3,2}` by `prop:localIntegrality`(2); the height is nonzero everywhere.
  - Index six is transported from the explicit reduction `(O_{E,w}/3)^×`
    (`RamifiedLocalModel.congruenceSubgroup_index`).
  - The height is one on `K_3^max` because `ℓ_w` vanishes there (`prop:basicfacts`). So the
    transform is independent of `s` and holomorphic.
-/

namespace Cubic.PoissonSummation.HeightFourierTransform

open CubicTargets.PoissonSummation.HeightFourierTransform
open UnramifiedLocalFourier HeightFourierPlaces ArchimedeanHeightFourier
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology Cubic.ToricHeights.QuotientLocalHaar

theorem «prop:heightFourierTransform» :
    CubicTargets.PoissonSummation.HeightFourierTransform.Claim where
  infinite_integrable χ s₀ σ h₀ hσ := ArchimedeanHeightFourier.integrable χ s₀ σ h₀ hσ
  infinite_ramified χ hχ s₀ σ _ _ := ArchimedeanHeightFourier.fourier_eq_zero_of_ramified χ hχ s₀ σ
  infinite_unramified χ hχ := exists_unique_m χ hχ
  infinite_formula χ m hχ hm hexp s₀ σ h₀ hσ :=
    InfiniteHeightFourierTransform.«eqn:infiniteHeightFourierTransform» χ m hχ hm hexp s₀ σ h₀ hσ
  split_converges p _ _ := convergesHolomorphically (splitHyp_first p)
  inert_converges p _ _ := convergesHolomorphically (inertHyp p)
  three_converges := HeightFourierPlaces.three_converges
  split_invariant p _ _ := indicator_invariant (splitHyp_first p)
  inert_invariant p _ _ := indicator_invariant (inertHyp p)
  split_first p _ _ :=
    { ramified := (placeConclusions (splitHyp_first p)).ramified
      descends := (placeConclusions (splitHyp_first p)).descends
      formula := FiniteHeightFourierTransform.«eqn:finiteHeightFourierTransform».split_first p }
  split_second p _ _ :=
    { ramified := (placeConclusions (splitHyp_second p)).ramified
      descends := (placeConclusions (splitHyp_second p)).descends
      formula := FiniteHeightFourierTransform.«eqn:finiteHeightFourierTransform».split_second p }
  inert p _ _ :=
    { ramified := (placeConclusions (inertHyp p)).ramified
      descends := (placeConclusions (inertHyp p)).descends
      formula := FiniteHeightFourierTransform.«eqn:finiteHeightFourierTransform».inert p }
  three_support s₀ σ _ _ := HeightFourierPlaces.three_support s₀ σ
  three_index := HeightFourierPlaces.three_index
  three_image := HeightFourierPlaces.three_image

end Cubic.PoissonSummation.HeightFourierTransform
