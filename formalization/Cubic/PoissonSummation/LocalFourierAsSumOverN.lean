import CubicTargets.PoissonSummation.LocalFourierAsSumOverN
import Cubic.PoissonSummation.HeightFourierPlaces

/-!
# `eqn:localfourierassumovern`

The proof follows the paper. The integrand is `K_v^max`-invariant, and `d^×x_v(K_v^max) = 1`.
So `ℓ_w : T(ℚ_v) → N_w` pushes `d^×x_v` forward to counting measure
(`measurePreserving_count_of_ker`, via `UnramifiedLocalFourier.hasSum_lattice`). This gives the
sum over `N_w`. Its terms vanish off the cone by `prop:localIntegrality`, which gives the second
equality. The place hypotheses are `HeightFourierPlaces.splitHyp_first`, `splitHyp_second` and
`inertHyp`.
-/

namespace Cubic.PoissonSummation.LocalFourierAsSumOverN

open MeasureTheory
open CubicTargets.ToricHeights.BasicFacts
open CubicTargets.PoissonSummation.HeightFourierTransform
open CubicTargets.PoissonSummation.LocalFourierAsSumOverN
open UnramifiedLocalFourier HeightFourierPlaces
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology Cubic.ToricHeights.QuotientLocalHaar

attribute [local instance] Classical.propDecidable

theorem sumOverN_of_hyp {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure] {K : Subgroup G}
    {D : DecompositionGroup} {ℓ : G → ℤ × ℤ} {q : ℕ} {h : ℂ → ℂ → G → ℂ} {ind : G → ℝ}
    (H : PlaceHyp μ K D ℓ q h ind) (χ : PontryaginDual G)
    (ψ : Multiplicative (invariantLattice D) →* Circle) (hψ : Descends D ℓ χ ψ)
    (s₀ σ : ℂ) (hσ : 0 < σ.re) : SumOverN μ D ℓ q (h s₀ σ) ind χ ψ s₀ σ := by
  obtain ⟨hI, hL, hC⟩ := hasSum_lattice H χ ψ hψ s₀ σ hσ
  refine ⟨hI, fun n => if Cubic.PoissonSummation.LatticeCone.InCone (n : ℤ × ℤ) then 1 else 0,
    fun x n hn => ?_, hL, hC⟩
  simp only
  rw [H.indicator_eq, hn]

theorem «eqn:localfourierassumovern» :
    CubicTargets.PoissonSummation.LocalFourierAsSumOverN.Claim where
  split_first p _ _ χ _ ψ hψ s₀ σ _ hσ := sumOverN_of_hyp (splitHyp_first p) χ ψ hψ s₀ σ hσ
  split_second p _ _ χ _ ψ hψ s₀ σ _ hσ := sumOverN_of_hyp (splitHyp_second p) χ ψ hψ s₀ σ hσ
  inert p _ _ χ _ ψ hψ s₀ σ _ hσ := sumOverN_of_hyp (inertHyp p) χ ψ hψ s₀ σ hσ

end Cubic.PoissonSummation.LocalFourierAsSumOverN
