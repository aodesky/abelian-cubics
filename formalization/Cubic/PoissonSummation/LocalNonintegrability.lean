import CubicTargets.PoissonSummation.LocalNonintegrability
import Cubic.PoissonSummation.HeightFourierPlaces

/-! At `σ=0` the local integrand is one on infinitely many disjoint
valuation cosets, each with normalized Haar mass one. -/

noncomputable section

namespace Cubic.PoissonSummation.LocalNonintegrability

open MeasureTheory UnramifiedLocalFourier
open Cubic.ToricHeights Cubic.OrbitParametrization
open CubicTargets.ToricHeights.BasicFacts
open CubicTargets.PoissonSummation.HeightFourierTransform
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology Cubic.ToricHeights.QuotientLocalHaar

theorem not_integrable
    {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
    {K : Subgroup G} {D : DecompositionGroup} {ℓ : G → ℤ × ℤ} {q : ℕ}
    {h : ℂ → ℂ → G → ℂ} {ind : G → ℝ}
    (H : PlaceHyp μ K D ℓ q h ind) (s₀ : ℂ) :
    ¬ Integrable (integrand h ind s₀ 0) μ := by
  classical
  let V := valuation H
  letI : MeasurableSpace (Multiplicative (invariantLattice D)) := ⊤
  haveI : Countable (Multiplicative (invariantLattice D)) :=
    Multiplicative.toAdd.injective.countable
  have hm : Measurable V := measurable_of_countable_ker V
    (by rw [valuation_ker H]; exact H.isOpen.measurableSet)
  have hv := measurePreserving_count_of_ker μ V hm (valuation_surjective H)
    (by rw [valuation_ker H]; exact H.measure_K)
  let g : Multiplicative (invariantLattice D) → ℂ := fun n =>
    if LatticeCone.InCone (n.toAdd : ℤ × ℤ) then 1 else 0
  have hf : integrand h ind s₀ 0 = g ∘ V := by
    funext x
    by_cases hx : LatticeCone.InCone (ℓ x)
    · simp [integrand, H.height_eq, H.indicator_eq, hx,
        supportFunction_cone s₀ 0 hx, g, V, valuation]
    · simp [integrand, H.indicator_eq, hx, g, V, valuation]
  let i : ℕ → Multiplicative (invariantLattice D) := fun n =>
    Multiplicative.ofAdd ⟨(-(n : ℤ), 3 * n), by
      cases D
      · trivial
      · change CocharacterLattice.conjugation (-(n : ℤ), 3 * (n : ℤ)) =
          (-(n : ℤ), 3 * (n : ℤ))
        ext <;> simp [CocharacterLattice.conjugation] <;> ring⟩
  have hi : Function.Injective i := by
    intro n m he
    have h1 := congrArg (fun z : Multiplicative (invariantLattice D) =>
      (z.toAdd : ℤ × ℤ).1) he
    simpa [i] using h1
  have hg : ∀ n : ℕ, ‖g (i n)‖ = 1 := by
    intro n
    have hn : LatticeCone.InCone (-(n : ℤ), 3 * n) := by
      rw [LatticeCone.inCone_iff]
      constructor <;> dsimp <;> omega
    simp [g, i, hn]
  intro hint
  rw [hf] at hint
  have hcount : Integrable g Measure.count :=
    (hv.integrable_comp (measurable_of_countable g).aestronglyMeasurable).mp hint
  have hs := (integrable_count_iff.mp hcount).comp_injective hi
  have hs1 : Summable (fun _ : ℕ => (1 : ℝ)) := hs.congr hg
  simpa only [summable_const_iff, one_ne_zero] using hs1

theorem «rem:localNonintegrability» :
    CubicTargets.PoissonSummation.LocalNonintegrability.Claim where
  split p _ _ s₀ := not_integrable (HeightFourierPlaces.splitHyp_first p) s₀
  inert p _ _ s₀ := not_integrable (HeightFourierPlaces.inertHyp p) s₀

end Cubic.PoissonSummation.LocalNonintegrability
