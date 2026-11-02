import Cubic.PoissonSummation.AdelicCutoff
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integrating the actual height over finite-place stages

This is the finite-place part of the first Fubini--Tonelli step in the proof
of `lemma:heightZetaConvergence`. Three belongs to every stage, so the exceptional
cutoff is integrated explicitly; all omitted compact factors are one.
-/

noncomputable section

namespace Cubic.PoissonSummation.FiniteAdelicStages

open MeasureTheory Set
open QuotientFiniteFourierProduct FiniteEulerProduct AdelicHeightZetaData
open CubicTargets.PoissonSummation.FiniteFourierProduct
open scoped RestrictedProductHaar AdelicHeightZetaData

abbrev Stage (S : Finset Nat.Primes) := RestrictedProductHaar.Stage
  (fun p => (family p).Carrier) (fun p => (family p).maxCompact) S

abbrev inclusion (S : Finset Nat.Primes) := RestrictedProductHaar.inclusion
  (fun p => (family p).Carrier) (fun p => (family p).maxCompact) S

abbrev projection (S : Finset Nat.Primes) := RestrictedProductHaar.projection
  (fun p => (family p).Carrier) (fun p => (family p).maxCompact) S

abbrev measure (S : Finset Nat.Primes) := RestrictedProductHaar.stageMeasure
  (fun p => (family p).Carrier) (fun p => (family p).maxCompact)
  (fun p => (family p).compact) S

theorem finiteCutoffHeight_eq_prod (S : Finset Nat.Primes) (hthree : primeThree ∈ S)
    (s₀ σ : ℂ) (x : FiniteAdelicData.Points)
    (hS : ∀ p ∉ S, x p ∈ (family p).maxCompact) :
    finiteCutoffHeight s₀ σ x = ∏ p ∈ S, localCutoffHeight p s₀ σ (x p) := by
  classical
  by_cases hx : x ∈ finiteIntegralLocus
  · rw [finiteCutoffHeight, Set.indicator_of_mem hx,
      FiniteAdelicData.inverseHeight_eq_prod s₀ σ x S hS]
    apply Finset.prod_congr rfl
    intro p _
    exact (Set.indicator_of_mem (hx p) _).symm
  · rw [finiteCutoffHeight, Set.indicator_of_notMem hx]
    have hex : ∃ p, x p ∉ (family p).integralLocus := by
      simpa only [finiteIntegralLocus, mem_setOf_eq, not_forall] using hx
    obtain ⟨p, hp⟩ := hex
    have hpS : p ∈ S := by
      by_contra h
      exact hp (local_compact_subset_integral p (by intro he; subst p; exact h hthree) (hS p h))
    exact (Finset.prod_eq_zero hpS (Set.indicator_of_notMem hp _)).symm

theorem localCutoffHeight_eq_integrand (p : Nat.Primes) (s₀ σ : ℂ) :
    localCutoffHeight p s₀ σ = localIntegrand (family p) s₀ σ 0 := by
  funext x
  simp only [localCutoffHeight, localIntegrand, (family p).character_zero]
  change _ = _ * ((1 : Circle) : ℂ)⁻¹
  simp

theorem localCutoffHeight_integrable (p : Nat.Primes) (s₀ σ : ℂ) (hσ : 1 < σ.re) :
    Integrable (localCutoffHeight p s₀ σ) (family p).measure := by
  rw [localCutoffHeight_eq_integrand]
  exact localCalculation.integrable p s₀ σ 0 hσ

theorem integral_localCutoffHeight (p : Nat.Primes) (s₀ σ : ℂ) :
    (∫ x, localCutoffHeight p s₀ σ x ∂(family p).measure) = localFourier (family p) s₀ σ 0 := by
  rw [localCutoffHeight_eq_integrand]
  rfl

theorem stage_height_eq (S : Finset Nat.Primes) (hthree : primeThree ∈ S)
    (s₀ σ : ℂ) (x : Stage S) :
    finiteCutoffHeight s₀ σ (inclusion S x) = ∏ p : S, localCutoffHeight p s₀ σ (x p) := by
  rw [finiteCutoffHeight_eq_prod S hthree s₀ σ _ (fun p hp => x.property hp)]
  exact (Finset.prod_coe_sort S _).symm

instance localSigmaFinite (p : Nat.Primes) : SigmaFinite (family p).measure := by
  letI : SigmaCompactSpace (family p).Carrier := sigmaCompactSpace_of_locallyCompact_secondCountable
  exact Measure.IsHaarMeasure.sigmaFinite _

theorem projection_measurePreserving (S : Finset Nat.Primes) :
    MeasurePreserving (projection S) (measure S) (Measure.pi fun p : S => (family p).measure) :=
  ⟨(RestrictedProductHaar.continuous_projection _ _ S).measurable,
    RestrictedProductHaar.map_stageMeasure_projection _ _ (fun p => (family p).compact)
      (fun p => (family p).measure) (fun p => (family p).normalized) S⟩

theorem integrable_stage_height (S : Finset Nat.Primes) (hthree : primeThree ∈ S)
    (s₀ σ : ℂ) (hσ : 1 < σ.re) :
    Integrable (fun x : Stage S => finiteCutoffHeight s₀ σ (inclusion S x)) (measure S) := by
  have hI := Integrable.fintype_prod_dep (fun p : S => localCutoffHeight_integrable p s₀ σ hσ)
  have hmap : Integrable (fun x : ∀ p : S, (family p).Carrier =>
      ∏ p : S, localCutoffHeight p s₀ σ (x p)) ((measure S).map (projection S)) := by
    rw [(projection_measurePreserving S).map_eq]
    exact hI
  have hcomp := (integrable_map_measure hmap.aestronglyMeasurable
    (projection_measurePreserving S).measurable.aemeasurable).mp hmap
  simpa only [Function.comp_def, stage_height_eq S hthree, projection,
    RestrictedProductHaar.projection, MonoidHom.coe_mk, OneHom.coe_mk] using hcomp

theorem integral_stage_height (S : Finset Nat.Primes) (hthree : primeThree ∈ S)
    (s₀ σ : ℂ) (hσ : 1 < σ.re) :
    (∫ x : Stage S, finiteCutoffHeight s₀ σ (inclusion S x) ∂measure S) =
      ∏ p ∈ S, localFourier (family p) s₀ σ 0 := by
  have hI := Integrable.fintype_prod_dep (fun p : S => localCutoffHeight_integrable p s₀ σ hσ)
  have hmap : AEStronglyMeasurable (fun x : ∀ p : S, (family p).Carrier =>
      ∏ p : S, localCutoffHeight p s₀ σ (x p)) ((measure S).map (projection S)) := by
    rw [(projection_measurePreserving S).map_eq]
    exact hI.aestronglyMeasurable
  simp_rw [stage_height_eq S hthree]
  change (∫ x : Stage S, (fun y : ∀ p : S, (family p).Carrier =>
    ∏ p : S, localCutoffHeight p s₀ σ (y p)) (projection S x) ∂measure S) = _
  rw [← integral_map (projection_measurePreserving S).measurable.aemeasurable hmap,
    (projection_measurePreserving S).map_eq, integral_fintype_prod_eq_prod]
  simp_rw [integral_localCutoffHeight]
  exact Finset.prod_coe_sort S (fun p : Nat.Primes => localFourier (family p) s₀ σ 0)

end Cubic.PoissonSummation.FiniteAdelicStages
