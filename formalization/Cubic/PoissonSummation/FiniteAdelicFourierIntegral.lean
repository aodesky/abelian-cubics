import Cubic.PoissonSummation.AdelicSpatialIntegrability
import Cubic.PoissonSummation.FiniteAdelicFourier

/-!
# Fourier integration on the finite restricted product

The integrand is the original cutoff height times the inverse logarithmic
character. Integrate first over finite-place stages containing three, using
the actual local Haar measures, then exhaust the restricted product. Absolute
integrability justifies the complex integral limit; convergence of the local
Fourier product identifies the same limit. This supplies the finite part of
the global factorization used in `lemma:poissonIntegral`.
-/

noncomputable section

namespace Cubic.PoissonSummation.FiniteAdelicFourierIntegral

open MeasureTheory Set Filter
open QuotientFiniteFourierProduct FiniteEulerProduct AdelicHeightZetaData
open CubicTargets.PoissonSummation.FiniteFourierProduct
open scoped RestrictedProductHaar AdelicHeightZetaData Topology

/-- The actual finite adelic Fourier integrand, before any factorization. -/
def integrand (s₀ σ : ℂ) (t : ℝ) (x : FiniteAdelicData.Points) : ℂ :=
  finiteCutoffHeight s₀ σ x * ((FiniteAdelicData.character t x : Circle) : ℂ)⁻¹

theorem norm_integrand (s₀ σ : ℂ) (t : ℝ) (x : FiniteAdelicData.Points) :
    ‖integrand s₀ σ t x‖ = ‖finiteCutoffHeight s₀ σ x‖ := by
  simp [integrand]

theorem measurable_integrand (s₀ σ : ℂ) (t : ℝ) : Measurable (integrand s₀ σ t) := by
  apply (measurable_finiteCutoffHeight s₀ σ).mul
  exact (continuous_subtype_val.comp (FiniteAdelicData.character t).continuous).measurable.inv

theorem integrable (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Integrable (integrand s₀ σ t) finiteMeasure := by
  apply (AdelicSpatialIntegrability.finite_integrable s₀ σ hσ).mono
    (measurable_integrand s₀ σ t).aestronglyMeasurable
  exact ae_of_all _ fun x => (norm_integrand s₀ σ t x).le

theorem character_eq_prod (S : Finset Nat.Primes) (x : FiniteAdelicData.Points)
    (hS : ∀ p ∉ S, x p ∈ (family p).maxCompact) (t : ℝ) :
    FiniteAdelicData.character t x = ∏ p ∈ S, (family p).character t (x p) := by
  rw [FiniteAdelicData.character_eq_tprod]
  exact Cubic.ToricHeights.RestrictedProductFunctions.prod_eq_prod _
    (fun p => FiniteAdelicData.local_character_one p t) x S hS

theorem stage_integrand_eq (S : Finset Nat.Primes) (hthree : primeThree ∈ S)
    (s₀ σ : ℂ) (t : ℝ) (x : FiniteAdelicStages.Stage S) :
    integrand s₀ σ t (FiniteAdelicStages.inclusion S x) =
      ∏ p : S, localIntegrand (family p) s₀ σ t (x p) := by
  have hc : FiniteAdelicData.character t (FiniteAdelicStages.inclusion S x) =
      ∏ p : S, (family p).character t (x p) :=
    (character_eq_prod S _ (fun p hp => x.property hp) t).trans
      (Finset.prod_coe_sort S _).symm
  rw [integrand, FiniteAdelicStages.stage_height_eq S hthree, hc]
  change (∏ p : S, localCutoffHeight p s₀ σ (x p)) *
    (Circle.coeHom (∏ p : S, (family p).character t (x p)))⁻¹ = _
  rw [map_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  rfl

theorem integral_stage (S : Finset Nat.Primes) (hthree : primeThree ∈ S)
    (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    (∫ x : FiniteAdelicStages.Stage S,
      integrand s₀ σ t (FiniteAdelicStages.inclusion S x) ∂FiniteAdelicStages.measure S) =
      ∏ p ∈ S, localFourier (family p) s₀ σ t := by
  have hI := Integrable.fintype_prod_dep
    (fun p : S => localCalculation.integrable p s₀ σ t hσ)
  have hmap : AEStronglyMeasurable (fun x : ∀ p : S, (family p).Carrier =>
      ∏ p : S, localIntegrand (family p) s₀ σ t (x p))
      ((FiniteAdelicStages.measure S).map (FiniteAdelicStages.projection S)) := by
    rw [(FiniteAdelicStages.projection_measurePreserving S).map_eq]
    exact hI.aestronglyMeasurable
  simp_rw [stage_integrand_eq S hthree]
  change (∫ x : FiniteAdelicStages.Stage S, (fun y : ∀ p : S, (family p).Carrier =>
    ∏ p : S, localIntegrand (family p) s₀ σ t (y p))
      (FiniteAdelicStages.projection S x) ∂FiniteAdelicStages.measure S) = _
  rw [← integral_map (FiniteAdelicStages.projection_measurePreserving S).measurable.aemeasurable
    hmap, (FiniteAdelicStages.projection_measurePreserving S).map_eq,
    integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort S (fun p : Nat.Primes => localFourier (family p) s₀ σ t)

theorem integral_stageSet (S : Finset Nat.Primes) (hthree : primeThree ∈ S)
    (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    (∫ x in FiniteAdelicStages.stageSet S, integrand s₀ σ t x ∂finiteMeasure) =
      ∏ p ∈ S, localFourier (family p) s₀ σ t := by
  have hE := (RestrictedProductHaar.isOpenEmbedding_inclusion
    (fun p => (family p).Carrier) (fun p => (family p).maxCompact) S).measurableEmbedding
  have hmap : (FiniteAdelicStages.measure S).map (FiniteAdelicStages.inclusion S) =
      finiteMeasure.restrict (FiniteAdelicStages.stageSet S) := hE.map_comap finiteMeasure
  rw [← hmap, hE.integral_map]
  exact integral_stage S hthree s₀ σ t hσ

/-- Fubini and exhaustion identify the actual restricted-product integral.
The exceptional local measure factor at three remains in the product. -/
theorem integral_eq_product (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    (∫ x, integrand s₀ σ t x ∂finiteMeasure) = finiteFourier family s₀ σ t := by
  have ht := tendsto_setIntegral_of_monotone
    (fun n => (FiniteAdelicStages.isOpen_stageSet
      (FiniteAdelicStages.exhaustionPrimes n)).measurableSet)
    (FiniteAdelicStages.stageSet_mono.comp FiniteAdelicStages.exhaustionPrimes_mono)
    (show IntegrableOn (integrand s₀ σ t)
      (⋃ n, FiniteAdelicStages.stageSet (FiniteAdelicStages.exhaustionPrimes n)) finiteMeasure by
        rw [FiniteAdelicStages.iUnion_stageSet]
        exact (integrable s₀ σ t hσ).integrableOn)
  simp only [FiniteAdelicStages.iUnion_stageSet, Measure.restrict_univ] at ht
  have hp := (finiteFourier_claim.finite_convergent s₀ σ t hσ).hasProd.comp
    FiniteAdelicStages.exhaustionPrimes_tendsto
  apply tendsto_nhds_unique ht
  convert hp using 1
  funext n
  exact integral_stageSet _ (by simp) s₀ σ t hσ

end Cubic.PoissonSummation.FiniteAdelicFourierIntegral
