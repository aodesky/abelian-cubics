import Cubic.PoissonSummation.FiniteAdelicExhaustion
import Cubic.PoissonSummation.ArchimedeanFourier

/-!
# Spatial integrability in `lemma:heightZetaConvergence`

Follow the paper's first argument: integrate on increasing finite-place stages,
replace the parameters by their real parts for the absolute-value integral,
and apply monotone convergence and convergence of the finite Euler product.
The resulting finite-place integrability combines with the proved archimedean
integral. Periodization convergence is a separate remaining part of the lemma.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicSpatialIntegrability

open MeasureTheory Set Filter
open Cubic.QuadraticCorrespondence
open QuotientFiniteFourierProduct FiniteEulerProduct AdelicHeightZetaData
open CubicTargets.PoissonSummation.FiniteFourierProduct
open scoped RestrictedProductHaar AdelicHeightZetaData ArchimedeanHaarData ENNReal Topology
  RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

theorem lintegral_stage_norm (S : Finset Nat.Primes) (hthree : primeThree ∈ S)
    (s₀ σ : ℂ) (hσ : 1 < σ.re) :
    (∫⁻ x in FiniteAdelicStages.stageSet S, ‖finiteCutoffHeight s₀ σ x‖ₑ ∂finiteMeasure) =
      ENNReal.ofReal (∏ p ∈ S, localFourier (family p) s₀.re σ.re 0).re := by
  have hE := (RestrictedProductHaar.isOpenEmbedding_inclusion
    (fun p => (family p).Carrier) (fun p => (family p).maxCompact) S).measurableEmbedding
  have hmap : (FiniteAdelicStages.measure S).map (FiniteAdelicStages.inclusion S) =
      finiteMeasure.restrict (FiniteAdelicStages.stageSet S) := hE.map_comap finiteMeasure
  rw [← hmap, hE.lintegral_map,
    ← ofReal_integral_norm_eq_lintegral_enorm
      (FiniteAdelicStages.integrable_stage_height S hthree s₀ σ hσ)]
  congr 1
  have hcomplex :
      ((∫ x : FiniteAdelicStages.Stage S,
        ‖finiteCutoffHeight s₀ σ (FiniteAdelicStages.inclusion S x)‖
        ∂FiniteAdelicStages.measure S : ℝ) : ℂ) =
        ∏ p ∈ S, localFourier (family p) s₀.re σ.re 0 := by
    rw [← integral_complex_ofReal]
    simp_rw [norm_finiteCutoffHeight]
    exact FiniteAdelicStages.integral_stage_height S hthree s₀.re σ.re (by simpa using hσ)
  exact (congrArg Complex.re hcomplex)

/-- Monotone convergence identifies the genuine finite adelic absolute integral. -/
theorem lintegral_finite_norm (s₀ σ : ℂ) (hσ : 1 < σ.re) :
    (∫⁻ x, ‖finiteCutoffHeight s₀ σ x‖ₑ ∂finiteMeasure) =
      ENNReal.ofReal (finiteFourier family s₀.re σ.re 0).re := by
  let a : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x in FiniteAdelicStages.stageSet (FiniteAdelicStages.exhaustionPrimes n),
      ‖finiteCutoffHeight s₀ σ x‖ₑ ∂finiteMeasure
  have hm : Monotone a := fun m n hmn => lintegral_mono_set
    (FiniteAdelicStages.stageSet_mono (FiniteAdelicStages.exhaustionPrimes_mono hmn))
  have hp := (finiteFourier_claim.finite_convergent s₀.re σ.re 0 (by simpa using hσ)).hasProd
  have ht := hp.comp FiniteAdelicStages.exhaustionPrimes_tendsto
  have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)
  have ha : Tendsto a atTop (𝓝 (ENNReal.ofReal (finiteFourier family s₀.re σ.re 0).re)) := by
    convert ht' using 1
    funext n
    exact lintegral_stage_norm _ (by simp) s₀ σ hσ
  rw [FiniteAdelicStages.lintegral_eq_iSup_stages]
  exact tendsto_nhds_unique (tendsto_atTop_iSup hm) ha

theorem finite_integrable (s₀ σ : ℂ) (hσ : 1 < σ.re) :
    Integrable (finiteCutoffHeight s₀ σ) finiteMeasure := by
  refine ⟨(measurable_finiteCutoffHeight s₀ σ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_finite_norm s₀ σ hσ]
  exact ENNReal.ofReal_lt_top

theorem infinite_integrable (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    Integrable (Cubic.ToricHeights.ArchimedeanQuotientLogarithm.inverseHeight s₀ σ)
      ArchimedeanHaar.measure := by
  open Cubic.ToricHeights.ArchimedeanQuotientLogarithm in
  have hmap : Integrable (ArchimedeanFourier.inverseHeight s₀ σ)
      (ArchimedeanHaar.measure.map coordinate) := by
    rw [ArchimedeanHaar.map_measure]
    exact ArchimedeanFourier.integrable_inverseHeight s₀ σ h₀ hσ
  have hcomp := hmap.comp_measurable
    Cubic.ToricHeights.ArchimedeanQuotientLogarithm.continuous_coordinate.measurable
  change Integrable (fun x => Cubic.ToricHeights.ArchimedeanQuotientLogarithm.inverseHeight s₀ σ x)
    ArchimedeanHaar.measure
  simpa only [Function.comp_def, ArchimedeanFourier.inverseHeight,
    Cubic.ToricHeights.ArchimedeanQuotientLogarithm.inverseHeight_eq] using hcomp

/-- The spatial assertion of the full paper lemma, on the actual adelic group. -/
theorem spatial_integrable (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    Integrable (cutoffHeight s₀ σ) AdelicHeightZetaData.measure := by
  have h := (infinite_integrable s₀ σ h₀ (lt_trans zero_lt_one hσ)).mul_prod
    (finite_integrable s₀ σ hσ)
  simpa only [← cutoffHeight_eq_components, AdelicHeightZetaData.measure] using h

end Cubic.PoissonSummation.AdelicSpatialIntegrability
