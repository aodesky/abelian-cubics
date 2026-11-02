import Cubic.PoissonSummation.HeightTranslation
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# From one absolutely summable value to continuous periodization

This is the convergence argument in `lemma:heightZetaConvergence`, conditional on
an absolutely summable value at a base point and the pointwise translation estimate.
It reuses mathlib's Weierstrass bound and continuity of locally uniform limits.
The application at the end proves the estimate for the existing support-function
height with arbitrary fixed finite factors and logarithmic shifts. The adelic
comparison and a summable base point are supplied in the proof of
`lemma:heightZetaConvergence`.
-/

noncomputable section

namespace Cubic.PoissonSummation.PeriodizationConvergence

open Filter Metric

variable {ι : Type*} (f : ι → ℝ → ℂ) (u₀ M : ℝ)

/-- The exponential comparison transfers absolute summability to every real point. -/
theorem summable_norm_at
    (hsum : Summable (fun i => ‖f i u₀‖))
    (hbound : ∀ i u, ‖f i u‖ ≤ Real.exp (M * |u - u₀|) * ‖f i u₀‖) (u : ℝ) :
    Summable (fun i => ‖f i u‖) :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hbound i u)
    (hsum.mul_left (Real.exp (M * |u - u₀|)))

/-- A fixed summable majorant on each closed interval around the base point. -/
theorem hasSumUniformlyOn_closedBall (hM : 0 ≤ M)
    (hsum : Summable (fun i => ‖f i u₀‖))
    (hbound : ∀ i u, ‖f i u‖ ≤ Real.exp (M * |u - u₀|) * ‖f i u₀‖) (R : ℝ) :
    HasSumUniformlyOn f (fun u => ∑' i, f i u) (closedBall u₀ R) := by
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum (hsum.mul_left (Real.exp (M * R)))
  intro i u hu
  have hu' : |u - u₀| ≤ R := by simpa only [mem_closedBall, Real.dist_eq] using hu
  exact (hbound i u).trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu' hM)) (norm_nonneg _))

/-- Local uniform convergence follows on arbitrary compact sets, with the same series. -/
theorem hasSumLocallyUniformly (hM : 0 ≤ M)
    (hsum : Summable (fun i => ‖f i u₀‖))
    (hbound : ∀ i u, ‖f i u‖ ≤ Real.exp (M * |u - u₀|) * ‖f i u₀‖) :
    HasSumLocallyUniformly f (fun u => ∑' i, f i u) := by
  apply hasSumLocallyUniformly_of_forall_compact
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall u₀
  exact (hasSumUniformlyOn_closedBall f u₀ M hM hsum hbound R).mono hR

/-- The locally uniform sum of the continuous summands is continuous. -/
theorem continuous_tsum (hM : 0 ≤ M)
    (hsum : Summable (fun i => ‖f i u₀‖))
    (hbound : ∀ i u, ‖f i u‖ ≤ Real.exp (M * |u - u₀|) * ‖f i u₀‖)
    (hcont : ∀ i, Continuous (f i)) : Continuous (fun u => ∑' i, f i u) := by
  apply (hasSumLocallyUniformly f u₀ M hM hsum hbound).continuous
  exact Frequently.of_forall fun s => continuous_finset_sum s (fun i _ => hcont i)

/-- Application to actual support-function heights with fixed complex factors and real shifts.
Only summability at one point is assumed; the uniform estimate is proved from the height.
The identification with the paper's rational-point periodization is made in the
proof of `lemma:heightZetaConvergence`. -/
theorem translated_height_series (s₀ σ : ℂ) (h₀ : 0 ≤ s₀.re) (hσ : 0 ≤ σ.re)
    (c : ι → ℂ) (r : ι → ℝ) (u₀ : ℝ)
    (hsum : Summable (fun i => ‖c i * ArchimedeanFourier.inverseHeight s₀ σ (r i + u₀)‖)) :
    (∀ u : ℝ, Summable (fun i => ‖c i * ArchimedeanFourier.inverseHeight s₀ σ (r i + u)‖)) ∧
    HasSumLocallyUniformly (fun i u => c i * ArchimedeanFourier.inverseHeight s₀ σ (r i + u))
      (fun u => ∑' i, c i * ArchimedeanFourier.inverseHeight s₀ σ (r i + u)) ∧
    Continuous (fun u => ∑' i, c i * ArchimedeanFourier.inverseHeight s₀ σ (r i + u)) := by
  let f : ι → ℝ → ℂ := fun i u => c i * ArchimedeanFourier.inverseHeight s₀ σ (r i + u)
  let M := max s₀.re (2 * σ.re)
  have hM : 0 ≤ M := le_trans h₀ (le_max_left _ _)
  have hbound : ∀ i u, ‖f i u‖ ≤ Real.exp (M * |u - u₀|) * ‖f i u₀‖ := fun i u =>
    ArchimedeanFourier.norm_mul_inverseHeight_translate_le s₀ σ h₀ hσ (c i) (r i) u u₀
  refine ⟨summable_norm_at f u₀ M hsum hbound,
    hasSumLocallyUniformly f u₀ M hM hsum hbound, ?_⟩
  apply continuous_tsum f u₀ M hM hsum hbound
  intro i
  exact continuous_const.mul ((ArchimedeanFourier.continuous_inverseHeight s₀ σ).comp
    (continuous_const.add continuous_id))

end Cubic.PoissonSummation.PeriodizationConvergence
