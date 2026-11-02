import Cubic.Counting.XiMeanValue
import Cubic.Counting.HeightCoefficientBounds
import Cubic.Counting.HeightCoefficientContinuation

/-!
The mean bound for the actual height Dirichlet series. On the bounded strip use
Lemma 11 and the bounded Euler correction; to the right of 2 use absolute
convergence. These are the two steps in the printed proof of Theorem 2.
-/

noncomputable section
namespace Cubic.Counting.HeightCoefficientMeanValue
open Complex MeasureTheory Set Filter
open Cubic.Counting.HeightCoefficientData
open CubicTargets.PoissonSummation.LeadingTerms

/-- The strip mean value of `|ζ_E|²` on the lines `1/2 + δ ≤ σ ≤ 2`. -/
def StripMean (δ η : ℝ) : Prop :=
  ∃ K : ℝ, ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → ∀ U : ℝ, 2 ≤ U →
    ∫ t in U..2 * U, ‖zetaE (σ + t * I)‖ ^ 2 ≤ K * U ^ (1 + η)

theorem calZ_continuousOn : ContinuousOn calZ HeightCoefficientContinuation.domain :=
  HeightCoefficientContinuation.calZ_differentiableOn.continuousOn

/-- The bounded Euler correction transfers the zeta mean to `𝒵` on the inner strip. -/
theorem calZ_mean {δ η : ℝ} (hδ : 0 < δ) (h : StripMean δ η) :
    ∃ K : ℝ, ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → ∀ U : ℝ, 2 ≤ U →
      ∫ t in U..2 * U, ‖calZ (σ + t * I)‖ ≤ K * U ^ (1 + η) := by
  obtain ⟨K, hK⟩ := h
  obtain ⟨C, hC⟩ := HeightCoefficientBounds.correction_bounded (1 / 2 + δ) (by linarith)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (1 / 2 + δ : ℝ) (by simp))
  refine ⟨C * K, fun σ hσ hσ2 U hU => ?_⟩
  have hmem : ∀ t ∈ Icc U (2 * U), ((σ : ℂ) + t * I) ∈ HeightCoefficientContinuation.domain := fun t ht =>
    ⟨by simp; linarith, by
      intro heq
      have hi := congrArg Complex.im heq
      simp at hi
      linarith [ht.1]⟩
  have hline : Continuous fun t : ℝ => (σ : ℂ) + t * I := by fun_prop
  have hZ : ContinuousOn (fun t : ℝ => ‖calZ ((σ : ℂ) + t * I)‖) (Icc U (2 * U)) :=
    (calZ_continuousOn.comp hline.continuousOn hmem).norm
  have hE : ContinuousOn (fun t : ℝ => ‖zetaE ((σ : ℂ) + t * I)‖ ^ 2) (Icc U (2 * U)) :=
    ((HeightCoefficientContinuation.zetaE_differentiableOn.continuousOn.comp
      hline.continuousOn hmem).norm).pow 2
  calc ∫ t in U..2 * U, ‖calZ (σ + t * I)‖
      ≤ ∫ t in U..2 * U, C * ‖zetaE (σ + t * I)‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (hZ.intervalIntegrable_of_Icc (by linarith))
          ((hE.const_smul C).intervalIntegrable_of_Icc (by linarith))
        intro t _
        rw [calZ, norm_mul, norm_pow, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply hC
        simp; linarith
    _ = C * ∫ t in U..2 * U, ‖zetaE (σ + t * I)‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ C * (K * U ^ (1 + η)) := mul_le_mul_of_nonneg_left (hK σ hσ hσ2 U hU) hC0
    _ = C * K * U ^ (1 + η) := by ring


/-- Absolute convergence at 2 bounds the series uniformly on `Re s ≥ 2`. -/
theorem calZ_bounded_right {D F : ℂ → ℂ} {γ c₂ c₁ : ℂ}
    (hE : Expansion D F γ c₂ c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 2 ≤ s.re → ‖calZ s‖ ≤ C := by
  let f : ℕ → ℂ := fun n => (d n : ℂ)
  have hsum : LSeriesSummable f (2 : ℂ) :=
    HeightCoefficientContinuation.LSeries_summable 2 (by norm_num)
  refine ⟨∑' n, ‖LSeries.term f 2 n‖, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro s hs
  have hss : LSeriesSummable f s :=
    HeightCoefficientContinuation.LSeries_summable s (by linarith)
  rw [← HeightCoefficientContinuation.LSeries_eq hE s (by linarith)]
  exact (norm_tsum_le_tsum_norm hss.norm).trans
    (hss.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f (by simpa using hs) n)
      hsum.norm)

/-- The full half-plane estimate, including the absolutely convergent region. -/
theorem calZ_mean_halfPlane
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox)
    {D F : ℂ → ℂ} {γ c₂ c₁ : ℂ} (hE : Expansion D F γ c₂ c₁)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K : ℝ, ∀ σ : ℝ, 1 / 2 + ρ ≤ σ → ∀ U : ℝ, 2 ≤ U →
      ∫ t in U..2 * U, ‖calZ (σ + t * I)‖ ≤ K * U ^ (1 + ρ) := by
  obtain ⟨K, hK⟩ := calZ_mean hρ
    (Cubic.Counting.XiMeanValue.inner_strip hCN ρ hρ ρ hρ)
  obtain ⟨C, hC0, hC⟩ := calZ_bounded_right hE
  refine ⟨max K C, fun σ hσ U hU => ?_⟩
  by_cases hσ2 : σ ≤ 2
  · exact (hK σ hσ hσ2 U hU).trans
      (mul_le_mul_of_nonneg_right (le_max_left K C) (by positivity))
  have hline : Continuous fun t : ℝ => (σ : ℂ) + t * I := by fun_prop
  have hmem : ∀ t ∈ Icc U (2 * U), ((σ : ℂ) + t * I) ∈ HeightCoefficientContinuation.domain := by
    intro t ht
    refine ⟨by simp; linarith, ?_⟩
    intro heq
    have hr := congrArg Complex.re heq
    simp at hr
    linarith
  have hcont := (calZ_continuousOn.comp hline.continuousOn hmem).norm
  calc ∫ t in U..2 * U, ‖calZ (σ + t * I)‖
      ≤ ∫ _t in U..2 * U, C := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (hcont.intervalIntegrable_of_Icc (by linarith)) (intervalIntegrable_const)
        intro t _
        exact hC _ (by simp; linarith)
    _ = C * U := by simp [intervalIntegral.integral_const]; ring
    _ ≤ C * U ^ (1 + ρ) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ U)
          (by linarith : (1 : ℝ) ≤ 1 + ρ)
    _ ≤ max K C * U ^ (1 + ρ) :=
        mul_le_mul_of_nonneg_right (le_max_right K C) (by positivity)

end Cubic.Counting.HeightCoefficientMeanValue
