import Cubic.Counting.HeightCoefficientMeanValue
import CubicTargets.Counting.HeightMeanBound

/-! The labelled integral comparison follows solely from the bounded Euler
correction. The separate half-plane mean estimate remains a supporting result. -/
noncomputable section
namespace Cubic.Counting.HeightMeanBound
open Complex MeasureTheory Set Filter
open Cubic.Counting.HeightCoefficientData Cubic.Counting.HeightCoefficientMeanValue

theorem «eqn:heightMeanBound» : CubicTargets.Counting.HeightMeanBound.Claim := by
  intro D F γ c₂ c₁ hExp δ hδ
  obtain ⟨C, hC⟩ := HeightCoefficientBounds.correction_bounded (1 / 2 + δ) (by linarith)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (1 / 2 + δ : ℝ) (by simp))
  refine ⟨C, hC0, fun σ hσ U hU => ?_⟩
  have heq : (∫ t in U..2 * U, ‖F (2 * ((σ : ℂ) + t * I))‖) =
      ∫ t in U..2 * U, ‖calZ ((σ : ℂ) + t * I)‖ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    dsimp only
    rw [← HeightCoefficientContinuation.calZ_eq hExp _ (by simp; linarith) (fun h => by
      have := congrArg Complex.im h; simp at this; linarith [ht.1])]
  rw [heq]
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

end Cubic.Counting.HeightMeanBound
