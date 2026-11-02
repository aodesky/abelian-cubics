import Cubic.PoissonSummation.HeightParameterShift
import Cubic.PoissonSummation.HeightZetaFormulaData
import Cubic.PoissonSummation.AdelicHeightZetaConvergence

/-!
# Extending the height series to the full convergence region

This implements the principal-divisor step of `thm:heightZetaFunctionFormula2`.
Choose `1 < ρ < Re(s₀/2+σ)` and shift to `(s₀+2σ-2ρ,ρ,ρ)`.
The proved rational product formula identifies each original height summand,
so the already proved convergence lemma applies. The Euler formula is
transported here from the initial region, where it is proved separately.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaFullRegion

open AdelicHeightZetaData HeightZetaFormulaData HeightParameterShift
open scoped Cubic.QuadraticCorrespondence.RationalQuotientGroup

theorem parameter_re (s₀ σ : ℂ) : (parameter s₀ σ).re = s₀.re / 2 + σ.re := by
  simp [parameter]

theorem region_iff (s₀ σ : ℂ) : 2 < (s₀ + 2 * σ).re ↔ 1 < (parameter s₀ σ).re := by
  rw [parameter_re]
  norm_num [Complex.add_re, Complex.mul_re]
  constructor <;> intro h <;> linarith

/-- The norm-character shift leaves the spectral parameter unchanged. -/
theorem parameter_shift (s₀ σ a : ℂ) :
    parameter (s₀ + 2 * a) (σ - a) = parameter s₀ σ := by
  unfold parameter
  ring

/-- The paper's choice of a real `ρ` places both shifted coordinates in the initial region. -/
theorem exists_initial_shift (s₀ σ : ℂ) (h : 2 < (s₀ + 2 * σ).re) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ < (parameter s₀ σ).re ∧
      0 < (s₀ + 2 * (σ - (ρ : ℂ))).re ∧ 1 < (σ - (σ - (ρ : ℂ))).re := by
  obtain ⟨ρ, hρ, hz⟩ := exists_between ((region_iff s₀ σ).mp h)
  refine ⟨ρ, hρ, hz, ?_, ?_⟩
  · rw [parameter_re] at hz
    norm_num [Complex.add_re, Complex.mul_re, Complex.sub_re]
    linarith
  · simpa only [sub_sub_cancel, Complex.ofReal_re] using hρ

/-- Absolute convergence of the original height series throughout the full claimed region.
This is one assertion of the theorem, not its Euler formula or continuation. -/
theorem series_absolute (s₀ σ : ℂ) (h : 2 < (s₀ + 2 * σ).re) :
    Summable (fun P : IntegralRationalPoints => ‖zetaTerm s₀ σ P‖) := by
  obtain ⟨ρ, _, _, h₀, hσ⟩ := exists_initial_shift s₀ σ h
  simpa only [zetaTerm_shift] using
    «lemma:heightZetaConvergence».zeta_absolute (s₀ + 2 * (σ - (ρ : ℂ)))
      (σ - (σ - (ρ : ℂ))) h₀ hσ

/-- Once the paper's contour argument proves the formula in its initial region,
the same principal-divisor shift extends that exact formula to the full region. -/
theorem euler_formula_of_initial_region
    (hformula : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
      heightZeta s₀ σ = eulerExpression (parameter s₀ σ))
    (s₀ σ : ℂ) (h : 2 < (s₀ + 2 * σ).re) :
    heightZeta s₀ σ = eulerExpression (parameter s₀ σ) := by
  obtain ⟨ρ, _, _, h₀, hσ⟩ := exists_initial_shift s₀ σ h
  simpa only [heightZeta_shift, parameter_shift] using
    hformula (s₀ + 2 * (σ - (ρ : ℂ))) (σ - (σ - (ρ : ℂ))) h₀ hσ

end Cubic.PoissonSummation.HeightZetaFullRegion
