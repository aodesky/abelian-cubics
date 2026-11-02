import Cubic.PoissonSummation.HeightZetaContinuationFormula
import Cubic.PoissonSummation.HeightZetaFullRegion
import Cubic.PoissonSummation.HeightZetaContourIntegral
import Cubic.PoissonSummation.PoissonAdelicApplication
import CubicTargets.PoissonSummation.HeightZetaFunctionFormula
import CubicTargets.PoissonSummation.PoissonIntegral

/-!
# Assembly of the full theorem after its initial-region height identity

All conclusions of the concrete theorem are retained. The sole prerequisite
of the first assembly is the exact height-series Euler identity in the initial
region. The second assembly now derives this identity from the full Poisson
lemma by the proved contour evaluation, including cancellation of the local
factor `1/6`. The final assembly uses the actual adelic application of general
Poisson. These helpers retain their prerequisites explicitly. The labelled
proof in `HeightZetaFunctionFormula` uses the assumed Poisson package including
normalized-dual existence, so its only premise is that general analytic input.
-/

namespace Cubic.PoissonSummation.HeightZetaCompletion

open AdelicHeightZetaData HeightZetaFormulaData

theorem claim_of_initial_region_formula
    (hformula : ∀ s₀ σ : ℂ, 0 < s₀.re → 1 < σ.re →
      heightZeta s₀ σ = eulerExpression (parameter s₀ σ)) :
    CubicTargets.PoissonSummation.HeightZetaFunctionFormula.Claim where
  series_absolute := HeightZetaFullRegion.series_absolute
  inert_product_absolute := HeightZetaEulerExtraction.inert_product_absolute
  split_product_absolute := HeightZetaEulerExtraction.split_product_absolute
  euler_formula := HeightZetaFullRegion.euler_formula_of_initial_region hformula
  meromorphic_continuation := by
    refine ⟨HeightZetaContinuation.value, HeightZetaContinuation.meromorphicOn_value, ?_⟩
    intro s₀ σ h
    rw [HeightZetaContinuationFormula.continuation_eq_eulerExpression _
      ((HeightZetaFullRegion.region_iff s₀ σ).mp h)]
    exact HeightZetaFullRegion.euler_formula_of_initial_region hformula s₀ σ h

/-- The initial-region formula, following Poisson by the residue calculation.
The full Poisson lemma is an explicit premise of this assembly helper. -/
theorem initial_region_formula_of_poisson
    (hPoisson : CubicTargets.PoissonSummation.PoissonIntegral.Claim)
    (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 1 < σ.re) :
    heightZeta s₀ σ = eulerExpression (parameter s₀ σ) := by
  have hz : 1 < (parameter s₀ σ).re := by
    simp only [parameter, Complex.add_re, Complex.div_ofNat_re]
    linarith
  rw [hPoisson.poisson_equality s₀ σ h₀ hσ,
    HeightZetaContourIntegral.integral_eq_finite_value s₀ σ h₀ hσ,
    HeightZetaEulerExtraction.eulerExpression_eq_unscaled_product _ hz,
    FiniteEulerProduct.value]
  ring

/-- Every assertion of the height-zeta theorem follows from the full Poisson
lemma, through the paper's contour, Euler-product and parameter-shift steps. -/
theorem claim_of_poisson
    (hPoisson : CubicTargets.PoissonSummation.PoissonIntegral.Claim) :
    CubicTargets.PoissonSummation.HeightZetaFunctionFormula.Claim :=
  claim_of_initial_region_formula (initial_region_formula_of_poisson hPoisson)

section AdelicApplication

open MeasureTheory AdelicRationalCharacter AdelicQuotientMeasure
open scoped Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData AdelicQuotientMeasure
  AdelicFourierSpectrum

/-- The full original-series theorem through the paper's adelic Poisson route.
The remaining general analytic inputs are visible: the assumed black box
and a full dual Haar measure satisfying quotient Fourier inversion. -/
theorem claim_of_general_poisson
    (hPoisson : CubicTargets.PoissonSummation.PoissonAE.BlackBox)
    (ν : Measure (PontryaginDual AutomorphicQuotient)) [ν.IsHaarMeasure] [ν.Regular]
    (hInv : ∀ F : AutomorphicQuotient → ℂ,
      let Fhat := fun χ : PontryaginDual AutomorphicQuotient =>
        ∫ q, F q * (χ q : ℂ)⁻¹ ∂quotientMeasure
      Integrable F quotientMeasure → Integrable Fhat ν →
        ∀ᵐ q ∂quotientMeasure, F q = ∫ χ, Fhat χ * (χ q : ℂ) ∂ν) :
    CubicTargets.PoissonSummation.HeightZetaFunctionFormula.Claim :=
  claim_of_poisson (PoissonAdelicApplication.claim_of_blackBox ν hInv hPoisson)

end AdelicApplication

end Cubic.PoissonSummation.HeightZetaCompletion
