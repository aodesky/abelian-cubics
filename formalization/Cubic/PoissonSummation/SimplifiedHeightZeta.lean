import Cubic.PoissonSummation.HeightZetaFunctionFormula
import Cubic.PoissonSummation.HeightZetaContinuationFormula
import Cubic.PoissonSummation.QuadraticDedekindFactorization
import CubicTargets.PoissonSummation.SimplifiedHeightZeta

/-!
# `lemma:simplifiedZ(s)`: the height zeta function through `ζ_{ℚ(√-3)}`

Proof correspondence with the paper:

* The Euler formula `Z(s) = (1-3^{-z}) ζ(z) ∏_q (1+q^{-z})^{-1} ∏_p (1+3p^{-z}(1-p^{-z})^{-1})`
  is `thm:heightZetaFunctionFormula2`, proved relative to the assumed Poisson
  black box; this is the only assumption.
* Direct comparison of the split and inert Euler factors is carried out in
  `HeightZetaContinuationFormula.continuation_eq_eulerExpression`, which rewrites
  the Euler expression as `((1-3^{-z}) ζ(z) L(z,χ))^2` times the two correction
  products on `Re z > 1`, using mathlib's Euler products for `ζ` and `L(·,χ)`.
* `ζ(z) L(z,χ) = ζ_{ℚ(√-3)}(z)` on `Re z > 1` is
  `QuadraticDedekindFactorization.factorization`, for mathlib's ideal-counting
  Dedekind zeta function.
* `HeightZetaCorrectionProduct` bounds the deviations by `5 p^(-2σ)` on
  `Re z ≥ σ > 1/2`, proves absolute and locally uniform convergence, and hence
  holomorphy of `R`. This direct argument supplies the correction factor in
  `HeightZetaContinuation.meromorphicOn_value`.
-/

noncomputable section

namespace Cubic.PoissonSummation

open AdelicHeightZetaData HeightZetaFormulaData FiniteEulerProduct
open CubicTargets.PoissonSummation.SimplifiedHeightZeta

private theorem parameter_re_gt_one {s₀ σ : ℂ} (h : 2 < (s₀ + 2 * σ).re) :
    1 < (parameter s₀ σ).re := by
  simp only [parameter, Complex.add_re, Complex.div_ofNat_re]
  simp only [Complex.add_re, Complex.mul_re] at h
  norm_num at h
  linarith

/-- The continuation of `ζ_{ℚ(√-3)}` used here: `ζ(z) L(z,χ)`. -/
private def dedekindContinuation (u : ℂ) : ℂ :=
  riemannZeta u * DirichletCharacter.LFunction QuadraticDirichletCharacter.character u

private theorem simplified_eq_value (z : ℂ) :
    simplified dedekindContinuation z = HeightZetaContinuation.value z := by
  simp only [simplified, dedekindContinuation, HeightZetaContinuation.value,
    HeightZetaCorrectionProduct.value, HeightZetaCorrectionProduct.inert,
    HeightZetaCorrectionProduct.split]
  ring

theorem «lemma:simplifiedZ(s)»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    Claim := by
  have hF := «thm:heightZetaFunctionFormula2» hPoisson
  have hanchor : ∀ u : ℂ, 1 < u.re → dedekindContinuation u =
      NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E u :=
    fun u hu => (QuadraticDedekindFactorization.factorization u hu).symm
  have hcont : ∀ s₀ σ : ℂ, 2 < (s₀ + 2 * σ).re →
      heightZeta s₀ σ = simplified dedekindContinuation (parameter s₀ σ) := by
    intro s₀ σ h
    rw [hF.euler_formula s₀ σ h, simplified_eq_value,
      HeightZetaContinuationFormula.continuation_eq_eulerExpression _
        (parameter_re_gt_one h)]
  refine
    { series_absolute := hF.series_absolute
      inert_product_absolute := HeightZetaCorrectionProduct.absolute_inert
      split_product_absolute := HeightZetaCorrectionProduct.absolute_split
      inert_product_locally_uniform := HeightZetaCorrectionProduct.locally_uniform_inert
      split_product_locally_uniform := HeightZetaCorrectionProduct.locally_uniform_split
      correction_holomorphic := HeightZetaCorrectionProduct.differentiableOn_value
      formula := ?_
      meromorphic_continuation := ?_ }
  · intro s₀ σ h
    have hz := parameter_re_gt_one h
    rw [hcont s₀ σ h]
    simp only [simplified, hanchor _ hz]
  · refine ⟨dedekindContinuation, hanchor, ?_, ?_, hcont⟩
    · intro u hu
      change (1 / 2 : ℝ) < u.re at hu
      exact (HeightZetaContinuation.meromorphicAt_riemannZeta u (by linarith)).fun_mul
        (QuadraticDirichletCharacter.differentiable_LFunction.analyticAt u).meromorphicAt
    · have he : simplified dedekindContinuation = HeightZetaContinuation.value :=
        funext simplified_eq_value
      rw [he]
      exact HeightZetaContinuation.meromorphicOn_value

end Cubic.PoissonSummation
