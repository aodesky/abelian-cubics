import Cubic.Counting.CountPolynomialNormalization
import Cubic.Counting.HeightCoefficientSum
import Cubic.Counting.AsymptoticConstantsAssembly
import CubicTargets.Counting.GeneralMonic

/-!
# Proof of `eqn:dSummatoryForGeneralTrace`

The label occurs inside the proof of `thm:asymptoticPolynomialCount`.
This file instantiates the supporting direct summatory estimate for the global count.

This is `eqn:dSummatoryForGeneralTrace`,
`Σ_{n ≤ X} d_n = (c₂/4) X log X + (c₁/2 − c₂/4) X + O_ε(X^{1/2+ε})`, rewritten with the
constants of the trace-one count: `C = (3/4) c₂` and `D = (3/4)(c₁ − c₂/2)`, so that
`c₂/4 = C/3` and `c₁/2 − c₂/4 = 2D/3`.
-/

noncomputable section

namespace Cubic.Counting.DSummatory

open Cubic.Counting.GeneralMonicData Cubic.Counting.AsymptoticConstantsData

theorem coefficient_estimate
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.GeneralMonic.DSummatoryCoefficients := by
  obtain ⟨Z, F, γ, c₂, c₁, hE⟩ := Cubic.PoissonSummation.leadingTerms_expansion hPoisson
  have hC : c₂ / 4 = ((Cconst / 3 : ℝ) : ℂ) := by
    have h := AsymptoticConstants.leading_original hE
    rw [leadingFromLaurent] at h
    simp only [Cconst]; push_cast
    linear_combination h / 3
  have hD : c₁ / 2 - c₂ / 4 = ((2 * Dconst / 3 : ℝ) : ℂ) := by
    have h := AsymptoticConstantsAssembly.secondary_from_laurent hE
    rw [secondaryFromLaurent] at h
    simp only [Dconst]; push_cast at h ⊢
    linear_combination 2 * h / 3
  intro ε hε
  obtain ⟨K, X₀, hK⟩ :=
    Cubic.Counting.HeightCoefficientSum.coefficient_estimate hPoisson hCN
      Z F γ c₂ c₁ hE ε hε
  refine ⟨K, X₀, fun X hX => ?_⟩
  have h := hK X hX
  rw [show c₂ / 4 * X * Real.log X + (c₁ / 2 - c₂ / 4) * X =
      ((Cconst / 3 * X * Real.log X + 2 * Dconst / 3 * X : ℝ) : ℂ) by
    push_cast at hC hD ⊢
    linear_combination (X * Real.log X : ℂ) * hC + (X : ℂ) * hD] at h
  simp only
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  simpa [d] using h

/-- The labelled formula in the current manuscript. -/
theorem «eqn:dSummatoryForGeneralTrace»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.GeneralMonic.DSummatoryClaim := by
  have he := coefficient_estimate hPoisson hCN
  intro ε hε
  obtain ⟨K, X₀, hK⟩ := he ε hε
  refine ⟨K, X₀, fun X hX => ?_⟩
  simpa only [CountPolynomialNormalization.summatory_main X] using hK X hX

end Cubic.Counting.DSummatory
