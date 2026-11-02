import Cubic.Counting.CountPolynomialNormalization
import Cubic.Counting.RSummatory
import Cubic.Counting.TraceZeroSplitCount

/-!
# Proof of `prop:traceZeroAsymptotic`

Following the paper:

* `lemma:traceZeroCoefficients` and `eqn:dSummatoryForGeneralTrace` give
  `Σ_{N ≤ X} r(N) = (5C/6) X log X + (5D/3 - (3C/4) log 3) X + O_ε(X^{1/2+ε})`
  (`RSummatory.sum_r_expansion`, using `Σ_{e ≥ 1} 3^{-e} = 1/2`, `Σ_{e ≥ 1} e 3^{-e} = 3/4`).
* A cubic `t³ - Nt + c`, `N ≥ 1`, has square discriminant exactly when it is cyclic or split,
  and not both (`TraceZeroSplitting.A₀_add_split`); "a reducible monic cubic with square
  discriminant splits completely".
* By Burnside's lemma over the `S₃`-orbits of roots `(x, y, -x-y)`,
  `#{split t³ - Nt + c : 1 ≤ N ≤ X} = πX/(3√3) + O(X^{1/2})`
  (`TraceZeroSplitCount.split_count`).

Subtracting the split cubics proves the proposition.
-/

noncomputable section

namespace Cubic.Counting.TraceZeroAsymptotic

open Cubic.Counting.GeneralMonicData Cubic.Counting.TraceZeroSplitting

theorem coefficient_estimate
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.GeneralMonic.TraceZeroAsymptoticCoefficients := by
  refine ⟨traceZeroSet_finite, fun ε hε => ?_⟩
  obtain ⟨K₁, X₁, h₁⟩ := RSummatory.sum_r_expansion hPoisson hCN ε hε
  obtain ⟨K₂, h₂⟩ := TraceZeroSplitCount.split_count
  refine ⟨K₁ + |K₂|, max X₁ 1, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hr := h₁ X (le_trans (le_max_left _ _) hX)
  have hs := h₂ X hX1
  have hsum : (A₀ X : ℝ) + Nat.card (splitSet X) = ∑ N ∈ Finset.Icc (1 : ℤ) ⌊X⌋, (r N : ℝ) := by
    exact_mod_cast A₀_add_split X
  have hsq : √X ≤ X ^ (1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hK₂ : K₂ * √X ≤ |K₂| * X ^ (1 / 2 + ε) :=
    (mul_le_mul_of_nonneg_right (le_abs_self K₂) (Real.sqrt_nonneg X)).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg K₂))
  simp only at hr ⊢
  rw [abs_le] at hr hs ⊢
  constructor <;> nlinarith

/-- The labelled formula in the current manuscript. -/
theorem «prop:traceZeroAsymptotic»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.GeneralMonic.TraceZeroAsymptoticClaim := by
  obtain ⟨hf, he⟩ := coefficient_estimate hPoisson hCN
  refine ⟨hf, ?_⟩
  intro ε hε
  obtain ⟨K, X₀, hK⟩ := he ε hε
  refine ⟨K, X₀, fun X hX => ?_⟩
  simpa only [CountPolynomialNormalization.trace_zero_main X] using hK X hX

end Cubic.Counting.TraceZeroAsymptotic
