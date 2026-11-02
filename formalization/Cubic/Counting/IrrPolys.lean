import Cubic.Counting.CountPolynomialNormalization
import Cubic.Counting.HeightCoefficientSum
import Cubic.Counting.AsymptoticConstantScaling
import Cubic.Counting.WeightedCount
import CubicTargets.Counting.IrrPolys

/-!
# Proof of `eqn:irrPolys`

The paper: "Apply `eqn:weightedPolynomialCount` and `eqn:ellipseLatticeCount` with
`H = √X`. Equation `eqn:dSummatoryForGeneralTrace` then gives `eqn:irrPolys`. Here the `O(√X)`
lattice-point error is absorbed by the displayed remainder."
-/

noncomputable section

namespace Cubic.Counting.IrrPolys

open Cubic.Counting.AsymptoticConstantScaling
open CubicTargets.Counting.WeightedPolynomialCount (countSet)

theorem of_heightCoefficientSum (hHCS : CubicTargets.Counting.HeightCoefficientSum.CoefficientClaim) :
    CubicTargets.Counting.IrrPolys.CoefficientClaim := by
  intro D F γ c₂ c₁ hE ε hε
  obtain ⟨K, X₀, hK⟩ := hHCS D F γ c₂ c₁ hE ε hε
  obtain ⟨K₂, hK₂⟩ := (Cubic.Counting.EllipseLatticeCount.«eqn:ellipseLatticeCount»).2
  refine ⟨(1 / 2) * |K| + (1 / 6) * |K₂|, max X₀ 1, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  set S : ℝ := Real.sqrt X with hS
  have hS1 : 1 ≤ S := by rw [hS, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hSX : S ^ 2 = X := Real.sq_sqrt (by linarith)
  obtain ⟨hfin, hw⟩ := Cubic.Counting.WeightedCount.exact_count S hS1
  refine ⟨hfin, ?_⟩
  rw [hSX] at hw
  have e1 := hK X hXX₀
  have e2 := hK₂ S hS1
  rw [hSX] at e2
  set N : ℝ := (Nat.card (CubicTargets.Counting.EllipseLatticeCount.latticePoints S) : ℝ)
  set Sd : ℂ := ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
    (Cubic.PoissonSummation.HeightCountingData.count n : ℂ) with hSd
  -- the identity: count − main = ½(Σ − coefficient main) − ⅙(N − area)
  have hid : (Nat.card (countSet S) : ℂ) -
      (c₂ / 8 * X * Real.log X +
        (c₁ / 4 - c₂ / 8 - ((Real.pi / (9 * Real.sqrt 3) : ℝ) : ℂ)) * X) =
      (1 / 2 : ℂ) * (Sd - coefficientMainTerm c₂ c₁ X) -
        (1 / 6 : ℂ) * ((N - 2 * Real.pi / (3 * Real.sqrt 3) * X : ℝ) : ℂ) := by
    have hw' : (Nat.card (countSet S) : ℂ) = (1 / 2 : ℂ) * Sd - (1 / 6 : ℂ) * (N : ℂ) := by
      have h := congrArg (fun r : ℝ => (r : ℂ)) hw
      simp only at h
      rw [hSd]
      push_cast at h ⊢
      exact h
    have hsplit := split_subtraction c₂ c₁ X
    simp only [toricPolynomialMainTerm] at hsplit
    rw [hw']
    have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne'
    push_cast
    rw [coefficientMainTerm] at hsplit ⊢
    field_simp
    field_simp at hsplit
    linear_combination (-(1 : ℂ)) * hsplit
  rw [hid]
  have hXE : Real.sqrt X ≤ X ^ (1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hXE0 : 0 ≤ X ^ (1 / 2 + ε) := by positivity
  have b1 : ‖(1 / 2 : ℂ) * (Sd - coefficientMainTerm c₂ c₁ X)‖ ≤ (1 / 2) * |K| * X ^ (1 / 2 + ε) := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact e1.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hXE0)
  have b2 : ‖(1 / 6 : ℂ) * ((N - 2 * Real.pi / (3 * Real.sqrt 3) * X : ℝ) : ℂ)‖ ≤
      (1 / 6) * |K₂| * X ^ (1 / 2 + ε) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, show ‖(1 / 6 : ℂ)‖ = 1 / 6 by norm_num,
      mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact e2.trans (mul_le_mul (le_abs_self K₂) hXE (Real.sqrt_nonneg _) (abs_nonneg _))
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ (1 / 2) * |K| * X ^ (1 / 2 + ε) + (1 / 6) * |K₂| * X ^ (1 / 2 + ε) := add_le_add b1 b2
    _ = ((1 / 2) * |K| + (1 / 6) * |K₂|) * X ^ (1 / 2 + ε) := by ring

/-- `eqn:irrPolys`, relative to the black-box hypotheses of `eqn:dSummatoryForGeneralTrace`. -/
theorem coefficient_estimate
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.IrrPolys.CoefficientClaim :=
  of_heightCoefficientSum
    (Cubic.Counting.HeightCoefficientSum.coefficient_estimate hPoisson hCN)

/-- The labelled formula, with its main term expressed using `Q`. -/
theorem «eqn:irrPolys»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.IrrPolys.Claim := by
  intro D F μ c₂ c₁ h ε hε
  obtain ⟨K, X₀, hK⟩ := coefficient_estimate hPoisson hCN D F μ c₂ c₁ h ε hε
  refine ⟨K, X₀, fun X hX => ?_⟩
  simpa only [CountPolynomialNormalization.irreducible_main h X] using hK X hX

end Cubic.Counting.IrrPolys
