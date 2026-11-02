import Cubic.Introduction.CubeIdealEuler
import Cubic.Introduction.IdealHeightSeries
import Cubic.Counting.CountPolynomialNormalization

/-! The two Laurent coefficients after removing the ramified ideal factor.
The comparison with the paper's constants uses the arithmetic height-series
identity, with no Poisson hypothesis. -/

noncomputable section

namespace Cubic.Introduction.CubeIdealMainTerm

open Cubic.PoissonSummation Cubic.Counting
open CubeIdealEuler

abbrev c₂ : ℂ := HeightZetaLaurent.numerator 2
abbrev c₁ : ℂ := deriv HeightZetaLaurent.numerator 2

theorem regular_one : regular 1 = 3 * c₂ / 8 := by
  norm_num [regular, Complex.cpow_neg]
  ring

theorem regular_deriv : deriv regular 1 =
    3 * c₁ / 4 - 3 * c₂ * (Real.log 3 : ℂ) / 16 := by
  have hn : HasDerivAt (fun z : ℂ => HeightZetaLaurent.numerator (2 * z))
      (c₁ * 2) 1 := by
    simpa using (HeightZetaLaurent.numerator_analytic (2 * (1 : ℂ)) (by norm_num)).differentiableAt
      |>.hasDerivAt.comp 1 ((hasDerivAt_id (1 : ℂ)).const_mul 2)
  have hp : HasDerivAt (fun z : ℂ => (3 : ℂ) ^ (-z))
      (-(Real.log 3 : ℂ) / 3) 1 := by
    convert (hasDerivAt_id (1 : ℂ)).neg.const_cpow
      (c := (3 : ℂ)) (.inl (by norm_num)) using 1
    simp [Complex.cpow_neg, ← Complex.natCast_log]
    ring
  have hd := (hn.div_const 4).div ((hasDerivAt_const (1 : ℂ) 1).sub hp)
    (by norm_num [Complex.cpow_neg])
  change HasDerivAt regular _ 1 at hd
  rw [hd.deriv]
  norm_num [Complex.cpow_neg]
  ring

def allMain (X : ℝ) : ℂ :=
  regular 1 * X * Real.log X + (deriv regular 1 - regular 1) * X

theorem main_difference (X : ℝ) (hX : X ≠ 0) :
    allMain X - allMain (X / 3) =
      AsymptoticConstantScaling.coefficientMainTerm c₂ c₁ X := by
  simp only [allMain, regular_one, regular_deriv, Real.log_div hX (by norm_num : (3 : ℝ) ≠ 0),
    AsymptoticConstantScaling.coefficientMainTerm]
  push_cast
  ring

theorem expansion :
    CubicTargets.PoissonSummation.LeadingTerms.Expansion
      QuadraticZetaRegularization.value HeightZetaLaurent.value
      EulerKroneckerCalculation.value c₂ c₁ :=
  LeadingTermsAssembly.expansion_of_agreement IdealHeightSeries.continuation_agrees
    QuadraticDedekindFactorization.factorization

theorem coefficient_main (X : ℝ) :
    AsymptoticConstantScaling.coefficientMainTerm c₂ c₁ X =
      ((X * IntegralPointCountData.Q EulerKroneckerCalculation.value
        (1 / 2 * Real.log X) : ℝ) : ℂ) :=
  CountPolynomialNormalization.laurent_main expansion X

end Cubic.Introduction.CubeIdealMainTerm
