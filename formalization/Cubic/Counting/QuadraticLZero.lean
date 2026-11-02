import Cubic.Counting.QuadraticLFunctionalEquation

/-!
# The root number and `L(0,χ)` for the character modulo three

Evaluate the finite Gauss sum with its standard additive-character sign, then
combine the functional equation with the class-number residue `L(1,χ)`.
This verifies the factor `L(0,χ)=1/3` in the classical-constant calculation.
The derivative at zero is computed in `QuadraticLDerivativeApproximation` and
`EulerKroneckerGamma`.
-/

noncomputable section

namespace Cubic.Counting.QuadraticLZero

open DirichletCharacter Cubic.PoissonSummation QuadraticDirichletCharacter
open QuadraticLFunctionalEquation

theorem additive_character_one : ZMod.stdAddChar (1 : ZMod 3) =
    -(1 / 2 : ℂ) + (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  have h := ZMod.stdAddChar_coe (N := 3) (1 : ℤ)
  norm_num only [Int.cast_one, Nat.cast_ofNat, mul_one] at h
  rw [h]
  have ha : 2 * (Real.pi : ℂ) * Complex.I / 3 =
      ((Real.pi - Real.pi / 3 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [ha, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

theorem additive_character_two : ZMod.stdAddChar (2 : ZMod 3) =
    -(1 / 2 : ℂ) - (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  have h := ZMod.stdAddChar_coe (N := 3) (2 : ℤ)
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat] at h
  rw [h]
  have ha : 2 * (Real.pi : ℂ) * Complex.I * 2 / 3 =
      ((Real.pi + Real.pi / 3 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [ha, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_add, Real.sin_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp only [Real.cos_pi, Real.sin_pi, neg_mul, one_mul, zero_mul, zero_add, sub_zero]
  push_cast
  ring

theorem gauss_sum : gaussSum character ZMod.stdAddChar = (Real.sqrt 3 : ℂ) * Complex.I := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  simp only [gaussSum, hu]
  simp [show (1 : ZMod 3) ≠ 2 by decide, additive_character_one, additive_character_two]
  ring

theorem three_half_power : (3 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 3 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem root_number : rootNumber character = 1 := by
  rw [rootNumber, if_neg character_odd.not_even, pow_one, gauss_sum]
  norm_num only [Nat.cast_ofNat]
  rw [three_half_power]
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp

theorem L_one : LFunction character 1 = (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ)) := by
  rw [LeadingTermsAssembly.L_one_eq_residue QuadraticDedekindFactorization.factorization,
    QuadraticDedekindResidue.residue_value_complex]

/-- The value at zero, deduced from the completed L-function. -/
theorem L_zero : LFunction character 0 = (1 / 3 : ℂ) := by
  have hf := completed_functional_equation (0 : ℂ)
  change completedLFunction character (1 - 0) =
    (3 : ℂ) ^ ((0 : ℂ) - 1 / 2) * rootNumber character * completedLFunction character 0 at hf
  rw [sub_zero, zero_sub, Complex.cpow_neg, three_half_power, root_number, mul_one] at hf
  have h₁ := LFunction_eq_completed_div_gammaFactor character (1 : ℂ) (Or.inr (by norm_num))
  have h₀ := LFunction_eq_completed_div_gammaFactor character (0 : ℂ) (Or.inr (by norm_num))
  rw [character_odd.gammaFactor_def, show (1 : ℂ) + 1 = 2 by norm_num, gammaR_two, L_one] at h₁
  rw [character_odd.gammaFactor_def, zero_add, Complex.Gammaℝ_one, div_one] at h₀
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [h₀]
  rw [hf] at h₁
  field_simp at h₁ ⊢
  linear_combination -h₁

end Cubic.Counting.QuadraticLZero
