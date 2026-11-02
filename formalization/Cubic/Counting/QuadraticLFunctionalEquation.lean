import Cubic.Counting.EulerKroneckerCalculation
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.FinCases

/-!
# The functional-equation calculation behind the Gamma constant

Specialize mathlib's primitive Dirichlet L-function functional equation to
the quadratic character modulo three. Logarithmic differentiation
eliminates the constant root number, while retaining the conductor term
`log 3` and both archimedean Gamma derivatives. This is the step relating
`L'(1)/L(1)` to `L'(0)/L(0)` in the calculation of [Shail, Math. Comp. 70 (2001)]
cited in the paper.
-/

noncomputable section

namespace Cubic.Counting.QuadraticLFunctionalEquation

open Filter DirichletCharacter Cubic.PoissonSummation
open QuadraticDirichletCharacter

theorem character_odd : character.Odd := by
  change character (-1 : ZMod 3) = -1
  rw [show (-1 : ZMod 3) = 2 by decide]
  exact character_two

theorem character_primitive : character.IsPrimitive := by
  have hd := character.conductor_dvd_level
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
  · exact False.elim (character_ne_one ((character.eq_one_iff_conductor_eq_one
      (by norm_num)).mpr h))
  · exact h

theorem character_inverse : character⁻¹ = character := by
  ext a
  rw [MulChar.inv_apply_eq_inv']
  fin_cases a <;> simp

private abbrev Λ := completedLFunction character

theorem completed_functional_equation (s : ℂ) :
    Λ (1 - s) = (3 : ℂ) ^ (s - 1 / 2) * rootNumber character * Λ s := by
  simpa only [character_inverse] using character_primitive.completedLFunction_one_sub s

private theorem completed_differentiable : Differentiable ℂ Λ :=
  differentiable_completedLFunction character_ne_one

private theorem completed_one_ne_zero : Λ 1 ≠ 0 := by
  have h := LFunction_apply_one_ne_zero character_ne_one
  rw [LFunction_eq_completed_div_gammaFactor _ _ (Or.inr (by norm_num))] at h
  exact (div_ne_zero_iff.mp h).1

private theorem completed_zero_ne_zero : Λ 0 ≠ 0 := by
  have he := completed_functional_equation 0
  norm_num only [sub_zero] at he
  have hn := completed_one_ne_zero
  rw [he] at hn
  exact (mul_ne_zero_iff.mp hn).2

private theorem root_number_ne_zero : rootNumber character ≠ 0 := by
  have he := completed_functional_equation 0
  norm_num only [sub_zero] at he
  have hn := completed_one_ne_zero
  rw [he] at hn
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2

theorem completed_log_derivatives : logDeriv Λ 1 + logDeriv Λ 0 = -(Real.log 3 : ℂ) := by
  have he : (Λ ∘ fun s : ℂ => 1 - s) =
      (fun s : ℂ => (3 : ℂ) ^ (s - 1 / 2) * rootNumber character * Λ s) :=
    funext completed_functional_equation
  have h := congrArg (fun f : ℂ → ℂ => logDeriv f 0) he
  dsimp only at h
  rw [logDeriv_comp (completed_differentiable _) (by fun_prop)] at h
  have hneg : deriv (fun s : ℂ => 1 - s) 0 = -1 :=
    ((hasDerivAt_id' (0 : ℂ)).const_sub 1).deriv
  simp only [sub_zero, hneg, mul_neg_one] at h
  have hd : DifferentiableAt ℂ (fun s : ℂ => (3 : ℂ) ^ (s - 1 / 2)) 0 := by fun_prop
  have hn : (3 : ℂ) ^ ((0 : ℂ) - 1 / 2) ≠ 0 := by simp
  rw [logDeriv_mul (f := fun s : ℂ => (3 : ℂ) ^ (s - 1 / 2) * rootNumber character)
    (g := Λ) 0 (mul_ne_zero hn root_number_ne_zero) completed_zero_ne_zero
    (hd.mul_const _) (completed_differentiable 0),
    logDeriv_mul_const 0 _ root_number_ne_zero] at h
  have hp : logDeriv (fun s : ℂ => (3 : ℂ) ^ (s - 1 / 2)) 0 = (Real.log 3 : ℂ) := by
    have ht := ((hasDerivAt_id' (0 : ℂ)).sub_const (1 / 2)).const_cpow
      (c := (3 : ℂ)) (Or.inl (by norm_num))
    rw [logDeriv_apply, ht.deriv]
    simp
  rw [hp] at h
  linear_combination -h

theorem gammaR_two : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
  norm_num [Complex.Gammaℝ, Complex.cpow_neg]

theorem gammaR_two_derivative : HasDerivAt Complex.Gammaℝ
    (-((Real.eulerMascheroniConstant : ℂ) + Complex.log Real.pi) /
      (2 * (Real.pi : ℂ))) 2 := by
  have hf := ((hasDerivAt_neg (2 : ℂ)).div_const 2).const_cpow
    (c := (Real.pi : ℂ)) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have hG : HasDerivAt Complex.Gamma (-(Real.eulerMascheroniConstant : ℂ))
      ((2 : ℂ) / 2) := by
    norm_num only [div_self (by norm_num : (2 : ℂ) ≠ 0)]
    exact Complex.hasDerivAt_Gamma_one
  have hg := hG.comp (h := fun s : ℂ => s / 2) (2 : ℂ)
    ((hasDerivAt_id' (2 : ℂ)).div_const (2 : ℂ))
  change HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) _ 2
  apply (hf.mul hg).congr_deriv
  norm_num [Complex.Gamma_one, Complex.cpow_neg]
  ring

private theorem gamma_factor_zero_derivative : HasDerivAt
    (fun s : ℂ => Complex.Gammaℝ (s + 1))
    (-((Real.eulerMascheroniConstant : ℂ) + Complex.log (4 * Real.pi)) / 2) 0 := by
  have hG : HasDerivAt Complex.Gammaℝ
      (-((Real.eulerMascheroniConstant : ℂ) + Complex.log (4 * Real.pi)) / 2)
      ((0 : ℂ) + 1) := by simpa using Complex.hasDerivAt_Gammaℝ_one
  simpa using hG.comp (h := fun s : ℂ => s + 1) (0 : ℂ)
    ((hasDerivAt_id' (0 : ℂ)).add_const (1 : ℂ))

private theorem gamma_factor_one_derivative : HasDerivAt
    (fun s : ℂ => Complex.Gammaℝ (s + 1))
    (-((Real.eulerMascheroniConstant : ℂ) + Complex.log Real.pi) /
      (2 * (Real.pi : ℂ))) 1 := by
  have hG : HasDerivAt Complex.Gammaℝ
      (-((Real.eulerMascheroniConstant : ℂ) + Complex.log Real.pi) /
        (2 * (Real.pi : ℂ))) ((1 : ℂ) + 1) := by
    norm_num only [one_add_one_eq_two]
    exact gammaR_two_derivative
  simpa using hG.comp (h := fun s : ℂ => s + 1) (1 : ℂ)
    ((hasDerivAt_id' (1 : ℂ)).add_const (1 : ℂ))

private theorem L_eq_completed_div_gamma : LFunction character =
    (fun s : ℂ => Λ s / Complex.Gammaℝ (s + 1)) := by
  funext s
  rw [LFunction_eq_completed_div_gammaFactor _ _ (Or.inr (by norm_num)),
    character_odd.gammaFactor_def]

theorem L_zero_ne_zero : LFunction character 0 ≠ 0 := by
  rw [L_eq_completed_div_gamma]
  simpa using completed_zero_ne_zero

theorem L_log_derivatives :
    logDeriv (LFunction character) 1 + logDeriv (LFunction character) 0 =
      (Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * Real.pi) : ℂ) -
        (Real.log 3 : ℂ) := by
  rw [L_eq_completed_div_gamma]
  rw [logDeriv_div (g := fun s : ℂ => Complex.Gammaℝ (s + 1)) 1 completed_one_ne_zero
    (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
    (completed_differentiable 1) gamma_factor_one_derivative.differentiableAt,
    logDeriv_div (g := fun s : ℂ => Complex.Gammaℝ (s + 1)) 0 completed_zero_ne_zero (by simp)
    (completed_differentiable 0) gamma_factor_zero_derivative.differentiableAt]
  have hg1 : logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) 1 =
      -((Real.eulerMascheroniConstant : ℂ) + Complex.log Real.pi) / 2 := by
    rw [logDeriv_apply, gamma_factor_one_derivative.deriv]
    norm_num only [one_add_one_eq_two, gammaR_two]
    field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]
  have hg0 : logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) 0 =
      -((Real.eulerMascheroniConstant : ℂ) + Complex.log (4 * Real.pi)) / 2 := by
    rw [logDeriv_apply, gamma_factor_zero_derivative.deriv]
    simp
  rw [hg1, hg0]
  have hlogs : Complex.log (4 * (Real.pi : ℂ)) + Complex.log (Real.pi : ℂ) =
      2 * (Real.log (2 * Real.pi) : ℂ) := by
    have hlog : Real.log (4 * Real.pi) + Real.log Real.pi = 2 * Real.log (2 * Real.pi) := by
      rw [Real.log_mul (by norm_num) Real.pi_ne_zero,
        Real.log_mul (by norm_num) Real.pi_ne_zero,
        show Real.log 4 = 2 * Real.log 2 by
          convert Real.log_pow (2 : ℝ) 2 using 1; norm_num]
      ring
    have h := congrArg (fun x : ℝ => (x : ℂ)) hlog
    push_cast at h
    simpa only [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi),
      Complex.ofReal_log Real.pi_pos.le, Complex.ofReal_mul, Complex.ofReal_ofNat] using h
  linear_combination completed_log_derivatives + hlogs / 2

end Cubic.Counting.QuadraticLFunctionalEquation
