import Cubic.PoissonSummation.LeadingTermsAssembly
import Cubic.PoissonSummation.QuadraticDedekindFactorization
import Cubic.Counting.AsymptoticConstantsData
import CubicTargets.Counting.AsymptoticPolynomialCount
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The Euler–Kronecker constant and the quadratic L-function derivative

Identify the constant defined by the Dedekind continuation with
`γ + L'(1,χ)/L(1,χ)`. The module `EulerKroneckerGamma` evaluates it using Gamma
values.
-/

noncomputable section

namespace Cubic.Counting.EulerKroneckerCalculation

open Filter DirichletCharacter Cubic.PoissonSummation
open scoped Topology

def value : ℂ := deriv QuadraticZetaRegularization.regular 1 /
  QuadraticZetaRegularization.regular 1

theorem regular_zeta_derivative :
    deriv (LFunctionTrivChar₁ 1) 1 = (Real.eulerMascheroniConstant : ℂ) := by
  apply tendsto_nhds_unique (differentiable_LFunctionTrivChar₁ 1 1).hasDerivAt.tendsto_slope
  apply tendsto_riemannZeta_sub_one_div.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [slope_def_field, LFunctionTrivChar₁, Function.update_of_ne hs,
    Function.update_self, Nat.primeFactors_one, Finset.prod_empty,
    LFunctionTrivChar, LFunction_modOne_eq]
  field_simp [sub_ne_zero.mpr hs]

theorem value_eq_euler_add_L_derivative :
    value = (Real.eulerMascheroniConstant : ℂ) +
      deriv (LFunction QuadraticDirichletCharacter.character) 1 /
        LFunction QuadraticDirichletCharacter.character 1 := by
  have hn := LFunction_apply_one_ne_zero QuadraticDirichletCharacter.character_ne_one
  rw [value, QuadraticZetaRegularization.regular_one]
  have hd : deriv QuadraticZetaRegularization.regular 1 =
      deriv (LFunctionTrivChar₁ 1) 1 * LFunction QuadraticDirichletCharacter.character 1 +
        LFunctionTrivChar₁ 1 1 * deriv (LFunction QuadraticDirichletCharacter.character) 1 :=
    ((differentiable_LFunctionTrivChar₁ 1 1).hasDerivAt.fun_mul
      (QuadraticDirichletCharacter.differentiable_LFunction 1).hasDerivAt).deriv
  rw [hd, regular_zeta_derivative]
  simp only [LFunctionTrivChar₁, Function.update_self, Nat.primeFactors_one, Finset.prod_empty,
    one_mul]
  field_simp

theorem genuine_constant :
    CubicTargets.Counting.AsymptoticPolynomialCount.EulerKronecker
      QuadraticZetaRegularization.value value :=
  ⟨fun s hs => (QuadraticDedekindFactorization.factorization s hs).symm,
    fun s _ hs => LeadingTermsAssembly.dedekind_expression_analytic s hs,
    QuadraticZetaRegularization.log_derivative_limit⟩

private theorem real_right_to_complex_punctured : Tendsto (fun s : ℝ => (s : ℂ))
    (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change (s : ℂ) ≠ 1
    exact_mod_cast (ne_of_gt hs)

/-- Agreement with the Dirichlet series on the right half-plane fixes the limit. -/
theorem unique {Z : ℂ → ℂ} {γ : ℂ}
    (h : CubicTargets.Counting.AsymptoticPolynomialCount.EulerKronecker Z γ) : γ = value := by
  have h₁ := h.defining_limit.comp real_right_to_complex_punctured
  have h₂ := genuine_constant.defining_limit.comp real_right_to_complex_punctured
  apply tendsto_nhds_unique h₁
  apply h₂.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have he : Z =ᶠ[𝓝 (s : ℂ)] QuadraticZetaRegularization.value := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (s : ℂ) ∈ {u : ℂ | 1 < u.re} from hs)] with u hu
    exact (h.agrees u hu).trans (genuine_constant.agrees u hu).symm
  simp only [Function.comp_apply]
  rw [he.deriv_eq, he.eq_of_nhds]

end Cubic.Counting.EulerKroneckerCalculation
