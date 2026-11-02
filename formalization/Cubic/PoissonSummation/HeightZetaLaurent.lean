import Cubic.PoissonSummation.AnalyticLaurent
import Cubic.PoissonSummation.QuadraticZetaRegularization
import Cubic.PoissonSummation.LeadingTermsCorrection
import Cubic.PoissonSummation.HeightZetaFunctionFormula

/-!
# The double pole and Laurent expansion of the height continuation

Regularize at `u=1`, then substitute `u=s/2`. The analytic numerator of the
height continuation is `4 R(s/2)² E_paper(s/2)`. Thus the factor 4 and both chain
factors in the next coefficient are obtained from actual complex derivatives.

The original height-series agreement uses only the approved general Poisson
input. Identifying `R'(1)/R(1)` with the paper's `γ_E` and `R(1)` with the
ideal-counting residue uses the Dedekind-zeta comparison, made in the proof of
`prop:leadingTerms`.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaLaurent

open Filter Asymptotics QuadraticZetaRegularization
open scoped Topology

def value (s : ℂ) : ℂ := HeightZetaContinuation.value (s / 2)

def numerator (s : ℂ) : ℂ := 4 * regular (s / 2) ^ 2 * LeadingTermsData.correction s

theorem half_ne_one {s : ℂ} (hs : s ≠ 2) : s / 2 ≠ 1 := by
  intro he
  apply hs
  simpa using (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).mp he

theorem value_factorization (s : ℂ) : value s =
    QuadraticZetaRegularization.value (s / 2) ^ 2 * LeadingTermsData.correction s := by
  unfold value HeightZetaContinuation.value QuadraticZetaRegularization.value
    LeadingTermsData.correction
  ring

theorem value_eq_quotient (s : ℂ) (hs : s ≠ 2) : value s = numerator s / (s - 2) ^ 2 := by
  rw [numerator, regular_eq _ (half_ne_one hs), value_factorization]
  field_simp [sub_ne_zero.mpr hs]
  ring

theorem numerator_analytic (s : ℂ) (hs : 1 < s.re) : AnalyticAt ℂ numerator s := by
  have hR : AnalyticAt ℂ (fun s : ℂ => regular (s / 2)) s :=
    (differentiable_regular.analyticAt (s / 2)).comp (f := fun s : ℂ => s / 2) (by fun_prop)
  have hE := LeadingTermsCorrection.differentiableOn_correction.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  exact (analyticAt_const.fun_mul (hR.fun_pow 2)).fun_mul hE

theorem numerator_two : numerator 2 =
    4 * DirichletCharacter.LFunction QuadraticDirichletCharacter.character 1 ^ 2 *
      LeadingTermsData.correction 2 := by
  simp [numerator, regular_one]

theorem numerator_two_ne_zero : numerator 2 ≠ 0 := by
  simp only [numerator, div_self (by norm_num : (2 : ℂ) ≠ 0)]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ regular_one_ne_zero))
    LeadingTermsCorrection.correction_two_ne_zero

theorem meromorphic : MeromorphicOn value {s : ℂ | 1 < s.re} := by
  intro s hs
  exact (HeightZetaContinuation.meromorphicOn_value (s / 2)
    (LeadingTermsCorrection.half_re hs)).comp_analyticAt
      (g := fun s : ℂ => s / 2) (by fun_prop)

theorem analytic_away_two (s : ℂ) (hs : 1 < s.re) (hne : s ≠ 2) : AnalyticAt ℂ value s := by
  have hA := numerator_analytic s hs
  have hquot : AnalyticAt ℂ (fun w : ℂ => numerator w / (w - 2) ^ 2) s :=
    hA.fun_div ((analyticAt_id.fun_sub analyticAt_const).fun_pow 2)
      (pow_ne_zero _ (sub_ne_zero.mpr hne))
  apply hquot.congr
  filter_upwards [isOpen_ne.mem_nhds hne] with w hw
  exact (value_eq_quotient w hw).symm

theorem pole_order : meromorphicOrderAt value 2 = (-2 : ℤ) :=
  AnalyticLaurent.order_of_nonzero_numerator (numerator_analytic 2 (by norm_num))
    numerator_two_ne_zero (by
      filter_upwards [self_mem_nhdsWithin] with s hs using value_eq_quotient s hs)

theorem laurent : (fun s : ℂ => value s - numerator 2 / (s - 2) ^ 2 -
    deriv numerator 2 / (s - 2)) =O[𝓝[≠] (2 : ℂ)] (fun _ => (1 : ℂ)) :=
  AnalyticLaurent.laurent_of_analytic_numerator (numerator_analytic 2 (by norm_num)) (by
    filter_upwards [self_mem_nhdsWithin] with s hs using value_eq_quotient s hs)

theorem numerator_derivative : deriv numerator 2 =
    4 * regular 1 * deriv regular 1 * LeadingTermsData.correction 2 +
      4 * regular 1 ^ 2 * deriv LeadingTermsData.correction 2 := by
  have hR : HasDerivAt (fun s : ℂ => regular (s / 2)) (deriv regular 1 / 2) 2 := by
    have hd := (differentiable_regular (2 / 2)).hasDerivAt.comp 2
      (h := fun s : ℂ => s / 2) ((hasDerivAt_id' (2 : ℂ)).div_const 2)
    simpa using hd
  have hE := LeadingTermsCorrection.differentiableOn_correction.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num))
  have hd := ((hR.fun_pow 2).const_mul 4).fun_mul hE.hasDerivAt
  change HasDerivAt numerator _ 2 at hd
  rw [hd.deriv]
  norm_num
  left
  ring

theorem coefficient_ratio : deriv numerator 2 / numerator 2 =
    deriv regular 1 / regular 1 +
      deriv LeadingTermsData.correction 2 / LeadingTermsData.correction 2 := by
  rw [numerator_derivative]
  simp only [numerator, div_self (by norm_num : (2 : ℂ) ≠ 0)]
  field_simp [regular_one_ne_zero, LeadingTermsCorrection.correction_two_ne_zero]

theorem agrees_with_height
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (s : ℂ) (hs : 2 < s.re) : value s = LeadingTermsData.heightZeta s := by
  have hh := («thm:heightZetaFunctionFormula2» hPoisson).euler_formula s 0 (by simpa using hs)
  have hhalf : 1 < (s / 2).re := by
    norm_num [Complex.div_re]
    linarith
  rw [value, HeightZetaContinuationFormula.continuation_eq_eulerExpression _ hhalf]
  simpa [LeadingTermsData.heightZeta, HeightZetaFormulaData.parameter] using hh.symm

end Cubic.PoissonSummation.HeightZetaLaurent
