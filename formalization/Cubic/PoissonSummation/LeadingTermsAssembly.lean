import Cubic.PoissonSummation.HeightZetaLaurent
import Cubic.PoissonSummation.LeadingTermsSimplifiedDerivative
import CubicTargets.PoissonSummation.LeadingTerms

/-!
# Assembly of `prop:leadingTerms` from its analytic and arithmetic ingredients

The analytic assembly takes the genuine Dedekind factorization as an explicit
argument. `QuadraticDedekindFactorization.factorization` proves that argument
from the actual ideal series and local splitting data. The exact-label theorem
in `LeadingTerms.lean` supplies it, leaving only the assumed general Poisson
hypothesis. The full concrete target is retained throughout.
-/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsAssembly

open Filter QuadraticZetaRegularization
open scoped Topology

private theorem real_right_to_complex_punctured : Tendsto (fun s : ℝ => (s : ℂ))
    (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change (s : ℂ) ≠ 1
    exact_mod_cast (ne_of_gt hs)

/-- The comparison uses two limits of the same genuine series on the real right half-line. -/
theorem L_one_eq_residue
    (hD : CubicTargets.PoissonSummation.LeadingTerms.DedekindFactorization) :
    DirichletCharacter.LFunction QuadraticDirichletCharacter.character 1 =
      (NumberField.dedekindZeta_residue Cubic.QuadraticCorrespondence.CyclotomicField.E : ℂ) := by
  have hL := QuadraticZetaRegularization.residue_limit.comp real_right_to_complex_punctured
  have hK := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT
    Cubic.QuadraticCorrespondence.CyclotomicField.E
  apply tendsto_nhds_unique hL
  apply hK.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply]
  rw [hD (s : ℂ) hs]
  rfl

theorem dedekind_expression_meromorphic :
    MeromorphicOn QuadraticZetaRegularization.value {u : ℂ | (1 / 2 : ℝ) < u.re} := by
  intro u hu
  change (1 / 2 : ℝ) < u.re at hu
  exact (HeightZetaContinuation.meromorphicAt_riemannZeta u (by linarith)).fun_mul
    (QuadraticDirichletCharacter.differentiable_LFunction.analyticAt u).meromorphicAt

theorem dedekind_expression_analytic (u : ℂ) (hu : u ≠ 1) :
    AnalyticAt ℂ QuadraticZetaRegularization.value u := by
  have hq : AnalyticAt ℂ (fun w : ℂ => regular w / (w - 1)) u :=
    (differentiable_regular.analyticAt u).fun_div
      (analyticAt_id.fun_sub analyticAt_const) (sub_ne_zero.mpr hu)
  apply hq.congr
  filter_upwards [isOpen_ne.mem_nhds hu] with w hw
  rw [regular_eq w hw]
  field_simp [sub_ne_zero.mpr hw]

/-- Assemble the full target once the genuine arithmetic factorization is supplied. -/
theorem expansion_of_agreement
    (hagree : ∀ s : ℂ, 2 < s.re →
      HeightZetaLaurent.value s = AdelicHeightZetaData.heightZeta s 0)
    (hD : CubicTargets.PoissonSummation.LeadingTerms.DedekindFactorization) :
    CubicTargets.PoissonSummation.LeadingTerms.Expansion
      QuadraticZetaRegularization.value HeightZetaLaurent.value
      (deriv regular 1 / regular 1) (HeightZetaLaurent.numerator 2)
      (deriv HeightZetaLaurent.numerator 2) := by
  refine {
    dedekind_agrees := fun u hu => (hD u hu).symm
    dedekind_meromorphic := dedekind_expression_meromorphic
    dedekind_analytic := fun u _ hu => dedekind_expression_analytic u hu
    euler_kronecker := log_derivative_limit
    dedekind_residue := ?_
    residue_value := QuadraticDedekindResidue.residue_value_complex
    residue_L_value := L_one_eq_residue hD
    continuation_agrees := hagree
    meromorphic := HeightZetaLaurent.meromorphic
    analytic_away_two := HeightZetaLaurent.analytic_away_two
    pole_order := HeightZetaLaurent.pole_order
    factorization := fun s _ _ => HeightZetaLaurent.value_factorization s
    correction_analytic := LeadingTermsCorrection.differentiableOn_correction
    correction_real := LeadingTermsCorrection.correction_two_real
    correction_positive := LeadingTermsCorrection.correction_two_pos
    inert_absolute := LeadingTermsCorrection.inert_absolute
    split_absolute := LeadingTermsCorrection.split_absolute
    laurent := HeightZetaLaurent.laurent
    leading_ne_zero := HeightZetaLaurent.numerator_two_ne_zero
    leading := HeightZetaLaurent.numerator_two
    subleading := HeightZetaLaurent.coefficient_ratio
    explicit_product_absolute := LeadingTermsSplitProduct.absolute_at_two
    explicit_leading := ?_
    explicit_sum_absolute := LeadingTermsPrimeSums.summable_split_log
    explicit_subleading := ?_ }
  · simpa only [L_one_eq_residue hD] using QuadraticZetaRegularization.residue_limit
  · rw [HeightZetaLaurent.numerator_two, L_one_eq_residue hD]
    exact LeadingTermsEulerProduct.residue_leading_explicit
  · rw [HeightZetaLaurent.coefficient_ratio,
      LeadingTermsSimplifiedDerivative.correction_log_derivative]
    ring

theorem claim_of_agreement
    (hagree : ∀ s : ℂ, 2 < s.re →
      HeightZetaLaurent.value s = AdelicHeightZetaData.heightZeta s 0)
    (hD : CubicTargets.PoissonSummation.LeadingTerms.DedekindFactorization) :
    CubicTargets.PoissonSummation.LeadingTerms.Claim :=
  ⟨_, _, _, _, _, expansion_of_agreement hagree hD⟩

/-- The main toric proof supplies the series comparison by Poisson summation. -/
theorem claim_of_dedekindFactorization
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hD : CubicTargets.PoissonSummation.LeadingTerms.DedekindFactorization) :
    CubicTargets.PoissonSummation.LeadingTerms.Claim :=
  claim_of_agreement (HeightZetaLaurent.agrees_with_height hPoisson) hD

end Cubic.PoissonSummation.LeadingTermsAssembly
