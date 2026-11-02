import Cubic.Counting.MonicEulerFactor
import Cubic.Counting.MonicConstantsFromTraceCounts

/-!
# Proof of `eqn:monicConceptualConstants`

`ρ_E = π/(3√3)` is the class-number-formula residue (`QuadraticDedekindResidue`). By
`MonicEulerFactor.eq_correction`, near `z = 1`,
`𝓔_mon(z) = R(z) E(2z)` with `R(z) = (1 + 2·3^{-2z})/(3(1 - 3^{-z}))`, so
`𝓔_mon(1) = (11/18) E(2)` and
`𝓔_mon'(1)/𝓔_mon(1) = R'(1)/R(1) + 2E'(2)/E(2) = -(19/22) log 3 + 2E'(2)/E(2)
  = -2ζ'(2)/ζ(2) - (5/44) log 3 + 2 Σ_{p≡1 (3)} (2p+1) log p/((p²-1)(p+2))`,
using the logarithmic derivative of `E` at `2` from the proof of `prop:leadingTerms`.
With `E(2) = (3/π²) ∏ (1 - 2/(p(p+1)))` and `eqn:monicArchimedeanMoments`, both lines are
identities between the explicit constants of `thm:generalMonicCount`. The second holds for
every value of `γ`; the hypothesis only names `γ_E`.
-/

noncomputable section

namespace Cubic.Counting.MonicConceptualConstants

open Cubic.Counting.MonicConstantsData Cubic.Counting.MonicEulerFactor
open Cubic.PoissonSummation Cubic.PoissonSummation.LeadingTermsData
open Cubic.PoissonSummation.FiniteEulerProduct
open CubicTargets.Counting.GeneralMonic
open Filter
open scoped Topology

/-- The prefactor `R(z) = (1 + 2·3^{-2z})/(3(1 - 3^{-z}))`. -/
def R (z : ℂ) : ℂ := (1 + 2 * (3 : ℂ) ^ (-(2 * z))) / (3 * (1 - (3 : ℂ) ^ (-z)))

theorem log_three : Complex.log 3 = (Real.log 3 : ℂ) := by
  rw [Complex.ofReal_log (by norm_num)]; norm_num

theorem three_neg_one : (3 : ℂ) ^ (-(1 : ℂ)) = 1 / 3 := by
  rw [Complex.cpow_neg_one]; ring

theorem three_neg_two : (3 : ℂ) ^ (-(2 * (1 : ℂ))) = 1 / 9 := by
  rw [three_sq, three_neg_one]; norm_num

theorem R_one : R 1 = 11 / 18 := by
  rw [R, three_neg_two, three_neg_one]; norm_num

theorem hasDerivAt_R : HasDerivAt R (-(19 / 36) * (Real.log 3 : ℂ)) 1 := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have h1 : HasDerivAt (fun z : ℂ => (3 : ℂ) ^ (-z)) (-(1 / 3 * (Real.log 3 : ℂ))) 1 := by
    have := (hasDerivAt_neg (1 : ℂ)).const_cpow (c := (3 : ℂ)) (Or.inl h3)
    simp only [three_neg_one, log_three] at this
    convert this using 1; ring
  have h2 : HasDerivAt (fun z : ℂ => (3 : ℂ) ^ (-(2 * z))) (-(2 / 9 * (Real.log 3 : ℂ))) 1 := by
    have hf : HasDerivAt (fun z : ℂ => -(2 * z)) (-2) 1 := by
      simpa using ((hasDerivAt_id' (1 : ℂ)).const_mul (2 : ℂ)).fun_neg
    have := hf.const_cpow (c := (3 : ℂ)) (Or.inl h3)
    simp only [three_neg_two, log_three] at this
    convert this using 1; ring
  have hN := (h2.const_mul 2).const_add 1
  have hD := (h1.const_sub 1).const_mul 3
  have hD0 : 3 * (1 - (3 : ℂ) ^ (-(1 : ℂ))) ≠ 0 := by rw [three_neg_one]; norm_num
  have := hN.div hD hD0
  simp only [three_neg_one, three_neg_two] at this
  convert this using 1
  ring

theorem correction_hasDerivAt :
    HasDerivAt correction (deriv correction 2) 2 :=
  (LeadingTermsCorrection.differentiableOn_correction.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).hasDerivAt

theorem log_derivative :
    deriv monicEulerFactor 1 / monicEulerFactor 1 =
      -2 * (deriv riemannZeta 2 / riemannZeta 2) - 5 / 44 * (Real.log 3 : ℂ) +
        2 * ∑' p : SplitPrimes, splitLogTerm p := by
  have hU : {z : ℂ | (1 / 2 : ℝ) < z.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have he : monicEulerFactor =ᶠ[𝓝 (1 : ℂ)] (fun z => R z * correction (2 * z)) := by
    filter_upwards [hU] with z hz using eq_correction hz
  have hg : HasDerivAt (fun z : ℂ => correction (2 * z)) (deriv correction 2 * 2) 1 := by
    have hh : HasDerivAt (fun z : ℂ => 2 * z) 2 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).const_mul 2
    exact HasDerivAt.comp_of_eq 1 correction_hasDerivAt hh (by norm_num)
  rw [he.deriv_eq, (hasDerivAt_R.fun_mul hg).deriv, value_one]
  have hc := LeadingTermsCorrection.correction_two_ne_zero
  have hl := LeadingTermsSimplifiedDerivative.correction_log_derivative
  rw [div_eq_iff hc] at hl
  norm_num only [R_one, mul_one]
  rw [hl]
  field_simp
  ring

theorem «eqn:monicConceptualConstants» : MonicConceptualConstantsClaim := by
  have hres := QuadraticDedekindResidue.residue_value_complex
  have h3c : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hρ : ((Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ))) ^ 2 = (Real.pi : ℂ) ^ 2 / 27 := by
    rw [MonicConstantsFromTraceCounts.pi_div_three_sqrt, div_pow, mul_pow, h3c]; ring
  refine ⟨hres, ?_, fun Z γ _ => ?_⟩
  · rw [hres, hρ, value_one, MonicArchimedeanMoments.value_one,
      LeadingTermsEulerProduct.correction_two_explicit, monicLeading]
    field_simp
    ring
  · rw [log_derivative, MonicConstantsFromTraceCounts.derivative_one,
      MonicArchimedeanMoments.value_one, MonicConstantsFromTraceCounts.pi_div_nine_sqrt,
      monicSecondary]
    push_cast
    ring

end Cubic.Counting.MonicConceptualConstants
