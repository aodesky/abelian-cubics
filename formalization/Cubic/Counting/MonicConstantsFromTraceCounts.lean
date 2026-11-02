import Cubic.Counting.CountPolynomialNormalization
import Cubic.PoissonSummation.Z0Laurent
import Cubic.Counting.MonicArchimedeanMoments
import Cubic.Counting.AsymptoticConstantIdentities

/-!
# Proof of `eqn:monicConstantsFromTraceCounts`

Substitute the two definite integral values (`eqn:monicArchimedeanMoments`)
into the trace-count coefficients and simplify, using
`C > 0` and `π/(9√3) = π√3/27`, `π/(3√3) = π√3/9`.
-/

noncomputable section

namespace Cubic.Counting.MonicConstantsFromTraceCounts

open Cubic.Counting.GeneralMonicData Cubic.Counting.MonicConstantsData
open CubicTargets.Counting.GeneralMonic

theorem derivative_one : deriv archimedeanFactor 1 =
    ((40 / 3 * Real.log 2 + 4 * Real.pi * Real.sqrt 3 / 3 - 76 / 9 : ℝ) : ℂ) := by
  obtain ⟨-, hJ⟩ := MonicArchimedeanMoments.«eqn:monicArchimedeanMoments»
  have hd := MonicArchimedeanMoments.hasDerivAt_archimedeanFactor
  rw [MonicArchimedeanMoments.derivative_real] at hd
  rw [hd.deriv, hJ]

theorem pi_div_nine_sqrt : (Real.pi : ℂ) / (9 * (Real.sqrt 3 : ℂ)) =
    (Real.pi : ℂ) * (Real.sqrt 3 : ℂ) / 27 := by
  have h : Real.pi / (9 * Real.sqrt 3) = Real.pi * Real.sqrt 3 / 27 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    field_simp; nlinarith [h3]
  exact_mod_cast h

theorem pi_div_three_sqrt : (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ)) =
    (Real.pi : ℂ) * (Real.sqrt 3 : ℂ) / 9 := by
  have h : Real.pi / (3 * Real.sqrt 3) = Real.pi * Real.sqrt 3 / 9 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    field_simp; nlinarith [h3]
  exact_mod_cast h

theorem coefficient_identities : TraceCountCoefficientsClaim := by
  have hV := MonicArchimedeanMoments.value_one
  have hC : (Cconst : ℂ) ≠ 0 := by
    exact_mod_cast (Cubic.Counting.AsymptoticConstantIdentities.original_leading_positive).ne'
  refine ⟨by simp only [traceCountLeading, hV]; ring, ?_⟩
  simp only [traceCountSecondary, traceCountLeading, hV, derivative_one, pi_div_nine_sqrt,
    pi_div_three_sqrt]
  push_cast
  field_simp
  ring

/-- The polynomial identity obtained from the trace-count coefficients. -/
theorem «eqn:monicConstantsFromTraceCounts» : MonicConstantsFromTraceCountsClaim := by
  intro Z μ hμ X
  have hc := AsymptoticConstantsAssembly.constants_of_continuation hμ
  have hDC : (Dconst : ℂ) / (Cconst : ℂ) =
      AsymptoticConstantsData.simplifiedSecondaryRatio μ := by
    simpa only [Cconst, Dconst, Complex.ofReal_div] using hc.simplified_secondary
  have hC : (Cconst : ℂ) =
      1 / 3 * Cubic.PoissonSummation.LeadingTermsData.splitProductAtTwo := by
    rw [CountPolynomialNormalization.C_eq_alpha]
    push_cast
    rw [Cubic.PoissonSummation.Z0Laurent.alpha_cast]
    ring
  have hS : monicSecondary μ = traceCountSecondary := by
    rw [coefficient_identities.2, coefficient_identities.1, hDC, hC,
      monicSecondary, monicLeading, AsymptoticConstantsData.simplifiedSecondaryRatio]
    simp only [AsymptoticConstantsConvergence.simplified_log_cast]
    ring
  have hL : monicLeading = traceCountLeading := by
    rw [coefficient_identities.1, hC, monicLeading]
    ring
  rw [hL, hS, coefficient_identities.2, coefficient_identities.1,
    CountPolynomialNormalization.Q_eq μ (EulerKroneckerCalculation.unique hμ) X]
  have hCn : (Cconst : ℂ) ≠ 0 := by
    exact_mod_cast hc.positive.ne'
  rw [CountPolynomialNormalization.C_eq_alpha] at hCn ⊢
  push_cast at hCn ⊢
  have ha := (div_ne_zero_iff.mp hCn).1
  field_simp [ha]
  ring

end Cubic.Counting.MonicConstantsFromTraceCounts
