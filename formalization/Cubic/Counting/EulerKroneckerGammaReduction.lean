import Cubic.Counting.QuadraticLFunctionalEquation
import Cubic.Counting.QuadraticLZero
import CubicTargets.Counting.EulerKroneckerGamma
import CubicTargets.Counting.QuadraticLZeroDerivative

/-!
# Reduction of the classical constant to the zero-value calculation

The functional equation and the Laurent computation reduce the Gamma
evaluation to the logarithmic derivative at zero. The companion
`EulerKroneckerGamma` module proves the required derivative identity.
`gamma_of_zero_values` records the special values used in
[Shail, Math. Comp. 70 (2001)], (3.4)–(3.7), and verifies the cancellation of
the conductor logarithm.
-/

noncomputable section

namespace Cubic.Counting.EulerKroneckerGammaReduction

open Cubic.PoissonSummation DirichletCharacter AsymptoticConstantsData

theorem value_from_zero_derivative : EulerKroneckerCalculation.value =
    2 * (Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * Real.pi) : ℂ) -
      (Real.log 3 : ℂ) - logDeriv (LFunction QuadraticDirichletCharacter.character) 0 := by
  rw [EulerKroneckerCalculation.value_eq_euler_add_L_derivative]
  change (Real.eulerMascheroniConstant : ℂ) +
    logDeriv (LFunction QuadraticDirichletCharacter.character) 1 = _
  linear_combination QuadraticLFunctionalEquation.L_log_derivatives

/-- The Gamma identity, with the conductor term explicit. -/
theorem gamma_iff_zero_log_derivative :
    CubicTargets.Counting.EulerKroneckerGamma.Claim ↔
      logDeriv (LFunction QuadraticDirichletCharacter.character) 0 =
        -(Real.log 3 : ℂ) +
          3 * (Real.log (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)) : ℂ) := by
  unfold CubicTargets.Counting.EulerKroneckerGamma.Claim classicalEulerKronecker
  rw [value_from_zero_derivative]
  push_cast
  constructor <;> intro h <;> linear_combination -h

/-- The Gamma identity from the values of `L` and `L'` at zero (the value is `QuadraticLZero.L_zero`). -/
theorem gamma_of_zero_values
    (h₀ : LFunction QuadraticDirichletCharacter.character 0 = (1 / 3 : ℂ))
    (h₀' : deriv (LFunction QuadraticDirichletCharacter.character) 0 =
      -(Real.log 3 : ℂ) / 3 +
        (Real.log (Real.Gamma (1 / 3) / Real.Gamma (2 / 3)) : ℂ)) :
    CubicTargets.Counting.EulerKroneckerGamma.Claim := by
  rw [gamma_iff_zero_log_derivative, logDeriv_apply, h₀', h₀]
  ring

/-- Reduction to the explicit derivative identity, with the value at zero proved. -/
theorem gamma_iff_zero_derivative : CubicTargets.Counting.EulerKroneckerGamma.Claim ↔
    CubicTargets.Counting.QuadraticLZeroDerivative.Claim := by
  rw [gamma_iff_zero_log_derivative, logDeriv_apply, QuadraticLZero.L_zero]
  unfold CubicTargets.Counting.QuadraticLZeroDerivative.Claim
  constructor
  · intro h
    linear_combination h / 3
  · intro h
    linear_combination 3 * h

end Cubic.Counting.EulerKroneckerGammaReduction
