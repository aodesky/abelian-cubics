import Cubic.Counting.QuadraticLApproximationIdentification

/-!
# The classical Gamma formula for the Euler–Kronecker constant

The zero derivative is proved by locally uniform convergence and the
Euler/Bohr–Mollerup limit. The functional equation then supplies the stated
Gamma evaluation, with no additional analytic hypothesis.
-/

namespace Cubic.Counting.EulerKroneckerGamma

theorem evaluation : CubicTargets.Counting.EulerKroneckerGamma.Claim :=
  EulerKroneckerGammaReduction.gamma_iff_zero_derivative.mpr
    QuadraticLApproximationIdentification.zero_derivative

/-- The formula holds for every continuation satisfying the paper's defining
conditions, not just for a chosen representative. -/
theorem of_continuation {Z : ℂ → ℂ} {γ : ℂ}
    (h : CubicTargets.Counting.AsymptoticPolynomialCount.EulerKronecker Z γ) :
    γ = (AsymptoticConstantsData.classicalEulerKronecker : ℂ) :=
  (EulerKroneckerCalculation.unique h).trans evaluation

end Cubic.Counting.EulerKroneckerGamma
