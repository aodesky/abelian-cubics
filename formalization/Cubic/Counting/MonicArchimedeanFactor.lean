import CubicTargets.Counting.GeneralMonic

/-!
# Proof of `eqn:monicArchimedeanFactor`

For real `u`, `3 + u² > 0`, so `u ↦ (3+u²)^z` is continuous (the base stays in the slit
plane) and hence integrable on `[-1, 1]` for every `z ∈ ℂ`.
-/

noncomputable section

namespace Cubic.Counting.MonicArchimedeanFactor

theorem base_mem_slitPlane (u : ℝ) : (((3 + u ^ 2 : ℝ)) : ℂ) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.mpr (by positivity)

theorem continuous_integrand (z : ℂ) :
    Continuous (fun u : ℝ => (((3 + u ^ 2 : ℝ)) : ℂ) ^ z) :=
  (Complex.continuous_ofReal.comp (by fun_prop)).cpow continuous_const base_mem_slitPlane

theorem «eqn:monicArchimedeanFactor» :
    CubicTargets.Counting.GeneralMonic.MonicArchimedeanFactorClaim := fun z =>
  (continuous_integrand z).intervalIntegrable _ _

end Cubic.Counting.MonicArchimedeanFactor
