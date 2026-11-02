import CubicTargets.Counting.IntroConstants
import Cubic.Counting.CountPolynomialNormalization

namespace Cubic.Counting.IntroConstants

theorem «eqn:introConstants» : CubicTargets.Counting.IntroConstants.Claim := by
  have hc := AsymptoticConstantsAssembly.constants
  refine ⟨Cubic.PoissonSummation.QuadraticZetaRegularization.value,
    EulerKroneckerCalculation.value, EulerKroneckerCalculation.genuine_constant,
    rfl, rfl, hc.simplified_product_absolute, hc.simplified_sum_absolute, ?_⟩
  have hpos : 0 < GeneralMonicData.Cconst := hc.positive
  rw [CountPolynomialNormalization.C_eq_alpha] at hpos
  linarith

end Cubic.Counting.IntroConstants
