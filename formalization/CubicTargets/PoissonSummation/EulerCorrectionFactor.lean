import Cubic.PoissonSummation.EulerCorrectionData

namespace CubicTargets.PoissonSummation.EulerCorrectionFactor

open Cubic.PoissonSummation

/-- The displayed product has convergent factors on its stated domain and
agrees with the product used in the continuation proof. -/
def Claim : Prop :=
  (∀ z : ℂ, (1 / 2 : ℝ) < z.re →
    Summable (fun q : FiniteEulerProduct.InertPrimes =>
      ‖HeightZetaCorrectionProduct.inert q z - 1‖) ∧
    Summable (fun p : FiniteEulerProduct.SplitPrimes =>
      ‖HeightZetaCorrectionProduct.split p z - 1‖)) ∧
  ∀ z : ℂ, EulerCorrectionData.R z = HeightZetaCorrectionProduct.value z

end CubicTargets.PoissonSummation.EulerCorrectionFactor
