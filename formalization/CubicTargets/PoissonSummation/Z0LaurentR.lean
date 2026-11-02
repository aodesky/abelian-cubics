import CubicTargets.PoissonSummation.LeadingTerms
import Cubic.PoissonSummation.EulerCorrectionData

namespace CubicTargets.PoissonSummation.Z0LaurentR

open Filter Asymptotics Cubic.PoissonSummation
open scoped Topology

def Claim : Prop := ∀ (D F : ℂ → ℂ) (μ c₂ c₁ : ℂ),
  LeadingTerms.Expansion D F μ c₂ c₁ →
  let r := DirichletCharacter.LFunction QuadraticDirichletCharacter.character 1
  let a := (4 / 9 : ℂ) * r ^ 2 * EulerCorrectionData.R 1
  (fun z : ℂ => F (2 * z) - a / (z - 1) ^ 2 -
      2 * a * (μ + (1 / 2 : ℂ) * (Real.log 3 : ℂ) +
        deriv EulerCorrectionData.R 1 / (2 * EulerCorrectionData.R 1)) / (z - 1))
    =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ))

end CubicTargets.PoissonSummation.Z0LaurentR
