import Cubic.PoissonSummation.EulerCorrectionData
import Cubic.QuadraticCorrespondence.CyclotomicField
import Mathlib.NumberTheory.NumberField.DedekindZeta

namespace CubicTargets.PoissonSummation.Z0Factorization

open Cubic.PoissonSummation

/-- Equality on the domain of the genuine height and ideal-counting series. -/
def Claim : Prop := ∀ z : ℂ, 1 < z.re →
  EulerCorrectionData.Z0 z = (1 - (3 : ℂ) ^ (-z)) ^ 2 *
    NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E z ^ 2 *
      EulerCorrectionData.R z

end CubicTargets.PoissonSummation.Z0Factorization
