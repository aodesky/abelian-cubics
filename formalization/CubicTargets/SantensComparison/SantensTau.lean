import Cubic.SantensComparison.ToricCountingData
import Cubic.SantensComparison.ToricPicardSpecialization

/-! The source theorem's actual coefficient and normalized local-volume product
in `eqn:santensTau`. Identification with the counting asymptotic is supplied by
the conditional `prop:santensConstant`. -/

namespace CubicTargets.SantensComparison.SantensTau
open Cubic.SantensComparison
open ToricMetricData ToricPicardSpecialization ToricCountingData
open Cubic.PoissonSummation.FiniteEulerProduct
open scoped LogDifferentials

def Claim : Prop :=
  coefficient paperLattices paperModel paperSupport (uniform paperSupport) 2 1 =
      tau paperModel (uniform paperSupport) 2 1 ∧
  tau paperModel (uniform paperSupport) 2 1 =
    2 * NumberField.dedekindZeta_residue Cubic.QuadraticCorrespondence.CyclotomicField.E *
      ((∏' p : SplitPrimes, splitVolume paperModel (uniform paperSupport) 2 1 p) *
       (∏' p : InertPrimes, inertVolume paperModel (uniform paperSupport) 2 1 p)) *
      ramifiedVolume paperModel (uniform paperSupport) 2 1 *
      LogDifferentials.boundaryResidueMeasure.real Set.univ ∧
  Summable (fun p : SplitPrimes => ‖splitVolume paperModel (uniform paperSupport) 2 1 p - 1‖) ∧
  Summable (fun p : InertPrimes => ‖inertVolume paperModel (uniform paperSupport) 2 1 p - 1‖)
end CubicTargets.SantensComparison.SantensTau
