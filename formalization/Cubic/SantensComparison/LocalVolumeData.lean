import Cubic.PoissonSummation.SplitLocalFourier
import Cubic.PoissonSummation.InertLocalFourier
import Cubic.PoissonSummation.RamifiedLocalFourier

/-! The norm-weighted integrals on the actual local groups, with Haar mass one
on the maximal compact subgroup. The subsequent comparison with the differential
form measure must supply its normalization; these are not yet Tamagawa volumes. -/

noncomputable section

namespace Cubic.SantensComparison.LocalVolumeData

open MeasureTheory Cubic.ToricHeights Cubic.QuadraticCorrespondence
open Cubic.PoissonSummation.FiniteEulerProduct
open scoped SplitLocalModel InertLocalModel RamifiedLocalModel

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance inertFact (p : InertPrimes) : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩

def splitWeight (p : SplitPrimes) (x : SplitLocalModel.Points p.1) : ℝ :=
  (SplitLocalIntegrality.coefficientLocus p.1).indicator
    (fun x => ‖(x.1 : ℚ_[p.1]) * (x.2 : ℚ_[p.1])‖) x

def inertWeight (p : InertPrimes) (x : InertLocalModel.Points p.1) : ℝ :=
  (InertLocalIntegrality.coefficientLocus p.1).indicator
    (fun x => ‖(x : CyclotomicInertField.Extension p.1)‖ ^ 2) x

def ramifiedWeight (x : RamifiedLocalModel.Points) : ℝ :=
  RamifiedLocalIntegrality.coefficientLocus.indicator
    (fun x => ‖(x : CyclotomicRamifiedField.Extension)‖ ^ 2) x

def splitMoment (p : SplitPrimes) : ℝ := ∫ x, splitWeight p x ∂SplitLocalModel.measure p.1
def inertMoment (p : InertPrimes) : ℝ := ∫ x, inertWeight p x ∂InertLocalModel.measure p.1
def ramifiedMoment : ℝ := ∫ x, ramifiedWeight x ∂RamifiedLocalModel.measure

end Cubic.SantensComparison.LocalVolumeData
