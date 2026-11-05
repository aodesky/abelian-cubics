import Cubic.SantensComparison.ToricPicardData
import Cubic.SantensComparison.IntegralModelWeights
import Cubic.SantensComparison.UnramifiedGaugeVolume
import Cubic.SantensComparison.RamifiedHaarNormalization

/-! The local integrals and leading-constant expression for general model
and metric data on the quadratic torus. The rank-two permutation-Picard
case has Dedekind convergence factors and a circle as its real residue
stratum. Neither the count nor these integrals use their cubic evaluations.
The finite local integrals use the metric at that prime; the cone factor uses
the height class, which is read from the real-place support function. -/

noncomputable section

namespace Cubic.SantensComparison.ToricCountingData

open MeasureTheory ToricPairData ToricPicardData ToricMetricData
open Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open scoped Cubic.ToricHeights.SplitLocalModel Cubic.ToricHeights.InertLocalModel
  Cubic.ToricHeights.RamifiedLocalModel LogDifferentials

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance inertFact (p : InertPrimes) : Fact ((p.1 : ℕ)%3=2) := ⟨p.2⟩

def splitVolume (A : IntegralModel) (ψ : FiniteSupport) (a : ℝ) (k : ℤ) (p : SplitPrimes) : ℝ :=
  UnramifiedGaugeVolume.splitScale p *
    ∫ x, IntegralModelWeights.splitWeight A (ψ p.1) a k p x ∂UnramifiedGaugeVolume.splitMeasure p

def inertVolume (A : IntegralModel) (ψ : FiniteSupport) (a : ℝ) (k : ℤ) (p : InertPrimes) : ℝ :=
  UnramifiedGaugeVolume.inertScale p *
    ∫ x, IntegralModelWeights.inertWeight A (ψ p.1) a k p x ∂UnramifiedGaugeVolume.inertMeasure p

def ramifiedVolume (A : IntegralModel) (ψ : FiniteSupport) (a : ℝ) (k : ℤ) : ℝ :=
  (PicardArtinFactors.ramifiedPolynomial ((3:ℂ)^(-1:ℂ))).re *
    ∫ x, IntegralModelWeights.ramifiedWeight A (ψ three) a k x ∂RamifiedHaarNormalization.gaugeMeasure

def tau (A : IntegralModel) (ψ : FiniteSupport) (a : ℝ) (k : ℤ) : ℝ :=
  2 * NumberField.dedekindZeta_residue E *
    ((∏' p : SplitPrimes, splitVolume A ψ a k p) *
      ∏' p : InertPrimes, inertVolume A ψ a k p) *
        ramifiedVolume A ψ a k * LogDifferentials.boundaryResidueMeasure.real Set.univ

def coefficient {P : Pair} (L : Lattices P) (A : IntegralModel) (φ : Support)
    (ψ : FiniteSupport) (a : ℝ) (k : ℤ) : ℝ :=
  L.theta φ / (a * (Nat.factorial (2-1):ℝ)) * tau A ψ a k

end Cubic.SantensComparison.ToricCountingData
