import Cubic.SantensComparison.SantensMetric
import Cubic.SantensComparison.ToricCountingData
import Cubic.SantensComparison.ToricPicardSpecialization
import Cubic.PoissonSummation.IntegralHeightNormalization
import Cubic.PoissonSummation.IntegralPointComparison

/-! The height `H̃` in the proof of `prop:santensConstant`.

`H(·,1)` does not come from Santens's metrics: its finite local norms need not
lie in `p^ℤ`. At the primes only points of `U` occur, and `L=[D₀′]` is
trivial there. The paper gives `L` the metric in which the canonical section
has norm one at every prime and the metric of `H(·,1)` at the real place.
In the toric presentation this is the zero support function at each prime.
It is a Santens metric, and its height `H̃` is the real-place factor of
`H(·,1)`.

On the support of the integral weight, `H_p(P,1)=1` at every prime. Hence
`H̃` and `H(·,1)` define the same bounded integral points and the same finite
local integrals. Santens's theorem for `H̃` therefore gives the count and
constant for `H(·,1)`. -/

noncomputable section

namespace Cubic.SantensComparison.TrivialFiniteMetric

open ToricMetricData ToricMetricGeometry ToricPairData SantensMetric
open ToricPairApplicability ToricPicardSpecialization ToricCountingData IntegralModelWeights
open Cubic.PoissonSummation Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.ToricHeights ToricFanData Cubic.SurfaceGeometry.ResolutionData

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance splitFact (p : SplitPrimes) : Fact ((p.1 : ℕ)%3=1) := ⟨p.2⟩
local instance inertFact (p : InertPrimes) : Fact ((p.1 : ℕ)%3=2) := ⟨p.2⟩

/-- The metric in which the canonical section of `O(D₀′)` has norm one. -/
def trivialMetric : FiniteSupport := fun _ => 0

/-- The support function of `H(·,1)` vanishes on the rays of `U`, so the
canonical section of `O(D₀′)` trivializes `L` on `U`. -/
theorem paper_open_rays (i : Fin 9) (hi : i ∉ paperPair.boundary) :
    paperSupport (ambientCoordinates (paperPair.fan.realRay i))=0 := by
  change paperSupport (ambientCoordinates (paperFan.realRay i))=0
  fin_cases i <;> simp [paperPair] at hi <;>
    norm_num [paperSupport, supportFunction, ambientCoordinates, Fan.realRay,
      paper_ray, paperPair, paperFan, rays, detReal]

/-- The trivial metric at every prime is a Santens metric on `L`. -/
theorem finite_metric : FiniteMetric paperPair paperSupport trivialMetric where
  toric _ :=
    { continuous := continuous_const
      real := fun _ => rfl
      invariant := fun _ => rfl
      linear_on_cones := fun _ => ⟨(0,0),fun _ _ => by simp [trivialMetric]⟩ }
  open_rays _ i hi := (paper_open_rays i hi).symm
  values p x := ⟨0,by rw [zpow_zero]; exact finiteHeight_zero p x⟩
  integral := ⟨∅,0,fun _ => ⟨(0,0),fun _ _ => by simp⟩,fun _ _ => rfl⟩

/-- `H̃(P)=H_∞(P,1)`. -/
theorem height_trivial (P : AdelicData.Points) :
    height paperSupport trivialMetric P=infiniteHeight paperSupport P.1 := by
  rw [height]
  simp only [trivialMetric, finiteHeight_zero, tprod_one, mul_one]

/-- `H_p(P,1)=1` at every prime for a global integral point. -/
theorem integral_finite_height (P : AdelicHeightZetaData.RationalPoints)
    (hP : Integral paperModel P) (p : Nat.Primes) :
    finiteHeight paperSupport p ((RationalAdelicEmbedding.diagonal P).2 p)=1 := by
  have h := (IntegralPointComparison.integralPoint_iff P).mp ((paper_model P).mp hP) p
  rw [paper_finite_height]
  exact IntegralHeightNormalization.local_inverseHeight_one p (-1) _ h

/-- On integral points, `H̃=H(·,1)`. -/
theorem height_eq (P : AdelicHeightZetaData.RationalPoints) (hP : Integral paperModel P) :
    height paperSupport trivialMetric (RationalAdelicEmbedding.diagonal P)=
      height paperSupport (uniform paperSupport) (RationalAdelicEmbedding.diagonal P) := by
  rw [height_trivial, height]
  simp only [uniform, integral_finite_height P hP, tprod_one, mul_one]

theorem bounded_points (B : ℝ) :
    boundedPoints paperModel paperSupport trivialMetric B=
      boundedPoints paperModel paperSupport (uniform paperSupport) B := by
  ext P
  simp only [boundedPoints, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP,hB⟩
    exact ⟨hP,by rwa [← height_eq P hP]⟩
  · rintro ⟨hP,hB⟩
    exact ⟨hP,by rwa [height_eq P hP]⟩

theorem count_eq (B : ℝ) :
    count paperModel paperSupport trivialMetric B=
      count paperModel paperSupport (uniform paperSupport) B := by
  rw [count, count, bounded_points]

/-! The local integrals in the constant only see the integral loci, where
both local heights are one. -/

theorem split_weight (p : SplitPrimes) :
    splitWeight paperModel 0 2 1 p=splitWeight paperModel paperSupport 2 1 p := by
  ext x
  unfold splitWeight
  rw [paper_split_locus]
  by_cases hx : x ∈ SplitLocalIntegrality.coefficientLocus p.1
  · simp only [Set.indicator_of_mem hx, paper_split_height p x hx]
    simp [splitHeight]
  · simp [Set.indicator_of_notMem hx]

theorem inert_weight (p : InertPrimes) :
    inertWeight paperModel 0 2 1 p=inertWeight paperModel paperSupport 2 1 p := by
  ext x
  unfold inertWeight
  rw [paper_inert_locus]
  by_cases hx : x ∈ InertLocalIntegrality.coefficientLocus p.1
  · simp only [Set.indicator_of_mem hx, paper_inert_height p x hx]
    simp [inertHeight]
  · simp [Set.indicator_of_notMem hx]

theorem ramified_weight :
    ramifiedWeight paperModel 0 2 1=ramifiedWeight paperModel paperSupport 2 1 := by
  ext x
  unfold ramifiedWeight
  rw [paper_ramified_locus]
  by_cases hx : x ∈ RamifiedLocalIntegrality.coefficientLocus
  · simp only [Set.indicator_of_mem hx, paper_ramified_height x hx]
    simp [ramifiedHeight]
  · simp [Set.indicator_of_notMem hx]

theorem tau_eq : tau paperModel trivialMetric 2 1=tau paperModel (uniform paperSupport) 2 1 := by
  simp only [tau, splitVolume, inertVolume, ramifiedVolume, trivialMetric, uniform,
    split_weight, inert_weight, ramified_weight]

theorem coefficient_eq :
    coefficient paperLattices paperModel paperSupport trivialMetric 2 1=
      coefficient paperLattices paperModel paperSupport (uniform paperSupport) 2 1 := by
  rw [coefficient, coefficient, tau_eq]

end Cubic.SantensComparison.TrivialFiniteMetric
