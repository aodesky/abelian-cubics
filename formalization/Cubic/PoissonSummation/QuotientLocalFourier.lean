import Cubic.ToricHeights.QuotientFiniteCharacter
import Cubic.PoissonSummation.QuotientLocalMeasure
import Cubic.PoissonSummation.LocalFourierComparison
import Cubic.PoissonSummation.SplitLocalFourier
import Cubic.PoissonSummation.InertLocalFourier
import Cubic.PoissonSummation.RamifiedLocalFourier

/-!
# Finite Fourier integrals on the original quotient points

The carrier is the original descended invariant-ring point functor, with its
evaluation topology and normalized Haar measure. The height uses the original
character valuations, actual residue cardinalities and global degree; the
cutoff uses the original `e₂,e₃,δ`. The spectral character uses the weighted
local logarithm and `exp(2πi⟨m,ell⟩)`.

The proved measure-preserving comparisons transfer integrability and the three
local Fourier formulas. These local objects still require global adelic assembly
and identification with the paper's automorphic character family.
-/

noncomputable section

namespace Cubic.PoissonSummation.QuotientLocalFourier

open MeasureTheory
open Cubic.QuadraticCorrespondence CyclotomicTorusGalois
open Cubic.ToricHeights
open CubicTargets.PoissonSummation.FiniteFourierProduct
open FiniteEulerProduct LocalFourierComparison
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology QuotientLocalHaar
  SplitLocalModel InertLocalModel RamifiedLocalModel

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance splitFact (p : SplitPrimes) : Fact ((p.1 : ℕ) % 3 = 1) := ⟨p.2⟩
local instance inertFact (p : InertPrimes) : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩

/-- Original split local points and the splitting-field definition of the integrand. -/
def splitData (p : SplitPrimes) : LocalData where
  Carrier := quotientFixedRing →ₐ[ℚ] ℚ_[p.1]
  locallyCompact := (QuotientLocalModels.splitEquiv p.1).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  hausdorff := (QuotientLocalModels.splitEquiv p.1).toHomeomorph.isEmbedding.t2Space
  maxCompact := QuotientLocalHaar.splitCompactUnits p.1
  compact := QuotientLocalHaar.isCompact_splitCompactUnits p.1
  open_compact := QuotientLocalHaar.isOpen_splitCompactUnits p.1
  maximal := QuotientLocalHaar.split_compact_subgroup_le p.1
  measure := QuotientLocalHaar.splitMeasure p.1
  normalized := QuotientLocalHaar.splitMeasure_compactUnits p.1
  inverseHeight := QuotientFiniteHeight.splitInverseHeight p.1
  integralLocus := QuotientInvariantIntegrality.invariantLocus p.1
  measurable_integralLocus := QuotientLocalMeasure.measurableSet_invariantLocus p.1
  character := QuotientFiniteCharacter.splitCharacter p.1
  character_zero := QuotientFiniteCharacter.splitCharacter_zero p.1

/-- Every field needed for the split change of variables is proved. -/
def splitComparison (p : SplitPrimes) : Comparison (splitData p) (SplitLocalFourier.data p) where
  equiv := QuotientLocalModels.splitEquiv p.1
  measurePreserving := QuotientLocalHaar.split_measurePreserving p.1
  inverseHeight_eq := by
    intro s₀ σ P
    change QuotientFiniteHeight.splitInverseHeight p.1 s₀ σ P =
      SplitLocalModel.inverseHeight p.1 s₀ σ (QuotientLocalModels.splitEquiv p.1 P)
    rw [QuotientFiniteHeight.splitInverseHeight_eq, QuotientLocalModels.splitEquiv_apply]
  integralLocus_eq := by
    ext P
    change QuotientLocalModels.splitEquiv p.1 P ∈ SplitLocalIntegrality.coefficientLocus p.1 ↔
      P ∈ QuotientInvariantIntegrality.invariantLocus p.1
    rw [QuotientLocalModels.splitEquiv_apply]
    exact (QuotientInvariantIntegrality.split_mem_iff p.1 P).symm
  character_eq := QuotientFiniteCharacter.splitCharacter_eq p.1

/-- Integrability and the split Euler factor for the integral on original quotient points. -/
theorem integral_eq_splitFactor (p : SplitPrimes) (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Integrable (localIntegrand (splitData p) s₀ σ t) (splitData p).measure ∧
      localFourier (splitData p) s₀ σ t = splitFactor p (spectralParameter σ t) := by
  obtain ⟨hI, hF⟩ := SplitLocalFourier.integral_eq_splitFactor p s₀ σ t hσ
  exact ⟨(integrable_iff (splitComparison p) s₀ σ t).mpr hI,
    (localFourier_eq (splitComparison p) s₀ σ t).trans hF⟩

/-- Original inert local points, retaining the actual residue-field cardinality in the height. -/
def inertData (p : InertPrimes) : LocalData where
  Carrier := quotientFixedRing →ₐ[ℚ] ℚ_[p.1]
  locallyCompact := (QuotientLocalModels.inertEquiv p.1).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  hausdorff := (QuotientLocalModels.inertEquiv p.1).toHomeomorph.isEmbedding.t2Space
  maxCompact := QuotientLocalHaar.inertCompactUnits p.1
  compact := QuotientLocalHaar.isCompact_inertCompactUnits p.1
  open_compact := QuotientLocalHaar.isOpen_inertCompactUnits p.1
  maximal := QuotientLocalHaar.inert_compact_subgroup_le p.1
  measure := QuotientLocalHaar.inertMeasure p.1
  normalized := QuotientLocalHaar.inertMeasure_compactUnits p.1
  inverseHeight := QuotientFiniteHeight.inertInverseHeight p.1
  integralLocus := QuotientInvariantIntegrality.invariantLocus p.1
  measurable_integralLocus := QuotientLocalMeasure.measurableSet_invariantLocus p.1
  character := QuotientFiniteCharacter.inertCharacter p.1
  character_zero := QuotientFiniteCharacter.inertCharacter_zero p.1

def inertComparison (p : InertPrimes) : Comparison (inertData p) (InertLocalFourier.data p) where
  equiv := QuotientLocalModels.inertEquiv p.1
  measurePreserving := QuotientLocalHaar.inert_measurePreserving p.1
  inverseHeight_eq := by
    intro s₀ σ P
    change QuotientFiniteHeight.inertInverseHeight p.1 s₀ σ P =
      InertLocalModel.inverseHeight p.1 s₀ σ (QuotientLocalModels.inertEquiv p.1 P)
    rw [QuotientFiniteHeight.inertInverseHeight_eq, QuotientLocalModels.inertEquiv_apply]
  integralLocus_eq := by
    ext P
    change QuotientLocalModels.inertEquiv p.1 P ∈ InertLocalIntegrality.coefficientLocus p.1 ↔
      P ∈ QuotientInvariantIntegrality.invariantLocus p.1
    rw [QuotientLocalModels.inertEquiv_apply]
    exact (QuotientInvariantIntegrality.inert_mem_iff p.1 P).symm
  character_eq := QuotientFiniteCharacter.inertCharacter_eq p.1

/-- Integrability and the inert Euler factor on original quotient points, including at two. -/
theorem integral_eq_inertFactor (p : InertPrimes) (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Integrable (localIntegrand (inertData p) s₀ σ t) (inertData p).measure ∧
      localFourier (inertData p) s₀ σ t = inertFactor p (spectralParameter σ t) := by
  obtain ⟨hI, hF⟩ := InertLocalFourier.integral_eq_inertFactor p s₀ σ t hσ
  exact ⟨(integrable_iff (inertComparison p) s₀ σ t).mpr hI,
    (localFourier_eq (inertComparison p) s₀ σ t).trans hF⟩

/-- Original ramified local points, with the residue/global-degree height and logarithm. -/
def ramifiedData : LocalData where
  Carrier := quotientFixedRing →ₐ[ℚ] ℚ_[3]
  locallyCompact := QuotientLocalModels.ramifiedEquiv.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  hausdorff := QuotientLocalModels.ramifiedEquiv.toHomeomorph.isEmbedding.t2Space
  maxCompact := QuotientLocalHaar.ramifiedCompactUnits
  compact := QuotientLocalHaar.isCompact_ramifiedCompactUnits
  open_compact := QuotientLocalHaar.isOpen_ramifiedCompactUnits
  maximal := QuotientLocalHaar.ramified_compact_subgroup_le
  measure := QuotientLocalHaar.ramifiedMeasure
  normalized := QuotientLocalHaar.ramifiedMeasure_compactUnits
  inverseHeight := QuotientFiniteHeight.ramifiedInverseHeight
  integralLocus := QuotientInvariantIntegrality.invariantLocus 3
  measurable_integralLocus := QuotientLocalMeasure.measurableSet_invariantLocus 3
  character := QuotientFiniteCharacter.ramifiedCharacter
  character_zero := QuotientFiniteCharacter.ramifiedCharacter_zero

def ramifiedComparison : Comparison ramifiedData RamifiedLocalFourier.data where
  equiv := QuotientLocalModels.ramifiedEquiv
  measurePreserving := QuotientLocalHaar.ramified_measurePreserving
  inverseHeight_eq := by
    intro s₀ σ P
    change QuotientFiniteHeight.ramifiedInverseHeight s₀ σ P =
      RamifiedLocalModel.inverseHeight s₀ σ (QuotientLocalModels.ramifiedEquiv P)
    rw [QuotientFiniteHeight.ramifiedInverseHeight_eq, QuotientLocalModels.ramifiedEquiv_apply]
  integralLocus_eq := by
    ext P
    change QuotientLocalModels.ramifiedEquiv P ∈ RamifiedLocalIntegrality.coefficientLocus ↔
      P ∈ QuotientInvariantIntegrality.invariantLocus 3
    rw [QuotientLocalModels.ramifiedEquiv_apply]
    exact (QuotientInvariantIntegrality.ramified_mem_iff P).symm
  character_eq := QuotientFiniteCharacter.ramifiedCharacter_eq

/-- The exceptional factor on the original group, valid for all divisor and spectral parameters. -/
theorem integral_eq_one_sixth (s₀ σ : ℂ) (t : ℝ) :
    Integrable (localIntegrand ramifiedData s₀ σ t) ramifiedData.measure ∧
      localFourier ramifiedData s₀ σ t = 1 / 6 := by
  obtain ⟨hI, hF⟩ := RamifiedLocalFourier.integral_eq_one_sixth s₀ σ t
  exact ⟨(integrable_iff ramifiedComparison s₀ σ t).mpr hI,
    (localFourier_eq ramifiedComparison s₀ σ t).trans hF⟩

end Cubic.PoissonSummation.QuotientLocalFourier
