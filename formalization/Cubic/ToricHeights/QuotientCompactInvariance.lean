import Cubic.ToricHeights.QuotientFiniteCompact
import Cubic.ToricHeights.QuotientInvariantIntegrality

/-!
# Local compact invariance of heights and integral cutoffs

The height depends only on the valuation, on every cone of the support function.
Away from three the original integral cutoff also depends only on valuations.
The exceptional cutoff is a smaller subgroup; its invariance is handled at the
congruence level rather than asserted for the full maximal compact.
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientCompactInvariance

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois
open QuotientFiniteHeight QuotientLocalHaar
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

variable (p : ℕ) [Fact p.Prime]

section Split
variable [Fact (p % 3 = 1)]

theorem split_valuation_mul_compact (P k : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hk : k ∈ splitCompactUnits p) :
    SplitLocalModel.valuation p (SplitQuotientLogarithm.localPoint p (P * k)) =
      SplitLocalModel.valuation p (SplitQuotientLogarithm.localPoint p P) := by
  have hk' : SplitLocalModel.valuation p (QuotientLocalModels.splitEquiv p k) = 1 := by
    change QuotientLocalModels.splitEquiv p k ∈ (SplitLocalModel.valuation p).ker
    rwa [SplitLocalModel.ker_valuation]
  change SplitLocalModel.valuation p (QuotientLocalModels.splitEquiv p (P * k)) =
    SplitLocalModel.valuation p (QuotientLocalModels.splitEquiv p P)
  rw [map_mul, map_mul, hk', mul_one]

theorem split_height_mul_compact (s₀ σ : ℂ) (P k : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hk : k ∈ splitCompactUnits p) :
    splitInverseHeight p s₀ σ (P * k) = splitInverseHeight p s₀ σ P := by
  simp only [splitInverseHeight_eq, SplitLocalModel.inverseHeight,
    SplitLocalModel.rayCoordinates, split_valuation_mul_compact p P k hk]

theorem split_integral_mul_compact_iff (P k : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hk : k ∈ splitCompactUnits p) :
    P * k ∈ QuotientInvariantIntegrality.invariantLocus p ↔
      P ∈ QuotientInvariantIntegrality.invariantLocus p := by
  have hp : p ≠ 3 := by have := (Fact.out : p % 3 = 1); omega
  simp only [QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus,
    QuotientLocalIntegrality.split_mem_iff,
    SplitLocalIntegrality.coefficientLocus_eq_integralLocus p hp,
    SplitLocalModel.integralLocus, Set.mem_setOf_eq,
    split_valuation_mul_compact p P k hk]

end Split

section Inert
variable [Fact (p % 3 = 2)]

theorem inert_valuation_mul_compact (P k : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hk : k ∈ inertCompactUnits p) :
    InertLocalModel.valuation p (InertQuotientLogarithm.localPoint p (P * k)) =
      InertLocalModel.valuation p (InertQuotientLogarithm.localPoint p P) := by
  have hk' : InertLocalModel.valuation p (QuotientLocalModels.inertEquiv p k) = 1 := by
    change QuotientLocalModels.inertEquiv p k ∈ (InertLocalModel.valuation p).ker
    rwa [InertLocalModel.ker_valuation]
  change InertLocalModel.valuation p (QuotientLocalModels.inertEquiv p (P * k)) =
    InertLocalModel.valuation p (QuotientLocalModels.inertEquiv p P)
  rw [map_mul, map_mul, hk', mul_one]

theorem inert_height_mul_compact (s₀ σ : ℂ) (P k : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hk : k ∈ inertCompactUnits p) :
    inertInverseHeight p s₀ σ (P * k) = inertInverseHeight p s₀ σ P := by
  simp only [inertInverseHeight_eq, InertLocalModel.inverseHeight,
    InertLocalModel.rayCoordinates, inert_valuation_mul_compact p P k hk]

theorem inert_integral_mul_compact_iff (P k : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hk : k ∈ inertCompactUnits p) :
    P * k ∈ QuotientInvariantIntegrality.invariantLocus p ↔
      P ∈ QuotientInvariantIntegrality.invariantLocus p := by
  simp only [QuotientInvariantIntegrality.invariantLocus_eq_coefficientLocus,
    QuotientLocalIntegrality.inert_mem_iff,
    InertLocalIntegrality.coefficientLocus_eq_integralLocus,
    InertLocalModel.mem_integralLocus_iff_cone, inert_valuation_mul_compact p P k hk]

end Inert

theorem ramified_height_mul_compact (s₀ σ : ℂ) (P k : quotientFixedRing →ₐ[ℚ] ℚ_[3])
    (hk : k ∈ ramifiedCompactUnits) :
    ramifiedInverseHeight s₀ σ (P * k) = ramifiedInverseHeight s₀ σ P := by
  have hk' : RamifiedLocalModel.logarithmicOrder (QuotientLocalModels.ramifiedEquiv k) = 0 :=
    (RamifiedLocalModel.logarithmicOrder_eq_zero_iff _).mpr hk
  simp only [ramifiedInverseHeight_eq, RamifiedLocalModel.inverseHeight,
    RamifiedLocalModel.rayCoordinates, ← QuotientLocalModels.ramifiedEquiv_apply,
    map_mul, RamifiedLocalModel.logarithmicOrder_mul, hk', add_zero]

end Cubic.ToricHeights.QuotientCompactInvariance
