import Cubic.ToricHeights.QuotientFiniteCharacter
import Cubic.ToricHeights.QuotientLocalHaar

/-!
# Compact triviality of the original finite height and logarithm

The restricted-product construction needs these facts before its products and
sums can be defined: local heights and characters equal one on the maximal
compact, and local logarithms vanish there. No integrality cutoff is imposed.
In particular, at three the maximal compact here is larger than `1+3O`.
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientFiniteCompact

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois
open Cubic.OrbitParametrization.CocharacterLattice
open QuotientFiniteHeight QuotientFiniteCharacter QuotientLocalHaar
open LocalLogarithmNormalization
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

variable (p : ℕ) [Fact p.Prime]

section Split
variable [Fact (p % 3 = 1)]

private theorem split_valuation_eq_one (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ splitCompactUnits p) :
    SplitLocalModel.valuation p (SplitQuotientLogarithm.localPoint p P) = 1 := by
  change QuotientLocalModels.splitEquiv p P ∈ SplitLocalModel.compactUnits p at hP
  rw [QuotientLocalModels.splitEquiv_apply] at hP
  change SplitQuotientLogarithm.localPoint p P ∈ (SplitLocalModel.valuation p).ker
  rwa [SplitLocalModel.ker_valuation]

theorem split_height_one (s₀ σ : ℂ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ splitCompactUnits p) : splitInverseHeight p s₀ σ P = 1 := by
  rw [splitInverseHeight_eq]
  simp [SplitLocalModel.inverseHeight, SplitLocalModel.rayCoordinates,
    split_valuation_eq_one p P hP, supportFunction]

theorem split_logarithm_zero (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ splitCompactUnits p) : splitLogarithm p P = 0 := by
  rw [splitLogarithm_eq]
  simp [SplitLocalModel.rayCoordinates, split_valuation_eq_one p P hP,
    normalizedLog, conjugateAverage]

theorem split_character_one (t : ℝ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ splitCompactUnits p) : splitCharacter p t P = 1 := by
  change Circle.exp (2 * Real.pi * spectralPairing t (splitLogarithm p P)) = 1
  simp [split_logarithm_zero p P hP, spectralPairing]

end Split

section Inert
variable [Fact (p % 3 = 2)]

private theorem inert_valuation_eq_one (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ inertCompactUnits p) :
    InertLocalModel.valuation p (InertQuotientLogarithm.localPoint p P) = 1 := by
  change QuotientLocalModels.inertEquiv p P ∈ InertLocalModel.compactUnits p at hP
  rw [QuotientLocalModels.inertEquiv_apply] at hP
  change InertQuotientLogarithm.localPoint p P ∈ (InertLocalModel.valuation p).ker
  rwa [InertLocalModel.ker_valuation]

theorem inert_height_one (s₀ σ : ℂ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ inertCompactUnits p) : inertInverseHeight p s₀ σ P = 1 := by
  rw [inertInverseHeight_eq]
  simp [InertLocalModel.inverseHeight, InertLocalModel.rayCoordinates,
    inert_valuation_eq_one p P hP, supportFunction]

theorem inert_logarithm_zero (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ inertCompactUnits p) : inertLogarithm p P = 0 := by
  rw [inertLogarithm_eq]
  simp [InertLocalModel.rayCoordinates, inert_valuation_eq_one p P hP, normalizedLog]

theorem inert_character_one (t : ℝ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ inertCompactUnits p) : inertCharacter p t P = 1 := by
  change Circle.exp (2 * Real.pi * spectralPairing t (inertLogarithm p P)) = 1
  simp [inert_logarithm_zero p P hP, spectralPairing]

end Inert

private theorem ramified_logarithmicOrder_zero (P : quotientFixedRing →ₐ[ℚ] ℚ_[3])
    (hP : P ∈ ramifiedCompactUnits) :
    RamifiedLocalModel.logarithmicOrder (RamifiedQuotientLogarithm.localPoint P) = 0 := by
  apply (RamifiedLocalModel.logarithmicOrder_eq_zero_iff _).mpr
  change QuotientLocalModels.ramifiedEquiv P ∈ RamifiedLocalModel.compactUnits at hP
  rwa [QuotientLocalModels.ramifiedEquiv_apply] at hP

theorem ramified_height_one (s₀ σ : ℂ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[3])
    (hP : P ∈ ramifiedCompactUnits) : ramifiedInverseHeight s₀ σ P = 1 := by
  rw [ramifiedInverseHeight_eq]
  simp [RamifiedLocalModel.inverseHeight, RamifiedLocalModel.rayCoordinates,
    ramified_logarithmicOrder_zero P hP, supportFunction]

theorem ramified_logarithm_zero (P : quotientFixedRing →ₐ[ℚ] ℚ_[3])
    (hP : P ∈ ramifiedCompactUnits) : ramifiedLogarithm P = 0 := by
  rw [ramifiedLogarithm_eq]
  simp [RamifiedLocalModel.rayCoordinates, ramified_logarithmicOrder_zero P hP, normalizedLog]

theorem ramified_character_one (t : ℝ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[3])
    (hP : P ∈ ramifiedCompactUnits) : ramifiedCharacter t P = 1 := by
  change Circle.exp (2 * Real.pi * spectralPairing t (ramifiedLogarithm P)) = 1
  simp [ramified_logarithm_zero P hP, spectralPairing]

end Cubic.ToricHeights.QuotientFiniteCompact
