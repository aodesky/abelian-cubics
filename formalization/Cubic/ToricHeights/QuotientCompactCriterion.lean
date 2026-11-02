import Cubic.ToricHeights.QuotientLocalHaar
import Cubic.ToricHeights.QuotientLocalIntegrality

/-!
# Compactness from integrality of a point and its inverse

At unramified primes, the original coefficient cutoff is a pointed valuation
cone. Requiring both a point and its inverse to lie in this cutoff forces the
valuation to vanish. This criterion puts rational points in the maximal
compact at almost every prime using only denominators of original functions.
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientCompactCriterion

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois
open Cubic.PoissonSummation QuotientLocalIntegrality QuotientLocalHaar
open scoped RationalQuotientGroup

variable (p : ℕ) [Fact p.Prime]

theorem split_mem_compact_of_integral [Fact (p % 3 = 1)]
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ coefficientLocus p) (hPi : P⁻¹ ∈ coefficientLocus p) :
    P ∈ splitCompactUnits p := by
  have hp : p ≠ 3 := by have := (Fact.out : p % 3 = 1); omega
  rw [split_mem_iff, SplitLocalIntegrality.coefficientLocus_eq_integralLocus p hp] at hP hPi
  rw [← QuotientLocalModels.splitEquiv_apply] at hP hPi
  change LatticeCone.InCone
    (SplitLocalModel.valuation p (QuotientLocalModels.splitEquiv p P)).toAdd at hP
  change LatticeCone.InCone
    (SplitLocalModel.valuation p (QuotientLocalModels.splitEquiv p P⁻¹)).toAdd at hPi
  rw [map_inv, map_inv] at hPi
  have h := (LatticeCone.inCone_iff _).mp hP
  have hi := (LatticeCone.inCone_iff _).mp hPi
  simp only [toAdd_inv, Prod.fst_neg, Prod.snd_neg] at hi
  change QuotientLocalModels.splitEquiv p P ∈ SplitLocalModel.compactUnits p
  rw [← SplitLocalModel.ker_valuation]
  change (SplitLocalModel.valuation p (QuotientLocalModels.splitEquiv p P)).toAdd = 0
  ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> omega

theorem inert_mem_compact_of_integral [Fact (p % 3 = 2)]
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p])
    (hP : P ∈ coefficientLocus p) (hPi : P⁻¹ ∈ coefficientLocus p) :
    P ∈ inertCompactUnits p := by
  rw [inert_mem_iff_norm, ← QuotientLocalModels.inertEquiv_apply] at hP hPi
  change QuotientLocalModels.inertEquiv p P ∈ CyclotomicInertField.compactUnits p
  rw [CyclotomicInertField.mem_compactUnits]
  exact ⟨hP, by simpa only [map_inv] using hPi⟩

end Cubic.ToricHeights.QuotientCompactCriterion
