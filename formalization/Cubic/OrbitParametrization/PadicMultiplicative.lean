import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.LocallyConstant.Basic

/-!
# The multiplicative group of a p-adic field

This constructs the valuation exact sequence and maximal compact subgroup for
`ℚ_[p]ˣ`, using mathlib's p-adic field and its topology. These objects are the
factors of the split local coordinate model `ToricHeights.SplitLocalModel`.
-/

noncomputable section

namespace Cubic.OrbitParametrization.PadicMultiplicative

open Topology

variable (p : ℕ) [Fact p.Prime]

/-- The additive p-adic valuation, written multiplicatively on the target. -/
def valuation : ℚ_[p]ˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (Padic.valuation (x : ℚ_[p]))
  map_one' := by simp
  map_mul' x y := by
    change Multiplicative.ofAdd (Padic.valuation ((x : ℚ_[p]) * (y : ℚ_[p]))) = _
    rw [Padic.valuation_mul x.ne_zero y.ne_zero]
    rfl

/-- The standard uniformizer, as an element of the multiplicative group. -/
def uniformizer : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (NeZero.ne _)

@[simp]
theorem valuation_uniformizer : valuation p (uniformizer p) = Multiplicative.ofAdd 1 := by
  simp [valuation, uniformizer]

/-- Integral powers of the uniformizer realize every integral valuation. -/
theorem valuation_surjective : Function.Surjective (valuation p) := by
  intro n
  refine ⟨uniformizer p ^ n.toAdd, ?_⟩
  change Multiplicative.ofAdd (Padic.valuation (↑(uniformizer p ^ n.toAdd) : ℚ_[p])) = n
  simp [uniformizer, Padic.valuation_zpow]

/-- The integral units inside the field's multiplicative group. -/
def compactUnits : Subgroup ℚ_[p]ˣ := (PadicInt.subring p).toSubmonoid.units

theorem mem_compactUnits (x : ℚ_[p]ˣ) :
    x ∈ compactUnits p ↔ ‖(x : ℚ_[p])‖ ≤ 1 ∧ ‖((x⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := Iff.rfl

/-- Exactness at the local multiplicative group. -/
theorem ker_valuation : (valuation p).ker = compactUnits p := by
  ext x
  rw [mem_compactUnits, Padic.norm_le_one_iff_val_nonneg,
    Padic.norm_le_one_iff_val_nonneg]
  change (Padic.valuation (x : ℚ_[p]) = 0) ↔ _
  rw [Units.val_inv_eq_inv_val, Padic.valuation_inv]
  omega

theorem isCompact_compactUnits : IsCompact (compactUnits p : Set ℚ_[p]ˣ) := by
  apply Submonoid.units_isCompact
  exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace ℤ_[p]))

theorem isOpen_compactUnits : IsOpen (compactUnits p : Set ℚ_[p]ˣ) := by
  apply Submonoid.isOpen_units
  change IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1}
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

/-- Every compact subgroup lies in the integral units. A norm greater than one
would give an unbounded sequence of powers inside that compact subgroup. -/
theorem compact_subgroup_le (H : Subgroup ℚ_[p]ˣ) (hH : IsCompact (H : Set ℚ_[p]ˣ)) :
    H ≤ compactUnits p := by
  obtain ⟨C, hC⟩ := (hH.image (continuous_norm.comp Units.continuous_val)).bddAbove
  have hnorm : ∀ x ∈ H, ‖(x : ℚ_[p])‖ ≤ 1 := by
    intro x hx
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge h)
    have hbound := hC (Set.mem_image_of_mem (fun u : ℚ_[p]ˣ => ‖(u : ℚ_[p])‖)
      (H.pow_mem hx n))
    simp only [Units.val_pow_eq_pow_val, norm_pow] at hbound
    exact (not_lt_of_ge hbound) hn
  intro x hx
  exact (mem_compactUnits p x).mpr ⟨hnorm x hx, hnorm x⁻¹ (H.inv_mem hx)⟩

/-- The valuation is locally constant because its kernel is open. -/
theorem locallyConstant_valuation : IsLocallyConstant (valuation p) := by
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro g
  have hfiber : valuation p ⁻¹' {valuation p g} =
      (fun x => g⁻¹ * x) ⁻¹' ((valuation p).ker : Set ℚ_[p]ˣ) := by
    ext x
    change valuation p x = valuation p g ↔ valuation p (g⁻¹ * x) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact eq_comm
  rw [hfiber, ker_valuation]
  exact (isOpen_compactUnits p).preimage (continuous_const.mul continuous_id)

end Cubic.OrbitParametrization.PadicMultiplicative
