import Cubic.QuadraticCorrespondence.CyclotomicRamifiedIntegers
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The exceptional congruence subgroup and local Haar measure

Construct the subgroup `1+3𝓞` of the ramified local compact units.
Its index six is transported from the explicit integral-order reduction,
using the proved identification with the norm-integral ring. The norm
description proves measurability independently of the algebraic presentation.
`RamifiedLocalHeight` constructs the height and spectral character on this
group; `QuotientLocalModels` compares it with the original local quotient.
-/

noncomputable section

namespace Cubic.ToricHeights.RamifiedLocalModel

open MeasureTheory TopologicalSpace
open Cubic.QuadraticCorrespondence
open CyclotomicRamifiedField

abbrev Points := CyclotomicRamifiedField.Points
abbrev compactUnits := CyclotomicRamifiedField.compactUnits

scoped instance : MeasurableSpace Points := borel Points
scoped instance : BorelSpace Points := ⟨rfl⟩

private theorem compactUnits_eq : compactUnits = integers.toSubmonoid.units := by
  ext x
  rw [mem_compactUnits]
  rfl

/-- Identify compact field units with units of the integral polynomial order. -/
def compactUnitsEquiv : compactUnits ≃* CyclotomicRamifiedReduction.IntegralModelˣ :=
  (MulEquiv.subgroupCongr compactUnits_eq).trans
    (integers.toSubmonoid.unitsEquivUnitsType.trans (Units.mapEquiv integralEquiv.symm.toMulEquiv))

theorem compactUnitsEquiv_val (x : compactUnits) :
    integralEmbedding ((compactUnitsEquiv x : CyclotomicRamifiedReduction.IntegralModelˣ) :
      CyclotomicRamifiedReduction.IntegralModel) = ((x : Points) : Extension) := by
  change ((integralEquiv (integralEquiv.symm _)) : Extension) = _
  rw [integralEquiv.apply_symm_apply]
  rfl

/-- The units congruent to one modulo `3𝓞`, inside the maximal compact. -/
def congruenceSubgroup : Subgroup compactUnits :=
  CyclotomicRamifiedReduction.congruenceSubgroup.comap compactUnitsEquiv.toMonoidHom

theorem congruenceSubgroup_index : congruenceSubgroup.index = 6 := by
  exact (CyclotomicRamifiedReduction.congruenceSubgroup.index_comap_of_surjective
    (f := compactUnitsEquiv.toMonoidHom) compactUnitsEquiv.surjective).trans
      CyclotomicRamifiedReduction.congruenceSubgroup_index

private theorem three_dvd_iff_norm (x : integers) :
    (3 : integers) ∣ x ↔ ‖(x : Extension)‖ ≤ 1 / 3 := by
  constructor
  · rintro ⟨y, rfl⟩
    change ‖(3 : Extension) * (y : Extension)‖ ≤ _
    rw [norm_mul, norm_three]
    have hy : ‖(y : Extension)‖ ≤ 1 := y.property
    linarith
  · intro hx
    have hy : (x : Extension) / 3 ∈ integers := by
      change ‖(x : Extension) / 3‖ ≤ 1
      rw [norm_div, norm_three]
      linarith
    refine ⟨⟨(x : Extension) / 3, hy⟩, ?_⟩
    apply Subtype.ext
    change (x : Extension) = 3 * ((x : Extension) / 3)
    have hthree : (3 : Extension) ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_three]; norm_num)
    field_simp [hthree]

/-- The congruence condition is the closed ball of radius `1/3` about one. -/
theorem mem_congruenceSubgroup (x : compactUnits) :
    x ∈ congruenceSubgroup ↔ ‖((x : Points) : Extension) - 1‖ ≤ 1 / 3 := by
  change compactUnitsEquiv x ∈ CyclotomicRamifiedReduction.congruenceSubgroup ↔ _
  rw [CyclotomicRamifiedReduction.mem_congruenceSubgroup,
    ← map_dvd_iff integralEquiv, map_ofNat, three_dvd_iff_norm]
  change ‖integralEmbedding ((compactUnitsEquiv x :
    CyclotomicRamifiedReduction.IntegralModelˣ) - 1)‖ ≤ 1 / 3 ↔ _
  rw [map_sub, map_one, compactUnitsEquiv_val]

theorem isClosed_congruenceSubgroup : IsClosed (congruenceSubgroup : Set compactUnits) := by
  have h : (congruenceSubgroup : Set compactUnits) =
      {x : compactUnits | ‖((x : Points) : Extension) - 1‖ ≤ 1 / 3} :=
    Set.ext mem_congruenceSubgroup
  rw [h]
  exact isClosed_le
    (((Units.continuous_val.comp continuous_subtype_val).sub continuous_const).norm)
    continuous_const

theorem measurableSet_congruenceSubgroup : MeasurableSet (congruenceSubgroup : Set compactUnits) :=
  isClosed_congruenceSubgroup.measurableSet

/-- The subgroup as a subset of the local multiplicative group. -/
def integralLocus : Set Points := Subtype.val '' (congruenceSubgroup : Set compactUnits)

theorem mem_integralLocus (x : Points) :
    x ∈ integralLocus ↔ x ∈ compactUnits ∧ ‖(x : Extension) - 1‖ ≤ 1 / 3 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.property, (mem_congruenceSubgroup u).mp hu⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, (mem_congruenceSubgroup ⟨x, hx⟩).mpr h, rfl⟩

/-- The small congruence ball automatically consists of integral units. -/
theorem mem_integralLocus_iff_norm (x : Points) :
    x ∈ integralLocus ↔ ‖(x : Extension) - 1‖ ≤ 1 / 3 := by
  rw [mem_integralLocus]
  refine ⟨And.right, fun hx => ⟨?_, hx⟩⟩
  rw [mem_compactUnits_iff_norm_one]
  have hadd (a b : Extension) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ :=
    isNonarchimedean_spectralNorm a b
  have hle : ‖(x : Extension)‖ ≤ 1 := by
    have h := hadd ((x : Extension) - 1) 1
    simp only [sub_add_cancel, norm_one] at h
    exact h.trans (max_le (by linarith) le_rfl)
  apply le_antisymm hle
  by_contra h
  have hlt : ‖(x : Extension)‖ < 1 := lt_of_not_ge h
  have hbound := hadd (x : Extension) (-((x : Extension) - 1))
  have heq : (x : Extension) + -((x : Extension) - 1) = 1 := by ring
  rw [heq, norm_one, norm_neg] at hbound
  exact (not_lt_of_ge hbound) (max_lt hlt (by linarith))

/-- The local locus is literally `1+3𝓞` in the field's multiplicative group. -/
theorem mem_integralLocus_iff_exists (x : Points) :
    x ∈ integralLocus ↔ ∃ a : integers, (x : Extension) = 1 + 3 * (a : Extension) := by
  rw [mem_integralLocus_iff_norm]
  constructor
  · intro hx
    have hint : (x : Extension) - 1 ∈ integers := by
      change ‖(x : Extension) - 1‖ ≤ 1
      linarith
    obtain ⟨a, ha⟩ := (three_dvd_iff_norm ⟨(x : Extension) - 1, hint⟩).mpr hx
    refine ⟨a, ?_⟩
    have h := congrArg Subtype.val ha
    change (x : Extension) - 1 = 3 * (a : Extension) at h
    linear_combination h
  · rintro ⟨a, ha⟩
    rw [ha, add_sub_cancel_left, norm_mul, norm_three]
    have hint : ‖(a : Extension)‖ ≤ 1 := a.property
    linarith

theorem integralLocus_subset : integralLocus ⊆ (compactUnits : Set Points) := by
  rintro x ⟨u, _, rfl⟩
  exact u.property

theorem measurableSet_integralLocus : MeasurableSet integralLocus :=
  (MeasurableEmbedding.subtype_coe isOpen_compactUnits.measurableSet).measurableSet_image.mpr
    measurableSet_congruenceSubgroup

def compactNeighborhood : PositiveCompacts Points where
  carrier := compactUnits
  isCompact' := isCompact_compactUnits
  interior_nonempty' := by
    rw [isOpen_compactUnits.interior_eq]
    exact ⟨1, compactUnits.one_mem⟩

/-- The local Haar measure gives the full unit group mass one. -/
def measure : Measure Points := Measure.haarMeasure compactNeighborhood

instance : measure.IsHaarMeasure := by unfold measure; infer_instance

theorem measure_compactUnits : measure compactUnits = 1 := Measure.haarMeasure_self

end Cubic.ToricHeights.RamifiedLocalModel
