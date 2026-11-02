import Cubic.QuadraticCorrespondence.CyclotomicRamified
import Cubic.QuadraticCorrespondence.CyclotomicLocalTopology
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The normed cyclotomic field over `ℚ₃`

As at inert primes, use the spectral extension norm on a type copy of the
irreducible polynomial quotient. The continuous tensor identification records
that this is the local algebra of the global cyclotomic field.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicRamifiedField

open scoped CyclotomicLocalAlgebra CyclotomicBaseChange

def Extension := CyclotomicLocalAlgebra.Model ℚ_[3]

local instance : Fact (Irreducible (Polynomial.cyclotomic 3 ℚ_[3])) :=
  ⟨CyclotomicRamified.field_irreducible⟩

instance : Field Extension := inferInstanceAs (Field (CyclotomicLocalAlgebra.Model ℚ_[3]))
instance : Algebra ℚ_[3] Extension :=
  inferInstanceAs (Algebra ℚ_[3] (CyclotomicLocalAlgebra.Model ℚ_[3]))
instance : CharZero Extension := Algebra.charZero_of_charZero ℚ_[3] Extension
instance : FiniteDimensional ℚ_[3] Extension :=
  inferInstanceAs (FiniteDimensional ℚ_[3] (CyclotomicLocalAlgebra.Model ℚ_[3]))

theorem finrank_extension : Module.finrank ℚ_[3] Extension = 2 :=
  CyclotomicLocalAlgebra.finrank_model

instance : NontriviallyNormedField Extension :=
  spectralNorm.nontriviallyNormedField ℚ_[3] Extension
instance : NormedSpace ℚ_[3] Extension := spectralNorm.normedSpace ℚ_[3] Extension
instance : IsUltrametricDist Extension :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (isNonarchimedean_spectralNorm (K := ℚ_[3]) (L := Extension))

@[simp]
theorem norm_algebraMap (a : ℚ_[3]) : ‖algebraMap ℚ_[3] Extension a‖ = ‖a‖ :=
  spectralAlgNorm_extends (K := ℚ_[3]) (L := Extension) a

instance : ProperSpace Extension := FiniteDimensional.proper ℚ_[3] Extension
instance : IsModuleTopology ℚ_[3] Extension := isModuleTopologyOfFiniteDimensional

def quotientEquiv : Extension ≃ₐ[ℚ_[3]] CyclotomicLocalAlgebra.Model ℚ_[3] := AlgEquiv.refl

def quotientContinuousEquiv : Extension ≃A[ℚ_[3]] CyclotomicLocalAlgebra.Model ℚ_[3] where
  __ := quotientEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap quotientEquiv.toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap quotientEquiv.symm.toLinearMap

def tensorContinuousEquiv : CyclotomicBaseChange.LocalAlgebra ℚ_[3] ≃A[ℚ_[3]] Extension :=
  (CyclotomicBaseChange.presentationContinuousEquiv ℚ_[3]).trans quotientContinuousEquiv.symm

abbrev Points := Extensionˣ

def tensorUnitsEquiv : (CyclotomicBaseChange.LocalAlgebra ℚ_[3])ˣ ≃ₜ* Points :=
  Units.mapContinuousMulEquiv {
    __ := tensorContinuousEquiv.toAlgEquiv.toMulEquiv
    __ := tensorContinuousEquiv.toHomeomorph }

/-- Both the element and its inverse lie in the closed unit ball. -/
def compactUnits : Subgroup Points := (Submonoid.unitClosedBall Extension).units

theorem mem_compactUnits (x : Points) :
    x ∈ compactUnits ↔ ‖(x : Extension)‖ ≤ 1 ∧ ‖((x⁻¹ : Points) : Extension)‖ ≤ 1 := by
  change (x : Extension) ∈ Metric.closedBall 0 1 ∧
    ((x⁻¹ : Points) : Extension) ∈ Metric.closedBall 0 1 ↔ _
  simp only [Metric.mem_closedBall, dist_zero_right]

theorem mem_compactUnits_iff_norm_one (x : Points) :
    x ∈ compactUnits ↔ ‖(x : Extension)‖ = 1 := by
  rw [mem_compactUnits, Units.val_inv_eq_inv_val, norm_inv,
    inv_le_one₀ (norm_pos_iff.mpr x.ne_zero)]
  exact le_antisymm_iff.symm

theorem isCompact_compactUnits : IsCompact (compactUnits : Set Points) := by
  apply Submonoid.units_isCompact
  exact isCompact_closedBall (0 : Extension) 1

theorem isOpen_compactUnits : IsOpen (compactUnits : Set Points) := by
  apply Submonoid.isOpen_units
  exact IsUltrametricDist.isOpen_closedBall (0 : Extension) one_ne_zero

theorem compact_subgroup_le (H : Subgroup Points) (hH : IsCompact (H : Set Points)) :
    H ≤ compactUnits := by
  obtain ⟨C, hC⟩ := (hH.image (continuous_norm.comp Units.continuous_val)).bddAbove
  have hnorm : ∀ x ∈ H, ‖(x : Extension)‖ ≤ 1 := by
    intro x hx
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge h)
    have hbound := hC (Set.mem_image_of_mem (fun u : Points => ‖(u : Extension)‖)
      (H.pow_mem hx n))
    simp only [Units.val_pow_eq_pow_val, norm_pow] at hbound
    exact (not_lt_of_ge hbound) hn
  intro x hx
  exact (mem_compactUnits x).mpr ⟨hnorm x hx, hnorm x⁻¹ (H.inv_mem hx)⟩

end Cubic.QuadraticCorrespondence.CyclotomicRamifiedField
