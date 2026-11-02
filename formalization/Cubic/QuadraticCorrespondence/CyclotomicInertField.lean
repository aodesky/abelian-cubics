import Cubic.QuadraticCorrespondence.CyclotomicInert
import Cubic.QuadraticCorrespondence.CyclotomicLocalTopology
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The norm and topology at an inert place

Use mathlib's spectral norm on the irreducible cyclotomic quotient. A type copy
keeps these normed-field instances separate from the quotient's module
topology; `quotientContinuousEquiv` proves they agree.

The norm-one units form a compact open subgroup. `CyclotomicInertNorm.lean`
proves the integral-basis norm formula; `InertLocalValuation.lean` uses it to
construct the discrete valuation with its normalization on `p`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicInertField

open scoped CyclotomicLocalAlgebra CyclotomicBaseChange

variable (p : ℕ) [Fact p.Prime]

/-- The cyclotomic quotient, with a type copy for its extension norm. -/
def Extension := CyclotomicLocalAlgebra.Model ℚ_[p]

variable [Fact (p % 3 = 2)]

local instance : Fact (Irreducible (Polynomial.cyclotomic 3 ℚ_[p])) :=
  ⟨CyclotomicInert.field_irreducible p Fact.out⟩

instance : Field (Extension p) := inferInstanceAs (Field (CyclotomicLocalAlgebra.Model ℚ_[p]))

instance : Algebra ℚ_[p] (Extension p) :=
  inferInstanceAs (Algebra ℚ_[p] (CyclotomicLocalAlgebra.Model ℚ_[p]))

instance : CharZero (Extension p) := Algebra.charZero_of_charZero ℚ_[p] (Extension p)

instance : FiniteDimensional ℚ_[p] (Extension p) :=
  inferInstanceAs (FiniteDimensional ℚ_[p] (CyclotomicLocalAlgebra.Model ℚ_[p]))

theorem finrank_extension : Module.finrank ℚ_[p] (Extension p) = 2 :=
  CyclotomicLocalAlgebra.finrank_model

/-- The unique extension norm supplied by mathlib's spectral-norm construction. -/
instance : NontriviallyNormedField (Extension p) :=
  spectralNorm.nontriviallyNormedField ℚ_[p] (Extension p)

instance : NormedSpace ℚ_[p] (Extension p) :=
  spectralNorm.normedSpace ℚ_[p] (Extension p)

instance : IsUltrametricDist (Extension p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := Extension p))

@[simp]
theorem norm_algebraMap (a : ℚ_[p]) : ‖algebraMap ℚ_[p] (Extension p) a‖ = ‖a‖ :=
  spectralAlgNorm_extends (K := ℚ_[p]) (L := Extension p) a

/-- Finite dimension over the proper p-adic field gives compact closed balls. -/
instance : ProperSpace (Extension p) := FiniteDimensional.proper ℚ_[p] (Extension p)

instance : IsModuleTopology ℚ_[p] (Extension p) :=
  isModuleTopologyOfFiniteDimensional

/-- The normed field is a type copy of the polynomial quotient, as a `ℚ_p`-algebra. -/
def quotientEquiv : Extension p ≃ₐ[ℚ_[p]] CyclotomicLocalAlgebra.Model ℚ_[p] :=
  AlgEquiv.refl

/-- The extension norm gives the same topology as the quotient's natural module topology. -/
def quotientContinuousEquiv : Extension p ≃A[ℚ_[p]] CyclotomicLocalAlgebra.Model ℚ_[p] where
  __ := quotientEquiv p
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (quotientEquiv p).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap (quotientEquiv p).symm.toLinearMap

/-- Identification with the global field's local tensor algebra, including topology. -/
def tensorContinuousEquiv : CyclotomicBaseChange.LocalAlgebra ℚ_[p] ≃A[ℚ_[p]] Extension p :=
  (CyclotomicBaseChange.presentationContinuousEquiv ℚ_[p]).trans (quotientContinuousEquiv p).symm

/-- The inert local multiplicative group. -/
abbrev Points := (Extension p)ˣ

/-- The unit-group identification needed to compare with the paper's local torus. -/
def tensorUnitsEquiv : (CyclotomicBaseChange.LocalAlgebra ℚ_[p])ˣ ≃ₜ* Points p :=
  Units.mapContinuousMulEquiv {
    __ := (tensorContinuousEquiv p).toAlgEquiv.toMulEquiv
    __ := (tensorContinuousEquiv p).toHomeomorph }

/-- Units for which the element and its inverse are integral in the extension norm. -/
def compactUnits : Subgroup (Points p) := (Submonoid.unitClosedBall (Extension p)).units

theorem mem_compactUnits (x : Points p) :
    x ∈ compactUnits p ↔ ‖(x : Extension p)‖ ≤ 1 ∧ ‖((x⁻¹ : Points p) : Extension p)‖ ≤ 1 := by
  change (x : Extension p) ∈ Metric.closedBall 0 1 ∧
    ((x⁻¹ : Points p) : Extension p) ∈ Metric.closedBall 0 1 ↔ _
  simp only [Metric.mem_closedBall, dist_zero_right]

theorem mem_compactUnits_iff_norm_one (x : Points p) :
    x ∈ compactUnits p ↔ ‖(x : Extension p)‖ = 1 := by
  rw [mem_compactUnits, Units.val_inv_eq_inv_val, norm_inv,
    inv_le_one₀ (norm_pos_iff.mpr x.ne_zero)]
  exact le_antisymm_iff.symm

theorem isCompact_compactUnits : IsCompact (compactUnits p : Set (Points p)) := by
  apply Submonoid.units_isCompact
  exact isCompact_closedBall (0 : Extension p) 1

theorem isOpen_compactUnits : IsOpen (compactUnits p : Set (Points p)) := by
  apply Submonoid.isOpen_units
  exact IsUltrametricDist.isOpen_closedBall (0 : Extension p) one_ne_zero

/-- No compact subgroup of the multiplicative group contains a nonintegral unit. -/
theorem compact_subgroup_le (H : Subgroup (Points p)) (hH : IsCompact (H : Set (Points p))) :
    H ≤ compactUnits p := by
  obtain ⟨C, hC⟩ := (hH.image (continuous_norm.comp Units.continuous_val)).bddAbove
  have hnorm : ∀ x ∈ H, ‖(x : Extension p)‖ ≤ 1 := by
    intro x hx
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge h)
    have hbound := hC (Set.mem_image_of_mem (fun u : Points p => ‖(u : Extension p)‖)
      (H.pow_mem hx n))
    simp only [Units.val_pow_eq_pow_val, norm_pow] at hbound
    exact (not_lt_of_ge hbound) hn
  intro x hx
  exact (mem_compactUnits p x).mpr ⟨hnorm x hx, hnorm x⁻¹ (H.inv_mem hx)⟩

end Cubic.QuadraticCorrespondence.CyclotomicInertField
