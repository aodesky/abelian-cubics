import Cubic.QuadraticCorrespondence.CyclotomicField
import Cubic.QuadraticCorrespondence.CyclotomicRamifiedReduction
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

/-!
# Global units and their reduction at three

Arithmetic inputs to `prop:Lmap` and `lemma:KprimeGroup`. The integer ring is
mathlib's actual ring of integers of the global cyclotomic field. Its principal
ideal property and six-unit classification are reused from mathlib. The map to
the local integral order is fixed by the chosen cyclotomic generator, so the
residue calculation uses the same convention as the local height calculation.
-/

noncomputable section

namespace Cubic.PoissonSummation.CyclotomicIntegerUnits

open NumberField Polynomial
open Cubic.QuadraticCorrespondence
open CyclotomicField

abbrev Integers := 𝓞 E

/-- The class-number-one input used in the paper's idele-class argument. -/
theorem integers_principal : IsPrincipalIdealRing Integers :=
  IsCyclotomicExtension.Rat.three_pid E

def zetaInteger : Integers := zeta_primitive.toInteger

def zetaUnit : Integersˣ :=
  (zeta_primitive.toInteger_isPrimitiveRoot.isUnit (by decide)).unit

@[simp]
theorem coe_zetaUnit : (zetaUnit : Integers) = zetaInteger := rfl

/-- The six units asserted in the proof of `lemma:KprimeGroup`. -/
theorem units_exhaustive (u : Integersˣ) :
    u = 1 ∨ u = -1 ∨ u = zetaUnit ∨ u = -zetaUnit ∨
      u = zetaUnit ^ 2 ∨ u = -(zetaUnit ^ 2) := by
  simpa [zetaUnit] using
    IsCyclotomicExtension.Rat.Three.Units.mem zeta_primitive u

theorem zetaUnit_cube : zetaUnit ^ 3 = 1 := by
  apply Units.ext
  exact zeta_primitive.toInteger_isPrimitiveRoot.pow_eq_one

theorem unit_pow_six (u : Integersˣ) : u ^ 6 = 1 := by
  have hz : zetaInteger ^ 6 = 1 := by
    rw [zetaInteger, show 6 = 3 * 2 by decide, pow_mul,
      zeta_primitive.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  have hz₂ : (zetaInteger ^ 2) ^ 6 = 1 := by
    rw [← pow_mul, show 2 * 6 = 6 * 2 by decide, pow_mul, hz, one_pow]
  apply Units.ext
  rcases units_exhaustive u with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Units.val_pow_eq_pow_val, Units.val_one, Units.val_neg, coe_zetaUnit]
    norm_num [neg_pow, hz, hz₂]

def integralPowerBasis : PowerBasis ℤ Integers := zeta_primitive.integralPowerBasis

@[simp]
theorem integralPowerBasis_gen : integralPowerBasis.gen = zetaInteger :=
  zeta_primitive.integralPowerBasis_gen

theorem minpoly_zetaInteger : minpoly ℤ zetaInteger = cyclotomic 3 ℤ := by
  rw [← minpoly.algebraMap_eq (A := ℤ) (B' := E)
    (show Function.Injective (algebraMap Integers E) from Subtype.val_injective)]
  exact (cyclotomic_eq_minpoly zeta_primitive (by decide)).symm

/-- The global integer ring maps into the local integral order by `ζ ↦ ζ`. -/
def toLocalOrder : Integers →ₐ[ℤ] CyclotomicRamifiedReduction.IntegralModel :=
  integralPowerBasis.lift CyclotomicRamifiedReduction.zeta (by
    rw [integralPowerBasis_gen, minpoly_zetaInteger]
    simpa [cyclotomic_three] using CyclotomicRamifiedReduction.zeta_relation)

@[simp]
theorem toLocalOrder_zeta : toLocalOrder zetaInteger = CyclotomicRamifiedReduction.zeta := by
  conv_lhs => rw [← integralPowerBasis_gen]
  exact integralPowerBasis.lift_gen _ _

/-- Reduction through the actual local order, not an arbitrary map on six labels. -/
def reduction : Integers →+* CyclotomicRamifiedReduction.ResidueRing :=
  CyclotomicRamifiedReduction.reduction.comp toLocalOrder.toRingHom

@[simp]
theorem reduction_zeta : reduction zetaInteger = CyclotomicRamifiedReduction.residueZeta := by
  simp [reduction]

def reductionUnits : Integersˣ →* CyclotomicRamifiedReduction.ResidueRingˣ :=
  Units.map reduction

@[simp]
theorem reductionUnits_zeta_val :
    (reductionUnits zetaUnit : CyclotomicRamifiedReduction.ResidueRing) =
      CyclotomicRamifiedReduction.residueZeta := reduction_zeta

theorem reductionUnits_surjective : Function.Surjective reductionUnits := by
  intro u
  rcases CyclotomicRamifiedReduction.residue_units_exhaustive u with h | h | h | h | h | h
  · exact ⟨1, Units.ext (by simpa [reductionUnits] using h.symm)⟩
  · exact ⟨-1, Units.ext (by simpa [reductionUnits] using h.symm)⟩
  · exact ⟨zetaUnit, Units.ext (by simpa using h.symm)⟩
  · exact ⟨-zetaUnit, Units.ext (by simpa [reductionUnits] using h.symm)⟩
  · exact ⟨zetaUnit ^ 2, Units.ext (by simpa [reductionUnits] using h.symm)⟩
  · exact ⟨-(zetaUnit ^ 2), Units.ext (by simpa [reductionUnits] using h.symm)⟩

/-- No nonidentity global unit becomes one modulo three. -/
theorem reductionUnits_eq_one_iff (u : Integersˣ) : reductionUnits u = 1 ↔ u = 1 := by
  constructor
  · intro h
    have hv := congrArg Units.val h
    change reduction (u : Integers) = 1 at hv
    rcases units_exhaustive u with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    all_goals
      exfalso
      simp only [Units.val_neg, Units.val_one,
        Units.val_pow_eq_pow_val, map_neg, map_one, map_pow, coe_zetaUnit,
        reduction_zeta] at hv
      revert hv
      decide
  · rintro rfl
    exact map_one _

theorem reductionUnits_injective : Function.Injective reductionUnits :=
  (injective_iff_map_eq_one reductionUnits).mpr (fun u => (reductionUnits_eq_one_iff u).mp)

/-- The arithmetic isomorphism used to remove torsion at the level at three. -/
def residueUnitsEquiv : Integersˣ ≃* CyclotomicRamifiedReduction.ResidueRingˣ :=
  MulEquiv.ofBijective reductionUnits ⟨reductionUnits_injective, reductionUnits_surjective⟩

instance : Finite Integersˣ := Finite.of_injective reductionUnits reductionUnits_injective

theorem card_units : Nat.card Integersˣ = 6 :=
  (Nat.card_congr residueUnitsEquiv.toEquiv).trans
    CyclotomicRamifiedReduction.card_residue_units

end Cubic.PoissonSummation.CyclotomicIntegerUnits
