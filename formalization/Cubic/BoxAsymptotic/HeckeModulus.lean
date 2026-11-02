import Cubic.BoxAsymptotic.HeckeFiniteCharacter

/-! The modulus in the primary-generator character is the actual ideal `3O`.
This records the kernel and coprimality checks needed when applying the general
Hecke theory, rather than treating an arbitrary six-element group as a modulus.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeModulus

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.PrimaryGenerator Cubic.BoxAsymptotic.AngularIdealData
open Cubic.BoxAsymptotic.EisensteinCoordinates
open Cubic.Counting.EisensteinNormCount
open Cubic.QuadraticCorrespondence

theorem reduction_coord_zero (p : ℤ × ℤ) :
    reduction (coord p) = 0 ↔ (3 : ℤ) ∣ p.1 ∧ (3 : ℤ) ∣ p.2 := by
  rw [reduction_coord]
  have h : ((p.1 : ResidueRing) + p.2 * CyclotomicRamifiedReduction.residueZeta = 0) ↔
      (p.1 : ZMod 3) = 0 ∧ (p.2 : ZMod 3) = 0 := by
    simp only [TrivSqZeroExt.ext_iff]
    simp [CyclotomicRamifiedReduction.residueZeta]
    intro hb
    simp [hb]
  rw [h, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

theorem three_dvd_coord (p : ℤ × ℤ) :
    (3 : Integers) ∣ coord p ↔ (3 : ℤ) ∣ p.1 ∧ (3 : ℤ) ∣ p.2 := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨q, rfl⟩ := coord_surjective y
    have hq : coord ((3 : ℤ) • q) = 3 * coord q := by simpa using coord_smul 3 q
    rw [← hq] at hy
    have hp := coord_injective hy
    exact ⟨⟨q.1, congrArg Prod.fst hp⟩, ⟨q.2, congrArg Prod.snd hp⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨coord (a, b), ?_⟩
    have hq : coord ((3 : ℤ) • (a, b)) = 3 * coord (a, b) := by simpa using coord_smul 3 (a, b)
    rw [← hq]
    exact congrArg coord (Prod.ext ha hb)

theorem ker_reduction : RingHom.ker reduction = Ideal.span {(3 : Integers)} := by
  ext x
  obtain ⟨p, rfl⟩ := coord_surjective x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, reduction_coord_zero, three_dvd_coord]

theorem isPrimary_iff (x : Integers) : IsPrimary x ↔ (3 : Integers) ∣ x - 1 := by
  rw [IsPrimary, ← sub_eq_zero, ← map_one reduction, ← map_sub,
    ← RingHom.mem_ker, ker_reduction, Ideal.mem_span_singleton]

theorem reduction_isUnit_iff (p : ℤ × ℤ) :
    IsUnit (reduction (coord p)) ↔ ¬ (3 : ℤ) ∣ nrm p := by
  rw [reduction_coord, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  change IsUnit ((p.1 : ZMod 3) + p.2 * (1 + 0)) ↔ _
  simp only [add_zero, mul_one, isUnit_iff_ne_zero]
  have h : ∀ a b : ZMod 3, a + b ≠ 0 ↔ a ^ 2 - a * b + b ^ 2 ≠ 0 := by decide
  rw [h]
  have he : (p.1 : ZMod 3) ^ 2 - p.1 * p.2 + p.2 ^ 2 = ((nrm p : ℤ) : ZMod 3) := by
    simp [nrm]
  rw [he, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

theorem reduction_isUnit_iff_norm (x : Integers) :
    IsUnit (reduction x) ↔ ¬ 3 ∣ Ideal.absNorm (Ideal.span {x}) := by
  obtain ⟨p, rfl⟩ := coord_surjective x
  rw [reduction_isUnit_iff, Ideal.absNorm_span_singleton, norm_coord']
  exact not_congr (by simpa using
    (Int.natAbs_dvd_natAbs (a := (3 : ℤ)) (b := nrm p)).symm)

theorem primary_norm_prime_to_three {x : Integers} (hx : IsPrimary x) :
    ¬ 3 ∣ Ideal.absNorm (Ideal.span {x}) :=
  (reduction_isUnit_iff_norm x).mp (by rw [show reduction x = 1 from hx]; exact isUnit_one)

theorem reduction_surjective : Function.Surjective reduction := by
  intro y
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective y.fst
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective y.snd
  refine ⟨coord (a - b, b), ?_⟩
  rw [reduction_coord]
  apply TrivSqZeroExt.ext <;> simp [CyclotomicRamifiedReduction.residueZeta, ha, hb]

def quotientEquiv : Integers ⧸ Ideal.span {(3 : Integers)} ≃+* ResidueRing :=
  (Ideal.quotEquivOfEq ker_reduction.symm).trans
    (RingHom.quotientKerEquivOfSurjective reduction_surjective)

end Cubic.BoxAsymptotic.HeckeModulus
