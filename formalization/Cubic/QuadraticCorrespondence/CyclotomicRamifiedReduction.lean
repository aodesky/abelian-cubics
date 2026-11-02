import Cubic.QuadraticCorrespondence.CyclotomicRamified
import Mathlib.Algebra.DualNumber
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.Index

/-!
# Reduction of the integral cyclotomic order at three

Reduce `ℤ₃[X]/(X²+X+1)` modulo three by sending the root to `1+ε` in
`𝔽₃[ε]/(ε²)`. This is the ramified quotient, with six units.
`CyclotomicRamifiedIntegers.lean` identifies this integral order with the
norm-integral subring of the local field before the index is used for Haar measure.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicRamifiedReduction

open Polynomial CyclotomicLocalAlgebra
open scoped DualNumber

/-- The integral polynomial order, before identifying it with the local integers. -/
abbrev IntegralModel := Model ℤ_[3]

/-- The nonreduced quotient at three; its nilpotent records ramification. -/
abbrev ResidueRing := DualNumber (ZMod 3)

instance : Fintype ResidueRing := inferInstanceAs (Fintype (ZMod 3 × ZMod 3))
instance : DecidableEq ResidueRing := inferInstanceAs (DecidableEq (ZMod 3 × ZMod 3))

def zeta : IntegralModel := AdjoinRoot.root (cyclotomic 3 ℤ_[3])

theorem zeta_relation : zeta ^ 2 + zeta + 1 = 0 := by
  simpa [zeta, cyclotomic_three] using AdjoinRoot.eval₂_root (cyclotomic 3 ℤ_[3])

theorem zeta_cube : zeta ^ 3 = 1 := by
  linear_combination (zeta - 1) * zeta_relation

/-- The cyclotomic generator is a unit of the integral order. -/
def zetaUnit : IntegralModelˣ where
  val := zeta
  inv := zeta ^ 2
  val_inv := by simpa [pow_succ, mul_comm] using zeta_cube
  inv_val := by simpa [pow_succ] using zeta_cube

def residueZeta : ResidueRing := 1 + ε

theorem residueZeta_relation : residueZeta ^ 2 + residueZeta + 1 = 0 := by decide

/-- Coefficient reduction and the image of the root specify the reduction map. -/
def reduction : IntegralModel →+* ResidueRing :=
  AdjoinRoot.lift ((algebraMap (ZMod 3) ResidueRing).comp PadicInt.toZMod)
    residueZeta (by simpa [cyclotomic_three] using residueZeta_relation)

@[simp]
theorem reduction_zeta : reduction zeta = residueZeta := AdjoinRoot.lift_root _

@[simp]
theorem reduction_scalar (a : ℤ_[3]) :
    reduction (algebraMap ℤ_[3] IntegralModel a) =
      algebraMap (ZMod 3) ResidueRing (PadicInt.toZMod a) :=
  AdjoinRoot.lift_of _

/-- Kernel-checked finite computation of the six residue units. -/
theorem card_residue_units : Nat.card ResidueRingˣ = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Every residue unit lifts to one of the six cyclotomic units. -/
theorem residue_units_exhaustive (u : ResidueRingˣ) :
    (u : ResidueRing) = 1 ∨ (u : ResidueRing) = -1 ∨
    (u : ResidueRing) = residueZeta ∨ (u : ResidueRing) = -residueZeta ∨
    (u : ResidueRing) = residueZeta ^ 2 ∨ (u : ResidueRing) = -(residueZeta ^ 2) := by
  revert u
  decide

def reductionUnits : IntegralModelˣ →* ResidueRingˣ := Units.map reduction

theorem reductionUnits_surjective : Function.Surjective reductionUnits := by
  intro u
  rcases residue_units_exhaustive u with h | h | h | h | h | h
  · exact ⟨1, Units.ext (by simpa [reductionUnits] using h.symm)⟩
  · exact ⟨-1, Units.ext (by simpa [reductionUnits] using h.symm)⟩
  · exact ⟨zetaUnit, Units.ext (by simpa [reductionUnits, zetaUnit] using h.symm)⟩
  · exact ⟨-zetaUnit, Units.ext (by simpa [reductionUnits, zetaUnit] using h.symm)⟩
  · exact ⟨zetaUnit ^ 2, Units.ext (by simpa [reductionUnits, zetaUnit] using h.symm)⟩
  · exact ⟨-(zetaUnit ^ 2), Units.ext (by simpa [reductionUnits, zetaUnit] using h.symm)⟩

/-- The congruence subgroup of the integral order's units. -/
def congruenceSubgroup : Subgroup IntegralModelˣ := reductionUnits.ker

theorem congruenceSubgroup_index : congruenceSubgroup.index = 6 := by
  calc
    _ = Nat.card ResidueRingˣ := Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective reductionUnits reductionUnits_surjective).toEquiv
    _ = 6 := card_residue_units

/-- Coordinates in the integral power basis. -/
def linear (a b : ℤ_[3]) : IntegralModel :=
  algebraMap ℤ_[3] IntegralModel a + algebraMap ℤ_[3] IntegralModel b * zeta

theorem exists_linear (x : IntegralModel) : ∃ a b : ℤ_[3], x = linear a b := by
  letI : Nontrivial IntegralModel := AdjoinRoot.nontrivial _ (by
    rw [degree_cyclotomic]
    decide)
  let pb := AdjoinRoot.powerBasis' (cyclotomic.monic 3 ℤ_[3])
  obtain ⟨f, hdeg, hf⟩ := pb.exists_eq_aeval x
  have hd : f.natDegree < 2 := by
    simpa only [pb, AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic] using hdeg
  have he := f.eq_X_add_C_of_degree_le_one
    (degree_le_of_natDegree_le (Nat.le_of_lt_succ hd))
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hf, he]
  simp [linear, pb, zeta, add_comm]

@[simp]
theorem reduction_linear_fst (a b : ℤ_[3]) :
    (reduction (linear a b)).fst = PadicInt.toZMod a + PadicInt.toZMod b := by
  simp only [linear, map_add, map_mul, reduction_scalar, reduction_zeta]
  simp [residueZeta, TrivSqZeroExt.algebraMap_eq_inl]

@[simp]
theorem reduction_linear_snd (a b : ℤ_[3]) :
    (reduction (linear a b)).snd = PadicInt.toZMod b := by
  simp only [linear, map_add, map_mul, reduction_scalar, reduction_zeta]
  simp [residueZeta, TrivSqZeroExt.algebraMap_eq_inl]

theorem reduction_surjective : Function.Surjective reduction := by
  intro x
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective PadicInt.toZMod (x.fst - x.snd)
  obtain ⟨b, hb⟩ := ZMod.ringHom_surjective PadicInt.toZMod x.snd
  refine ⟨linear a b, TrivSqZeroExt.ext ?_ ?_⟩ <;> simp [ha, hb]

private theorem scalar_reduction_eq_zero (a : ℤ_[3]) :
    PadicInt.toZMod a = 0 ↔ (3 : ℤ_[3]) ∣ a := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
  norm_num

/-- This is reduction modulo the ideal generated by three, not modulo the
maximal ideal generated by `ζ-1`. -/
theorem ker_reduction : RingHom.ker reduction = Ideal.span {(3 : IntegralModel)} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · obtain ⟨a, b, rfl⟩ := exists_linear x
    intro h
    have hb : PadicInt.toZMod b = 0 := by
      simpa using congrArg TrivSqZeroExt.snd h
    have ha : PadicInt.toZMod a = 0 := by
      simpa [hb] using congrArg TrivSqZeroExt.fst h
    obtain ⟨a', rfl⟩ := (scalar_reduction_eq_zero a).mp ha
    obtain ⟨b', rfl⟩ := (scalar_reduction_eq_zero b).mp hb
    refine ⟨linear a' b', ?_⟩
    simp only [linear, map_mul, map_ofNat]
    ring
  · rintro ⟨y, rfl⟩
    have hthree : reduction 3 = 0 := by
      rw [map_ofNat]
      decide
    rw [map_mul, hthree, zero_mul]

/-- An explicit presentation of the order modulo three. -/
def quotientEquiv : IntegralModel ⧸ Ideal.span {(3 : IntegralModel)} ≃+* ResidueRing :=
  (Ideal.quotEquivOfEq ker_reduction.symm).trans
    (RingHom.quotientKerEquivOfSurjective reduction_surjective)

/-- The kernel is exactly the units congruent to one modulo three. -/
theorem mem_congruenceSubgroup (u : IntegralModelˣ) :
    u ∈ congruenceSubgroup ↔ (3 : IntegralModel) ∣ ((u : IntegralModel) - 1) := by
  change reductionUnits u = 1 ↔ _
  rw [← Units.val_inj]
  change reduction (u : IntegralModel) = 1 ↔ _
  rw [← sub_eq_zero, ← map_one reduction, ← map_sub, ← RingHom.mem_ker,
    ker_reduction, Ideal.mem_span_singleton]

end Cubic.QuadraticCorrespondence.CyclotomicRamifiedReduction
