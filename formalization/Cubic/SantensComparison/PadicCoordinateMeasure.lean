import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Additive measure in an integral two-coordinate chart. Reduction modulo p
has p² equal-mass fibers. This supplies the bad-prime coordinate volume without
assigning the desired volume to the congruence subgroup by definition. -/

noncomputable section

namespace Cubic.SantensComparison.PadicCoordinateMeasure

open MeasureTheory TopologicalSpace

variable (p : ℕ) [Fact p.Prime]

abbrev Coordinates := ℤ_[p] × ℤ_[p]

scoped instance : MeasurableSpace (Coordinates p) := borel (Coordinates p)
scoped instance : BorelSpace (Coordinates p) := ⟨rfl⟩

def coordinateDomain : PositiveCompacts (Coordinates p) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

def measure : Measure (Coordinates p) := Measure.addHaarMeasure (coordinateDomain p)

instance : (measure p).IsAddHaarMeasure := by unfold measure; infer_instance
instance : IsProbabilityMeasure (measure p) :=
  ⟨show measure p Set.univ = 1 from Measure.addHaarMeasure_self⟩

def reduction : Coordinates p →+ (ZMod p × ZMod p) where
  toFun x := (PadicInt.toZMod x.1, PadicInt.toZMod x.2)
  map_zero' := by simp
  map_add' a b := by ext <;> simp

theorem reduction_surjective : Function.Surjective (reduction p) := by
  rintro ⟨a,b⟩
  obtain ⟨x,hx⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p) a
  obtain ⟨y,hy⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p) b
  exact ⟨(x,y), Prod.ext hx hy⟩

theorem reduction_kernel (x : Coordinates p) :
    x ∈ (reduction p).ker ↔ ‖x.1‖ < 1 ∧ ‖x.2‖ < 1 := by
  change (PadicInt.toZMod x.1,PadicInt.toZMod x.2) = 0 ↔ _
  rw [Prod.ext_iff]
  change (PadicInt.toZMod x.1 = 0 ∧ PadicInt.toZMod x.2 = 0) ↔ _
  simp only [← RingHom.mem_ker, PadicInt.ker_toZMod,
    IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem measurable_kernel : MeasurableSet ((reduction p).ker : Set (Coordinates p)) := by
  have he : ((reduction p).ker : Set (Coordinates p)) =
      {x | ‖x.1‖ < 1} ∩ {x | ‖x.2‖ < 1} := Set.ext (reduction_kernel p)
  rw [he]
  exact (isOpen_lt continuous_fst.norm continuous_const).measurableSet.inter
    (isOpen_lt continuous_snd.norm continuous_const).measurableSet

theorem kernel_index : (reduction p).ker.index = p^2 := by
  rw [AddSubgroup.index_ker, (reduction p).range_eq_top_of_surjective (reduction_surjective p)]
  simp [Nat.card_eq_fintype_card, Fintype.card_prod, pow_two]

theorem kernel_mass : (measure p).real ((reduction p).ker : Set (Coordinates p)) =
    1 / (p : ℝ)^2 := by
  letI : (reduction p).ker.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr (by
    rw [kernel_index]
    exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  have h := MeasureTheory.AddSubgroup.index_mul_measure (reduction p).ker
    (measurable_kernel p) (measure p)
  rw [kernel_index, measure_univ] at h
  have hr := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_one,
    Nat.cast_pow, Measure.real] at hr ⊢
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact (eq_div_iff (pow_ne_zero 2 hp)).mpr (by simpa [mul_comm] using hr)

theorem fiber_mass (a : Coordinates p) :
    (measure p).real {x | reduction p x = reduction p a} = 1/(p:ℝ)^2 := by
  have he : {x | reduction p x = reduction p a} =
      (fun x => -a+x) ⁻¹' ((reduction p).ker : Set (Coordinates p)) := by
    ext x
    change reduction p x = reduction p a ↔ reduction p (-a+x) = 0
    rw [map_add, map_neg, neg_add_eq_zero]
    exact eq_comm
  rw [he, Measure.real, measure_preimage_add]
  exact kernel_mass p

theorem reduction_eq_iff (x a : Coordinates p) :
    reduction p x = reduction p a ↔ (p : ℤ_[p]) ∣ x.1-a.1 ∧ (p : ℤ_[p]) ∣ x.2-a.2 := by
  rw [← sub_eq_zero, ← map_sub]
  change x-a ∈ (reduction p).ker ↔ _
  rw [reduction_kernel]
  simp only [Prod.fst_sub, Prod.snd_sub, PadicInt.norm_lt_one_iff_dvd]

theorem measurable_fiber (a : Coordinates p) :
    MeasurableSet {x | reduction p x = reduction p a} := by
  have he : {x | reduction p x = reduction p a} =
      (fun x => -a+x) ⁻¹' ((reduction p).ker : Set (Coordinates p)) := by
    ext x
    change reduction p x = reduction p a ↔ reduction p (-a+x) = 0
    rw [map_add, map_neg, neg_add_eq_zero]
    exact eq_comm
  rw [he]
  exact (measurable_kernel p).preimage (measurable_const_add _)

end Cubic.SantensComparison.PadicCoordinateMeasure
