import Cubic.PoissonSummation.CyclotomicIntegerLocal
import Cubic.QuadraticCorrespondence.RationalParameterBaseChange
import Cubic.PoissonSummation.RationalAdelicEmbedding
import Cubic.PoissonSummation.AdelicCompactQuotient

/-!
# Reduction of actual rational unit points

Transfer the global six-unit calculation to original rational torus points.
The ramified local parameter is proved to be the base change of the global
parameter; its compact-unit reduction is exactly the specified global reduction.
-/

noncomputable section

namespace Cubic.PoissonSummation.RationalUnitReduction

open NumberField
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicField CyclotomicIntegerUnits RationalParameterBaseChange
open RationalAdelicEmbedding
open scoped TensorProduct RationalQuotientGroup

def rationalUnit : Integersˣ →* Points :=
  parameterEquiv.symm.toMonoidHom.comp (Units.map (algebraMap Integers E))

theorem rationalUnit_injective : Function.Injective rationalUnit := by
  intro u v h
  have h' := congrArg parameterEquiv h
  change parameterEquiv (parameterEquiv.symm (Units.map (algebraMap Integers E) u)) =
    parameterEquiv (parameterEquiv.symm (Units.map (algebraMap Integers E) v)) at h'
  simp only [MulEquiv.apply_symm_apply] at h'
  apply Units.ext
  exact RingOfIntegers.coe_injective (congrArg Units.val h')

/-- The six global units lie in every local maximal compact, including the infinite place. -/
theorem diagonal_rationalUnit_mem_maximalCompact (u : Integersˣ) :
    diagonal (rationalUnit u) ∈ AdelicCompactQuotient.maximalCompact := by
  constructor
  · let f := ArchimedeanHaar.coordinateHom.comp ((baseChange ℝ).comp rationalUnit)
    have h : f u ^ 6 = 1 := by simpa only [map_pow, map_one] using congrArg f (unit_pow_six u)
    have ha := congrArg Multiplicative.toAdd h
    change (6 : ℕ) • ArchimedeanQuotientLogarithm.coordinate
      (baseChange ℝ (rationalUnit u)) = 0 at ha
    change ArchimedeanQuotientLogarithm.coordinate (baseChange ℝ (rationalUnit u)) = 0
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] using ha
  · intro p
    exact (QuotientFiniteFourierProduct.family p).maximal
      ((localPoint p).comp rationalUnit).range
      (Set.finite_range ((localPoint p).comp rationalUnit)).isCompact ⟨u, rfl⟩

theorem ramifiedParameter_baseChange (P : Points) :
    RamifiedQuotientLogarithm.localPoint (baseChange ℚ_[3] P) =
      Units.map toLocalField.toMonoidHom (parameterEquiv P) := by
  have h : RamifiedQuotientLogarithm.place.toAlgHom.comp (fieldInclusion ℚ_[3]) =
      toLocalField := (zeta_primitive.powerBasis ℚ).algHom_ext (by
    rw [IsPrimitiveRoot.powerBasis_gen]
    change RamifiedQuotientLogarithm.place (zeta ⊗ₜ[ℚ] (1 : ℚ_[3])) = toLocalField zeta
    rw [RamifiedQuotientLogarithm.place_zeta, toLocalField_zeta])
  change Units.map RamifiedQuotientLogarithm.place.toMonoidHom
    (RationalQuotientGroup.quotientRestrictionScalarsMulEquiv ℚ_[3]
      ((Algebra.ofId ℚ ℚ_[3]).comp P)) = _
  rw [parameter_baseChange]
  apply Units.ext
  exact DFunLike.congr_fun h (parameterEquiv P : E)

def localUnit : Integersˣ →* CyclotomicRamifiedField.Points :=
  Units.map (toLocalField.toRingHom.comp (algebraMap Integers E))

theorem localPoint_rationalUnit (u : Integersˣ) :
    RamifiedQuotientLogarithm.localPoint (baseChange ℚ_[3] (rationalUnit u)) = localUnit u := by
  rw [ramifiedParameter_baseChange]
  change Units.map toLocalField.toMonoidHom
    (parameterEquiv (parameterEquiv.symm (Units.map (algebraMap Integers E) u))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

def localCompactUnit : Integersˣ →* CyclotomicRamifiedField.compactUnits :=
  localUnit.codRestrict _ (fun u => by
    rw [CyclotomicRamifiedField.mem_compactUnits_iff_norm_one]
    exact norm_unit_image (toLocalField.toRingHom.comp (algebraMap Integers E)) u)

theorem compactUnitsEquiv_localCompactUnit (u : Integersˣ) :
    RamifiedLocalModel.compactUnitsEquiv (localCompactUnit u) =
      Units.map toLocalOrder.toMonoidHom u := by
  apply Units.ext
  apply CyclotomicRamifiedField.integralEmbedding_injective
  rw [RamifiedLocalModel.compactUnitsEquiv_val]
  exact (integralEmbedding_toLocalOrder (u : Integers)).symm

/-- The residue of the actual local unit is the global arithmetic reduction. -/
theorem reduction_localCompactUnit (u : Integersˣ) :
    CyclotomicRamifiedReduction.reductionUnits
      (RamifiedLocalModel.compactUnitsEquiv (localCompactUnit u)) = reductionUnits u := by
  rw [compactUnitsEquiv_localCompactUnit]
  rfl

/-- The six global unit points meet the paper's ramified level only in the identity. -/
theorem localCompactUnit_mem_congruence_iff (u : Integersˣ) :
    localCompactUnit u ∈ RamifiedLocalModel.congruenceSubgroup ↔ u = 1 := by
  change CyclotomicRamifiedReduction.reductionUnits
    (RamifiedLocalModel.compactUnitsEquiv (localCompactUnit u)) = 1 ↔ _
  rw [reduction_localCompactUnit, reductionUnits_eq_one_iff]

end Cubic.PoissonSummation.RationalUnitReduction
