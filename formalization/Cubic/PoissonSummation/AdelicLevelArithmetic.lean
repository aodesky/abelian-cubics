import Cubic.PoissonSummation.AdelicLevel
import Cubic.PoissonSummation.RationalCompactIntegers

/-!
# Rational intersection and representatives of the compact level

Use the actual global integer units and their specified ramified reduction.
This is the six-unit step of the proof of `lemma:KprimeGroup`; the separate
class-number argument for arbitrary adelic classes is still required.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicLevel

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicIntegerUnits RationalUnitReduction RationalCompactIntegers
open AdelicCompactQuotient RationalAdelicEmbedding
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology

theorem localUnit_mem_level_iff (u : Integersˣ) :
    localUnit u ∈ localLevelModel ↔ u = 1 := by
  constructor
  · rintro ⟨x, hx, he⟩
    have hxe : x = localCompactUnit u := Subtype.ext he
    exact (localCompactUnit_mem_congruence_iff u).mp (hxe ▸ hx)
  · rintro rfl
    simpa only [map_one] using localLevelModel.one_mem

theorem rationalUnit_mem_ramifiedLevel_iff (u : Integersˣ) :
    baseChange ℚ_[3] (rationalUnit u) ∈ ramifiedLevel ↔ u = 1 := by
  change QuotientLocalModels.ramifiedEquiv (baseChange ℚ_[3] (rationalUnit u)) ∈ localLevelModel ↔ _
  rw [QuotientLocalModels.ramifiedEquiv_apply, localPoint_rationalUnit, localUnit_mem_level_iff]

/-- Triviality of the actual finite rational intersection, with no archimedean condition needed. -/
theorem finiteDiagonal_mem_level_iff (P : Points) : finiteDiagonal P ∈ finiteLevel ↔ P = 1 := by
  constructor
  · intro h
    obtain ⟨u, rfl⟩ := (finite_compact_iff_integer_unit P).mp h.1
    have hu : u = 1 := (rationalUnit_mem_ramifiedLevel_iff u).mp h.2
    simp [hu]
  · rintro rfl
    simpa only [map_one] using finiteLevel.one_mem

theorem diagonal_mem_level_iff (P : Points) : diagonal P ∈ level ↔ P = 1 := by
  constructor
  · intro h
    exact (finiteDiagonal_mem_level_iff P).mp h.2
  · rintro rfl
    simpa only [map_one] using level.one_mem

/-- The residue map on the actual local maximal compact. -/
def compactReduction : CyclotomicRamifiedField.compactUnits →*
    CyclotomicRamifiedReduction.ResidueRingˣ :=
  CyclotomicRamifiedReduction.reductionUnits.comp RamifiedLocalModel.compactUnitsEquiv.toMonoidHom

theorem exists_local_unit_correction (x : CyclotomicRamifiedField.compactUnits) :
    ∃ u : Integersˣ, (localCompactUnit u)⁻¹ * x ∈ RamifiedLocalModel.congruenceSubgroup := by
  obtain ⟨u, hu⟩ := reductionUnits_surjective (compactReduction x)
  refine ⟨u, ?_⟩
  change compactReduction ((localCompactUnit u)⁻¹ * x) = 1
  rw [map_mul, map_inv]
  change (CyclotomicRamifiedReduction.reductionUnits
    (RamifiedLocalModel.compactUnitsEquiv (localCompactUnit u)))⁻¹ * compactReduction x = 1
  rw [reduction_localCompactUnit, hu, inv_mul_cancel]

/-- Every finite maximal-compact point has a global-unit translate at the congruence level. -/
theorem exists_finite_unit_correction (x : finiteCompact) :
    ∃ u : Integersˣ, (finiteDiagonal (rationalUnit u))⁻¹ * (x : FiniteAdelicData.Points) ∈
      finiteLevel := by
  let y : CyclotomicRamifiedField.compactUnits :=
    ⟨QuotientLocalModels.ramifiedEquiv (atThree x), x.property FiniteEulerProduct.primeThree⟩
  obtain ⟨u, hu⟩ := exists_local_unit_correction y
  refine ⟨u, ?_, ?_⟩
  · exact finiteCompact.mul_mem
      (finiteCompact.inv_mem (diagonal_rationalUnit_mem_maximalCompact u).2) x.property
  · change QuotientLocalModels.ramifiedEquiv
      (atThree ((finiteDiagonal (rationalUnit u))⁻¹ * (x : FiniteAdelicData.Points))) ∈ localLevelModel
    rw [map_mul, map_inv, atThree_finiteDiagonal, map_mul, map_inv,
      QuotientLocalModels.ramifiedEquiv_apply, localPoint_rationalUnit]
    exact ⟨(localCompactUnit u)⁻¹ * y, hu, rfl⟩

/-- The equality `Kmax = μmax K^{D₀}` in the paper, with representatives as original rational points. -/
theorem exists_unit_correction (x : maximalCompact) :
    ∃ u : Integersˣ, (diagonal (rationalUnit u))⁻¹ * (x : AdelicData.Points) ∈ level := by
  obtain ⟨u, hu⟩ := exists_finite_unit_correction ⟨x.val.2, x.property.2⟩
  refine ⟨u, ?_, hu⟩
  exact ArchimedeanHaar.coordinateHom.ker.mul_mem
    (ArchimedeanHaar.coordinateHom.ker.inv_mem (diagonal_rationalUnit_mem_maximalCompact u).1)
    x.property.1

def finiteLevelInCompact : Subgroup finiteCompact := finiteLevel.comap finiteCompact.subtype

def finiteUnit : Integersˣ →* finiteCompact :=
  (finiteDiagonal.comp rationalUnit).codRestrict _
    (fun u => (diagonal_rationalUnit_mem_maximalCompact u).2)

def finiteUnitQuotient : Integersˣ →* (finiteCompact ⧸ finiteLevelInCompact) :=
  (QuotientGroup.mk' finiteLevelInCompact).comp finiteUnit

theorem finiteUnitQuotient_bijective : Function.Bijective finiteUnitQuotient := by
  constructor
  · apply (injective_iff_map_eq_one finiteUnitQuotient).mpr
    intro u hu
    have h := (QuotientGroup.eq_one_iff (finiteUnit u)).mp hu
    change finiteDiagonal (rationalUnit u) ∈ finiteLevel at h
    apply rationalUnit_injective
    rw [map_one]
    exact (finiteDiagonal_mem_level_iff _).mp h
  · intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨u, hu⟩ := exists_finite_unit_correction x
      exact ⟨u, QuotientGroup.eq.mpr hu⟩

def finiteUnitQuotientEquiv : Integersˣ ≃* (finiteCompact ⧸ finiteLevelInCompact) :=
  MulEquiv.ofBijective finiteUnitQuotient finiteUnitQuotient_bijective

/-- The finite level has index six in the full finite maximal compact. -/
theorem finiteLevelInCompact_index : finiteLevelInCompact.index = 6 :=
  (Nat.card_congr finiteUnitQuotientEquiv.toEquiv).symm.trans card_units

end Cubic.PoissonSummation.AdelicLevel
