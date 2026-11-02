import Cubic.PoissonSummation.AdelicRepresentativeRegion

/-!
# The rational diagonal is countable and discrete

The open finite congruence level meets the rational diagonal only in one.
This supplies the discreteness needed for counting-measure unfolding, without
using the still-unproved covering property of the representative region.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicRationalTopology

open Set
open Cubic.QuadraticCorrespondence
open RationalAdelicEmbedding AdelicLevel
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology
  AdelicHeightZetaData

scoped instance : Countable Points := by
  letI : Countable CyclotomicField.E :=
    (CyclotomicField.zeta_primitive.powerBasis ℚ).basis.repr.injective.countable
  letI : Countable CyclotomicField.Eˣ :=
    (show Function.Injective (Units.val : CyclotomicField.Eˣ → CyclotomicField.E)
      from Units.val_injective).countable
  exact RationalParameterBaseChange.parameterEquiv.injective.countable

open scoped AdelicRationalTopology

scoped instance : Countable diagonal.range := by
  exact Set.Countable.to_subtype (Set.countable_range diagonal)

theorem preimage_representativeRegion :
    diagonal.range.subtype ⁻¹' representativeRegion = ({1} : Set diagonal.range) := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, hP⟩ := x.property
    have hc : finiteDiagonal P ∈ finiteLevel := by
      change (diagonal P).2 ∈ finiteLevel
      rw [hP]
      exact hx.2
    have hP1 := (finiteDiagonal_mem_level_iff P).mp hc
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    change (x : AdelicData.Points) = 1
    rw [← hP, hP1, map_one]
  · rintro rfl
    exact ⟨mem_univ _, finiteLevel.one_mem⟩

scoped instance : DiscreteTopology diagonal.range := by
  apply discreteTopology_of_isOpen_singleton_one
  rw [← preimage_representativeRegion]
  exact isOpen_representativeRegion.preimage continuous_subtype_val

end Cubic.PoissonSummation.AdelicRationalTopology
