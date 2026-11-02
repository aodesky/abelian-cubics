import Cubic.ToricHeights.QuotientLocalModels
import Cubic.PoissonSummation.HaarTransport

/-!
# Normalized Haar measures on the original local quotient

Use the Borel space of regular-function evaluation on the original quotient
points. Pulling back the local unit subgroups gives their maximal compact
subgroups: every compact subgroup is contained in these, as proved below.
Construct Haar measure on the original point space and normalize on that
compact subgroup. Haar uniqueness identifies its pushforward with the measure
used for each local Fourier calculation.
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientLocalHaar

open MeasureTheory
open Cubic.QuadraticCorrespondence CyclotomicTorusGalois
open Cubic.PoissonSummation
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology
  SplitLocalModel InertLocalModel RamifiedLocalModel

local instance unitsSecondCountable {R : Type*} [Monoid R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology Rˣ := by
  letI : SecondCountableTopology Rᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : R ≃ₜ Rᵐᵒᵖ).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

variable (p : ℕ) [Fact p.Prime]

scoped instance : MeasurableSpace (quotientFixedRing →ₐ[ℚ] ℚ_[p]) :=
  borel (quotientFixedRing →ₐ[ℚ] ℚ_[p])

scoped instance : BorelSpace (quotientFixedRing →ₐ[ℚ] ℚ_[p]) := ⟨rfl⟩

section Split

variable [Fact (p % 3 = 1)]

def splitCompactUnits : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[p]) :=
  (SplitLocalModel.compactUnits p).comap (QuotientLocalModels.splitEquiv p).toMonoidHom

theorem isCompact_splitCompactUnits : IsCompact (splitCompactUnits p : Set (quotientFixedRing →ₐ[ℚ] ℚ_[p])) :=
  (QuotientLocalModels.splitEquiv p).toHomeomorph.isCompact_preimage.mpr
    (SplitLocalModel.isCompact_compactUnits p)

theorem isOpen_splitCompactUnits : IsOpen (splitCompactUnits p : Set (quotientFixedRing →ₐ[ℚ] ℚ_[p])) :=
  (SplitLocalModel.isOpen_compactUnits p).preimage (QuotientLocalModels.splitEquiv p).continuous

theorem split_compact_subgroup_le (L : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[p]))
    (hL : IsCompact (L : Set (quotientFixedRing →ₐ[ℚ] ℚ_[p]))) : L ≤ splitCompactUnits p :=
  HaarTransport.compact_subgroup_le (QuotientLocalModels.splitEquiv p) _
    (SplitLocalModel.compact_subgroup_le p) L hL

/-- Haar measure on the original quotient at a split prime, with compact mass one. -/
def splitMeasure : Measure (quotientFixedRing →ₐ[ℚ] ℚ_[p]) :=
  HaarTransport.measure (QuotientLocalModels.splitEquiv p) (SplitLocalModel.compactNeighborhood p)

instance : (splitMeasure p).IsHaarMeasure := by unfold splitMeasure; infer_instance

theorem splitMeasure_compactUnits : splitMeasure p (splitCompactUnits p) = 1 :=
  HaarTransport.measure_preimage _ _

theorem split_measurePreserving :
    MeasurePreserving (QuotientLocalModels.splitEquiv p) (splitMeasure p) (SplitLocalModel.measure p) :=
  HaarTransport.measurePreserving _ _

end Split

section Inert

variable [Fact (p % 3 = 2)]

def inertCompactUnits : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[p]) :=
  (InertLocalModel.compactUnits p).comap (QuotientLocalModels.inertEquiv p).toMonoidHom

theorem isCompact_inertCompactUnits : IsCompact (inertCompactUnits p : Set (quotientFixedRing →ₐ[ℚ] ℚ_[p])) :=
  (QuotientLocalModels.inertEquiv p).toHomeomorph.isCompact_preimage.mpr
    (CyclotomicInertField.isCompact_compactUnits p)

theorem isOpen_inertCompactUnits : IsOpen (inertCompactUnits p : Set (quotientFixedRing →ₐ[ℚ] ℚ_[p])) :=
  (CyclotomicInertField.isOpen_compactUnits p).preimage (QuotientLocalModels.inertEquiv p).continuous

theorem inert_compact_subgroup_le (L : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[p]))
    (hL : IsCompact (L : Set (quotientFixedRing →ₐ[ℚ] ℚ_[p]))) : L ≤ inertCompactUnits p :=
  HaarTransport.compact_subgroup_le (QuotientLocalModels.inertEquiv p) _
    (CyclotomicInertField.compact_subgroup_le p) L hL

/-- Haar measure on the original quotient at an inert prime, with compact mass one. -/
def inertMeasure : Measure (quotientFixedRing →ₐ[ℚ] ℚ_[p]) :=
  HaarTransport.measure (QuotientLocalModels.inertEquiv p) (InertLocalModel.compactNeighborhood p)

instance : (inertMeasure p).IsHaarMeasure := by unfold inertMeasure; infer_instance

theorem inertMeasure_compactUnits : inertMeasure p (inertCompactUnits p) = 1 :=
  HaarTransport.measure_preimage _ _

theorem inert_measurePreserving :
    MeasurePreserving (QuotientLocalModels.inertEquiv p) (inertMeasure p) (InertLocalModel.measure p) :=
  HaarTransport.measurePreserving _ _

end Inert

/-- The maximal compact subgroup of the original quotient at three. -/
def ramifiedCompactUnits : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[3]) :=
  RamifiedLocalModel.compactUnits.comap QuotientLocalModels.ramifiedEquiv.toMonoidHom

theorem isCompact_ramifiedCompactUnits : IsCompact (ramifiedCompactUnits : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3])) :=
  QuotientLocalModels.ramifiedEquiv.toHomeomorph.isCompact_preimage.mpr
    CyclotomicRamifiedField.isCompact_compactUnits

theorem isOpen_ramifiedCompactUnits : IsOpen (ramifiedCompactUnits : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3])) :=
  CyclotomicRamifiedField.isOpen_compactUnits.preimage QuotientLocalModels.ramifiedEquiv.continuous

theorem ramified_compact_subgroup_le (L : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[3]))
    (hL : IsCompact (L : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3]))) : L ≤ ramifiedCompactUnits :=
  HaarTransport.compact_subgroup_le QuotientLocalModels.ramifiedEquiv _
    CyclotomicRamifiedField.compact_subgroup_le L hL

/-- Haar measure on the original quotient at three, with compact mass one. -/
def ramifiedMeasure : Measure (quotientFixedRing →ₐ[ℚ] ℚ_[3]) :=
  HaarTransport.measure QuotientLocalModels.ramifiedEquiv RamifiedLocalModel.compactNeighborhood

instance : ramifiedMeasure.IsHaarMeasure := by unfold ramifiedMeasure; infer_instance

theorem ramifiedMeasure_compactUnits : ramifiedMeasure ramifiedCompactUnits = 1 :=
  HaarTransport.measure_preimage _ _

theorem ramified_measurePreserving :
    MeasurePreserving QuotientLocalModels.ramifiedEquiv ramifiedMeasure RamifiedLocalModel.measure :=
  HaarTransport.measurePreserving _ _

end Cubic.ToricHeights.QuotientLocalHaar
