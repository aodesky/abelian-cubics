import Cubic.QuadraticCorrespondence.CyclotomicInertField
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The inert local group and its normalized Haar measure

The multiplicative group comes from the quadratic extension; its topological
comparison with the global field's tensor algebra is proved in `CyclotomicInertField`.
Its maximal compact subgroup is given Haar mass one. `InertLocalValuation.lean`
and `InertLocalHeight.lean` construct the normalized valuation, height, character
and integral-locus descriptions used in the subsequent Fourier calculation.
-/

noncomputable section

namespace Cubic.ToricHeights.InertLocalModel

open MeasureTheory TopologicalSpace
open Cubic.QuadraticCorrespondence

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]

abbrev Points := CyclotomicInertField.Points p

abbrev compactUnits := CyclotomicInertField.compactUnits p

scoped instance : MeasurableSpace (Points p) := borel (Points p)

scoped instance : BorelSpace (Points p) := ⟨rfl⟩

def compactNeighborhood : PositiveCompacts (Points p) where
  carrier := compactUnits p
  isCompact' := CyclotomicInertField.isCompact_compactUnits p
  interior_nonempty' := by
    rw [(CyclotomicInertField.isOpen_compactUnits p).interior_eq]
    exact ⟨1, (compactUnits p).one_mem⟩

/-- Haar measure normalized on the maximal compact subgroup. -/
def measure : Measure (Points p) := Measure.haarMeasure (compactNeighborhood p)

instance : (measure p).IsHaarMeasure := by unfold measure; infer_instance

theorem measure_compactUnits : measure p (compactUnits p) = 1 := Measure.haarMeasure_self

end Cubic.ToricHeights.InertLocalModel
