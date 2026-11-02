import Cubic.OrbitParametrization.PadicMultiplicative
import Cubic.QuadraticCorrespondence.CocharacterIsomorphism
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The split p-adic coordinate model

The split cyclotomic local algebra has multiplicative group `ℚ_[p]ˣ × ℚ_[p]ˣ`.
We give it its topology, integral units, valuation in the paper's enlarged
cocharacter lattice, and normalized Haar measure. This is a concrete coordinate
model. `CyclotomicLocalTopology` proves the cyclotomic tensor splitting;
`QuotientLocalModels.splitEquiv` identifies the original local quotient with this
model, and `SplitQuotientLogarithm` compares the logarithms.
-/

noncomputable section

namespace Cubic.ToricHeights.SplitLocalModel

open MeasureTheory TopologicalSpace
open Cubic.OrbitParametrization
open Cubic.QuadraticCorrespondence.CocharacterIsomorphism

variable (p : ℕ) [Fact p.Prime]

abbrev Points := ℚ_[p]ˣ × ℚ_[p]ˣ

/-- The valuation in `(v₁, ω)` coordinates, induced from valuations in the
cyclotomic basis `(ω, γω)`. Thus it lands in the full enlarged lattice. -/
def valuation : Points p →* Multiplicative (ℤ × ℤ) where
  toFun x := Multiplicative.ofAdd (fromCyclotomic
    ((PadicMultiplicative.valuation p x.1).toAdd, (PadicMultiplicative.valuation p x.2).toAdd))
  map_one' := by simp [PadicMultiplicative.valuation]
  map_mul' x y := by
    change Multiplicative.ofAdd (fromCyclotomic
      (Padic.valuation (↑(x.1 * y.1) : ℚ_[p]), Padic.valuation (↑(x.2 * y.2) : ℚ_[p]))) = _
    simp only [Units.val_mul, Padic.valuation_mul x.1.ne_zero y.1.ne_zero,
      Padic.valuation_mul x.2.ne_zero y.2.ne_zero]
    exact congrArg Multiplicative.ofAdd (fromCyclotomic.map_add
      (Padic.valuation (x.1 : ℚ_[p]), Padic.valuation (x.2 : ℚ_[p]))
      (Padic.valuation (y.1 : ℚ_[p]), Padic.valuation (y.2 : ℚ_[p])))

theorem valuation_surjective : Function.Surjective (valuation p) := by
  intro n
  obtain ⟨x, hx⟩ := PadicMultiplicative.valuation_surjective p
    (Multiplicative.ofAdd (fromCyclotomic.symm n.toAdd).1)
  obtain ⟨y, hy⟩ := PadicMultiplicative.valuation_surjective p
    (Multiplicative.ofAdd (fromCyclotomic.symm n.toAdd).2)
  refine ⟨(x, y), ?_⟩
  simp [valuation, hx, hy]

def compactUnits : Subgroup (Points p) :=
  (PadicMultiplicative.compactUnits p).prod (PadicMultiplicative.compactUnits p)

theorem ker_valuation : (valuation p).ker = compactUnits p := by
  ext x
  change fromCyclotomic
    ((PadicMultiplicative.valuation p x.1).toAdd,
      (PadicMultiplicative.valuation p x.2).toAdd) = 0 ↔ _
  rw [map_eq_zero_iff fromCyclotomic fromCyclotomic.injective]
  rw [Prod.ext_iff]
  change ((PadicMultiplicative.valuation p x.1).toAdd = 0 ∧
    (PadicMultiplicative.valuation p x.2).toAdd = 0) ↔
      x.1 ∈ PadicMultiplicative.compactUnits p ∧ x.2 ∈ PadicMultiplicative.compactUnits p
  rw [← PadicMultiplicative.ker_valuation]
  rfl

theorem isCompact_compactUnits : IsCompact (compactUnits p : Set (Points p)) :=
  (PadicMultiplicative.isCompact_compactUnits p).prod
    (PadicMultiplicative.isCompact_compactUnits p)

theorem isOpen_compactUnits : IsOpen (compactUnits p : Set (Points p)) :=
  (PadicMultiplicative.isOpen_compactUnits p).prod
    (PadicMultiplicative.isOpen_compactUnits p)

/-- The product of the two integral-unit groups is the maximal compact subgroup. -/
theorem compact_subgroup_le (H : Subgroup (Points p)) (hH : IsCompact (H : Set (Points p))) :
    H ≤ compactUnits p := by
  have h1 := PadicMultiplicative.compact_subgroup_le p (H.map (MonoidHom.fst _ _))
    (hH.image continuous_fst)
  have h2 := PadicMultiplicative.compact_subgroup_le p (H.map (MonoidHom.snd _ _))
    (hH.image continuous_snd)
  intro x hx
  exact ⟨h1 ⟨x, hx, rfl⟩, h2 ⟨x, hx, rfl⟩⟩

theorem locallyConstant_valuation : IsLocallyConstant (valuation p) :=
  (((PadicMultiplicative.locallyConstant_valuation p).comp_continuous continuous_fst).prodMk
    ((PadicMultiplicative.locallyConstant_valuation p).comp_continuous continuous_snd)).comp
      (fun n => Multiplicative.ofAdd (fromCyclotomic (n.1.toAdd, n.2.toAdd)))

/-- The Borel sigma-algebra on the p-adic product group. -/
scoped instance : MeasurableSpace (Points p) := borel (Points p)

scoped instance : BorelSpace (Points p) := ⟨rfl⟩

def compactNeighborhood : PositiveCompacts (Points p) where
  carrier := compactUnits p
  isCompact' := isCompact_compactUnits p
  interior_nonempty' := by
    rw [(isOpen_compactUnits p).interior_eq]
    exact ⟨1, (compactUnits p).one_mem⟩

/-- Haar measure giving the product of integral units mass one. -/
def measure : Measure (Points p) := Measure.haarMeasure (compactNeighborhood p)

instance : (measure p).IsHaarMeasure := by unfold measure; infer_instance

theorem measure_compactUnits : measure p (compactUnits p) = 1 := Measure.haarMeasure_self

end Cubic.ToricHeights.SplitLocalModel
