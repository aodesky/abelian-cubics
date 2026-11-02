import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Haar measure on the finite restricted product

Normalize Haar measure on the product of the specified compact open subgroups.
Finite-place stages are open subgroups with the topology inherited from the
restricted product. These constructions supply the measure used in the spatial
integrability argument; no integral factorization is part of their definition.
-/

noncomputable section

namespace Cubic.PoissonSummation.RestrictedProductHaar

open MeasureTheory TopologicalSpace Set Filter
open scoped RestrictedProduct

variable {ι : Type*} (R : ι → Type*) [∀ i, CommGroup (R i)]
  [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalGroup (R i)]
  (K : ∀ i, Subgroup (R i))

abbrev Points := Πʳ i, [R i, K i]

/-- The product of the local maximal compacts, in the actual restricted product. -/
def compactSubgroup : Subgroup (Points R K) where
  carrier := {x | ∀ i, x i ∈ K i}
  one_mem' := fun i => (K i).one_mem
  mul_mem' hx hy i := (K i).mul_mem (hx i) (hy i)
  inv_mem' hx i := (K i).inv_mem (hx i)

omit [∀ i, IsTopologicalGroup (R i)] in
theorem isOpen_compactSubgroup (hopen : ∀ i, IsOpen (K i : Set (R i))) :
    IsOpen (compactSubgroup R K : Set (Points R K)) :=
  RestrictedProduct.isOpen_forall_mem hopen

omit [∀ i, IsTopologicalGroup (R i)] in
theorem isCompact_compactSubgroup (hcompact : ∀ i, IsCompact (K i : Set (R i))) :
    IsCompact (compactSubgroup R K : Set (Points R K)) := by
  letI : ∀ i, CompactSpace (K i) := fun i => isCompact_iff_compactSpace.mp (hcompact i)
  have h := isCompact_range
    (RestrictedProduct.isEmbedding_structureMap (R := R) (A := fun i => (K i : Set (R i)))
      (𝓕 := cofinite)).continuous
  simpa only [RestrictedProduct.range_structureMap] using h

/-- The finite adelic normalization has mass one on the full compact subgroup. -/
def normalizationCompact (hopen : ∀ i, IsOpen (K i : Set (R i)))
    (hcompact : ∀ i, IsCompact (K i : Set (R i))) : PositiveCompacts (Points R K) where
  carrier := compactSubgroup R K
  isCompact' := isCompact_compactSubgroup R K hcompact
  interior_nonempty' := by
    rw [(isOpen_compactSubgroup R K hopen).interior_eq]
    exact ⟨1, (compactSubgroup R K).one_mem⟩

scoped instance : MeasurableSpace (Points R K) := borel (Points R K)
scoped instance : BorelSpace (Points R K) := ⟨rfl⟩

open scoped RestrictedProductHaar

variable [Fact (∀ i, IsOpen (K i : Set (R i)))]

def measure (hcompact : ∀ i, IsCompact (K i : Set (R i))) : Measure (Points R K) :=
  Measure.haarMeasure (normalizationCompact R K Fact.out hcompact)

instance (hcompact : ∀ i, IsCompact (K i : Set (R i))) :
    (measure R K hcompact).IsHaarMeasure := by unfold measure; infer_instance

theorem measure_compactSubgroup (hcompact : ∀ i, IsCompact (K i : Set (R i))) :
    measure R K hcompact (compactSubgroup R K) = 1 := Measure.haarMeasure_self

end Cubic.PoissonSummation.RestrictedProductHaar
