import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Normalized Haar measure under a topological group isomorphism

Construct Haar measure on the source group itself, normalized on the preimage
of a compact neighborhood. Haar uniqueness proves that its pushforward is the
target's normalized Haar measure, with no additional scalar. This supplies
change of variables for local Fourier integrals and their integrability.
-/

noncomputable section

namespace Cubic.PoissonSummation.HaarTransport

open MeasureTheory TopologicalSpace

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]

/-- Pull back a compact neighborhood through a proved homeomorphism. -/
def compactNeighborhood (e : G ≃ₜ* H) (K : PositiveCompacts H) : PositiveCompacts G where
  carrier := e ⁻¹' (K : Set H)
  isCompact' := e.toHomeomorph.isCompact_preimage.mpr K.isCompact
  interior_nonempty' := by
    obtain ⟨y, hy⟩ := K.interior_nonempty
    refine ⟨e.symm y, ?_⟩
    apply mem_interior_iff_mem_nhds.mpr
    exact e.continuous.continuousAt.preimage_mem_nhds
      (by
        change (K : Set H) ∈ nhds (e (e.symm y))
        rw [e.apply_symm_apply]
        exact mem_interior_iff_mem_nhds.mp hy)

/-- The source Haar measure, defined by Haar's construction on its own topology. -/
def measure (e : G ≃ₜ* H) (K : PositiveCompacts H) : Measure G :=
  Measure.haarMeasure (compactNeighborhood e K)

instance (e : G ≃ₜ* H) (K : PositiveCompacts H) : (measure e K).IsHaarMeasure := by
  unfold measure
  infer_instance

omit [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] in
theorem measure_preimage (e : G ≃ₜ* H) (K : PositiveCompacts H) :
    measure e K (e ⁻¹' (K : Set H)) = 1 := Measure.haarMeasure_self

variable [T2Space H] [SecondCountableTopology H]

/-- Haar uniqueness fixes the normalization in the change of variables. -/
theorem map_measure (e : G ≃ₜ* H) (K : PositiveCompacts H) :
    (measure e K).map e = Measure.haarMeasure K := by
  letI : LocallyCompactSpace H := K.locallyCompactSpace_of_group
  symm
  apply (Measure.haarMeasure_eq_iff K _).mpr
  rw [Measure.map_apply (show Measurable (e : G → H) from e.continuous.measurable)
    K.isCompact.isClosed.measurableSet]
  exact measure_preimage e K

theorem measurePreserving (e : G ≃ₜ* H) (K : PositiveCompacts H) :
    MeasurePreserving e (measure e K) (Measure.haarMeasure K) :=
  ⟨e.continuous.measurable, map_measure e K⟩

theorem integrable_comp_iff (e : G ≃ₜ* H) (K : PositiveCompacts H)
    {V : Type*} [NormedAddCommGroup V] (f : H → V) :
    Integrable (f ∘ e) (measure e K) ↔ Integrable f (Measure.haarMeasure K) := by
  rw [← map_measure e K]
  exact e.toHomeomorph.measurableEmbedding.integrable_map_iff.symm

theorem integral_comp (e : G ≃ₜ* H) (K : PositiveCompacts H)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : H → V) :
    (∫ x, f (e x) ∂measure e K) = ∫ y, f y ∂Measure.haarMeasure K :=
  (measurePreserving e K).integral_comp e.toHomeomorph.measurableEmbedding f

omit [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
    [T2Space H] [SecondCountableTopology H] [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- A subgroup containing every compact subgroup has the same intrinsic
maximality property after a topological group isomorphism. -/
theorem compact_subgroup_le (e : G ≃ₜ* H) (K : Subgroup H)
    (hK : ∀ L : Subgroup H, IsCompact (L : Set H) → L ≤ K)
    (L : Subgroup G) (hL : IsCompact (L : Set G)) : L ≤ K.comap e.toMonoidHom := by
  intro x hx
  apply hK (L.map e.toMonoidHom) (hL.image e.continuous)
  exact ⟨x, hx, rfl⟩

end Cubic.PoissonSummation.HaarTransport
