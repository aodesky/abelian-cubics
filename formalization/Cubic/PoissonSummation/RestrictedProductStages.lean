import Cubic.PoissonSummation.RestrictedProductHaar

/-!
# Finite-place stages of the restricted product

Outside a finite set the coordinates remain in the specified compact open
subgroups. The stage carries the actual subspace topology and the restriction
of the normalized restricted-product Haar measure.
-/

noncomputable section

namespace Cubic.PoissonSummation.RestrictedProductHaar

open MeasureTheory TopologicalSpace Set Filter
open scoped RestrictedProduct RestrictedProductHaar

variable {ι : Type*} (R : ι → Type*) [∀ i, CommGroup (R i)]
  [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalGroup (R i)]
  (K : ∀ i, Subgroup (R i))
  [Fact (∀ i, IsOpen (K i : Set (R i)))]

abbrev Stage (S : Finset ι) := Πʳ i, [R i, K i]_[𝓟 (S : Set ι)ᶜ]

theorem stage_filter (S : Finset ι) : cofinite ≤ 𝓟 (S : Set ι)ᶜ := by
  rw [le_principal_iff, mem_cofinite]
  simp

def inclusion (S : Finset ι) : Stage R K S →* Points R K where
  toFun := RestrictedProduct.inclusion R (fun i => (K i : Set (R i))) (stage_filter S)
  map_one' := rfl
  map_mul' _ _ := rfl

omit [∀ i, IsTopologicalGroup (R i)] in
theorem isOpenEmbedding_inclusion (S : Finset ι) :
    Topology.IsOpenEmbedding (inclusion R K S) :=
  RestrictedProduct.isOpenEmbedding_inclusion_principal Fact.out (stage_filter S)

scoped instance (S : Finset ι) : MeasurableSpace (Stage R K S) := borel (Stage R K S)
scoped instance (S : Finset ι) : BorelSpace (Stage R K S) := ⟨rfl⟩

def stageMeasure (hcompact : ∀ i, IsCompact (K i : Set (R i))) (S : Finset ι) :
    Measure (Stage R K S) := (measure R K hcompact).comap (inclusion R K S)

instance (hcompact : ∀ i, IsCompact (K i : Set (R i))) (S : Finset ι) :
    (stageMeasure R K hcompact S).IsHaarMeasure :=
  Measure.IsHaarMeasure.comap (mH := inferInstance) _ (isOpenEmbedding_inclusion R K S)

def projection (S : Finset ι) : Stage R K S →* (∀ i : S, R i) where
  toFun x i := x i
  map_one' := rfl
  map_mul' _ _ := rfl

omit [∀ i, IsTopologicalGroup (R i)] [Fact (∀ i, IsOpen (K i : Set (R i)))] in
theorem continuous_projection (S : Finset ι) : Continuous (projection R K S) :=
  continuous_pi fun i => RestrictedProduct.continuous_eval i.val

omit [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalGroup (R i)]
  [Fact (∀ i, IsOpen (K i : Set (R i)))] in
theorem projection_surjective (S : Finset ι) : Function.Surjective (projection R K S) := by
  classical
  intro x
  refine ⟨⟨fun i => if hi : i ∈ S then x ⟨i, hi⟩ else 1, ?_⟩, ?_⟩
  · intro i hi
    change i ∉ S at hi
    change (if hi : i ∈ S then x ⟨i, hi⟩ else 1) ∈ K i
    simpa only [dif_neg hi] using (K i).one_mem
  · funext i
    exact dif_pos i.property

variable [∀ i, T2Space (R i)]

omit [∀ i, IsTopologicalGroup (R i)] [Fact (∀ i, IsOpen (K i : Set (R i)))] in
/-- The omitted coordinates form a compact product, so finite projection is proper. -/
theorem isCompact_projection_preimage
    (hcompact : ∀ i, IsCompact (K i : Set (R i))) (S : Finset ι)
    {C : Set (∀ i : S, R i)} (hC : IsCompact C) :
    IsCompact (projection R K S ⁻¹' C) := by
  classical
  let boxes : ∀ i, Set (R i) := fun i =>
    if hi : i ∈ S then (fun x : ∀ j : S, R j => x ⟨i, hi⟩) '' C else K i
  have hboxes : ∀ i, IsCompact (boxes i) := by
    intro i
    dsimp only [boxes]
    split_ifs with hi
    · exact hC.image (show Continuous (fun x : ∀ j : S, R j => x ⟨i, hi⟩) from
        continuous_apply _)
    · exact hcompact i
  have hrange : univ.pi boxes ⊆
      range ((⇑) : Stage R K S → ∀ i, R i) := by
    rw [RestrictedProduct.range_coe_principal]
    intro x hx i hi
    have hi' : i ∉ S := hi
    simpa only [boxes, dif_neg hi'] using hx i (mem_univ i)
  have hboxcompact := RestrictedProduct.isEmbedding_coe_of_principal.isInducing
    |>.isCompact_preimage' (isCompact_univ_pi hboxes) hrange
  apply hboxcompact.of_isClosed_subset
    (hC.isClosed.preimage (continuous_projection R K S))
  intro x hx i _
  dsimp only [boxes]
  split_ifs with hi
  · exact ⟨projection R K S x, hx, rfl⟩
  · exact x.property hi

omit [∀ i, IsTopologicalGroup (R i)] [Fact (∀ i, IsOpen (K i : Set (R i)))] in
theorem projection_tendsto_cocompact
    (hcompact : ∀ i, IsCompact (K i : Set (R i))) (S : Finset ι) :
    Tendsto (projection R K S) (cocompact (Stage R K S)) (cocompact (∀ i : S, R i)) := by
  apply Filter.hasBasis_cocompact.tendsto_right_iff.mpr
  intro C hC
  exact (isCompact_projection_preimage R K hcompact S hC).compl_mem_cocompact

/-- The compact normalizing set in the finite product of unrestricted coordinates. -/
def finiteNormalizationCompact (hcompact : ∀ i, IsCompact (K i : Set (R i)))
    (S : Finset ι) : PositiveCompacts (∀ i : S, R i) where
  carrier := univ.pi (fun i : S => (K i : Set (R i)))
  isCompact' := isCompact_univ_pi fun i => hcompact i
  interior_nonempty' := by
    have ho : IsOpen (univ.pi (fun i : S => (K i : Set (R i)))) :=
      isOpen_set_pi finite_univ (fun i _ => (Fact.out : ∀ i, IsOpen (K i : Set (R i))) i)
    rw [ho.interior_eq]
    exact ⟨1, fun i _ => (K i).one_mem⟩

omit [∀ i, T2Space (R i)] in
theorem stageMeasure_projection_compact
    (hcompact : ∀ i, IsCompact (K i : Set (R i))) (S : Finset ι) :
    stageMeasure R K hcompact S
      (projection R K S ⁻¹' (finiteNormalizationCompact R K hcompact S : Set (∀ i : S, R i))) = 1 := by
  classical
  rw [stageMeasure, (isOpenEmbedding_inclusion R K S).measurableEmbedding.comap_apply]
  have heq : inclusion R K S ''
      (projection R K S ⁻¹' (finiteNormalizationCompact R K hcompact S : Set (∀ i : S, R i))) =
      (compactSubgroup R K : Set (Points R K)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      by_cases hi : i ∈ S
      · exact hx ⟨i, hi⟩ (mem_univ _)
      · exact x.property hi
    · intro hy
      refine ⟨⟨y, fun i _ => hy i⟩, ?_, rfl⟩
      exact fun i _ => hy i
  rw [heq, measure_compactSubgroup]

variable [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
  [∀ i, SecondCountableTopology (R i)] [∀ i, LocallyCompactSpace (R i)]

/-- Finite-stage projection has exactly the product of the normalized local measures. -/
theorem map_stageMeasure_projection
    (hcompact : ∀ i, IsCompact (K i : Set (R i)))
    (μ : ∀ i, Measure (R i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ i, μ i (K i) = 1) (S : Finset ι) :
    (stageMeasure R K hcompact S).map (projection R K S) =
      Measure.pi (fun i : S => μ i) := by
  letI : ∀ i, SigmaCompactSpace (R i) := fun i =>
    sigmaCompactSpace_of_locallyCompact_secondCountable
  letI : ∀ i, SigmaFinite (μ i) := fun i => Measure.IsHaarMeasure.sigmaFinite (μ i)
  letI : SigmaCompactSpace (∀ i : S, R i) := sigmaCompactSpace_of_locallyCompact_secondCountable
  let ν := (stageMeasure R K hcompact S).map (projection R K S)
  letI : ν.IsHaarMeasure := Measure.isHaarMeasure_map _ (projection R K S)
    (continuous_projection R K S) (projection_surjective R K S)
    (projection_tendsto_cocompact R K hcompact S)
  have hν : ν (finiteNormalizationCompact R K hcompact S) = 1 := by
    rw [Measure.map_apply (continuous_projection R K S).measurable
      (finiteNormalizationCompact R K hcompact S).isCompact.measurableSet]
    exact stageMeasure_projection_compact R K hcompact S
  have hprod : Measure.pi (fun i : S => μ i) (finiteNormalizationCompact R K hcompact S) = 1 := by
    change Measure.pi (fun i : S => μ i) (univ.pi fun i : S => (K i : Set (R i))) = 1
    rw [Measure.pi_pi]
    simp only [hμ, Finset.prod_const_one]
  exact ((Measure.haarMeasure_eq_iff _ ν).mpr hν).symm.trans
    ((Measure.haarMeasure_eq_iff _ _).mpr hprod)

omit [∀ i, IsTopologicalGroup (R i)] [∀ i, T2Space (R i)]
  [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
  [∀ i, LocallyCompactSpace (R i)] in
/-- Countably many finite-place stages give a second-countable restricted product. -/
theorem secondCountableTopology [Countable ι] : SecondCountableTopology (Points R K) := by
  classical
  letI (S : Finset ι) : SecondCountableTopology (Stage R K S) :=
    RestrictedProduct.isEmbedding_coe_of_principal.isInducing.secondCountableTopology
  letI (S : Finset ι) : SecondCountableTopology (range (inclusion R K S)) :=
    (isOpenEmbedding_inclusion R K S).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply secondCountableTopology_of_countable_cover
    (fun S => (isOpenEmbedding_inclusion R K S).isOpen_range)
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  have hfin : {i | x i ∉ K i}.Finite := x.property
  refine ⟨hfin.toFinset, ⟨⟨x, ?_⟩, rfl⟩⟩
  intro i hi
  by_contra hn
  exact hi (hfin.mem_toFinset.mpr hn)

end Cubic.PoissonSummation.RestrictedProductHaar
