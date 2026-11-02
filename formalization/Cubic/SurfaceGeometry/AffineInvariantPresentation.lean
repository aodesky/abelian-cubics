import Cubic.SurfaceGeometry.AffineHomogeneousLift

noncomputable section

namespace Cubic.SurfaceGeometry.AffineInvariantPresentation

open MvPolynomial AffineModelData CubicPresentationData
open Cubic.ToricHeights

theorem kernel : RingHom.ker invariantEvaluation.toRingHom = Ideal.span {equation ℤ} := by
  apply le_antisymm
  · intro p hp
    obtain ⟨n,q,hq,hp'⟩ := AffineHomogeneousLift.exists_homogeneous_lift p
    have hq0 : cubicEvaluation q = 0 := by
      apply ChartDehomogenization.eq_zero_of_dehom_eq_zero
        (CubicGrading.evaluation_homogeneous hq)
      rw [AffineHomogeneousLift.invariant_evaluation, hp']
      exact hp
    have hm : q ∈ Ideal.span {cubic} := CubicPresentationElimination.kernel ▸ hq0
    obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hm
    apply Ideal.mem_span_singleton.mpr
    refine ⟨dehomogenize r, ?_⟩
    rw [← hp', hr, map_mul, AffineDehomogenization.equation_dehomogenize]
  · rw [Ideal.span_singleton_le_iff_mem]
    change invariantEvaluation (equation ℤ) = 0
    rw [← AffineDehomogenization.equation_dehomogenize,
      ← AffineHomogeneousLift.invariant_evaluation, CubicPresentationElimination.cubic_root,
      map_zero]

theorem evaluation_range : invariantEvaluation.range = AffineInvariantRing.invariants := by
  rw [invariantEvaluation, ← Algebra.adjoin_range_eq_range_aeval,
    AffineC3Invariants.«eqn:affineC3invariants»]
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  apply le_antisymm <;> apply Algebra.adjoin_le
  · intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · exact Algebra.subset_adjoin (by simp)
    · exact Subalgebra.neg_mem _ (Algebra.subset_adjoin (by simp))
    · exact Algebra.subset_adjoin (by simp)
  · intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · exact Algebra.subset_adjoin (by simp)
    · have hn : -AffineChartInvariants.e3 ∈
          Algebra.adjoin ℤ {AffineChartInvariants.e2, -AffineChartInvariants.e3,
            AffineChartInvariants.delta} := Algebra.subset_adjoin (by simp)
      simpa only [neg_neg] using Subalgebra.neg_mem _ hn
    · exact Algebra.subset_adjoin (by simp)

def evaluation : AffinePolynomial ℤ →ₐ[ℤ] AffineInvariantRing.invariants :=
  invariantEvaluation.codRestrict _ (fun p =>
    evaluation_range ▸ (show invariantEvaluation p ∈ invariantEvaluation.range from ⟨p,rfl⟩))

theorem evaluation_surjective : Function.Surjective evaluation := by
  intro f
  have hf : f.val ∈ invariantEvaluation.range := evaluation_range.symm ▸ f.property
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,Subtype.ext hp⟩

theorem evaluation_kernel : RingHom.ker evaluation.toRingHom = Ideal.span {equation ℤ} := by
  rw [← kernel]
  ext p
  rw [RingHom.mem_ker, RingHom.mem_ker, Subtype.ext_iff]
  rfl

def presentation : CoordinateRing ℤ ≃ₐ[ℤ] AffineInvariantRing.invariants :=
  (Ideal.quotientEquivAlgOfEq ℤ evaluation_kernel.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective evaluation_surjective)

theorem presentation_mk (p : AffinePolynomial ℤ) :
    (presentation (Ideal.Quotient.mk _ p)).val = invariantEvaluation p := by
  simp only [presentation, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  rfl

end Cubic.SurfaceGeometry.AffineInvariantPresentation
