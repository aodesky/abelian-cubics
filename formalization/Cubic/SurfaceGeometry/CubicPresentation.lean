import Cubic.SurfaceGeometry.CubicPresentationElimination
import Mathlib.RingTheory.Flat.TorsionFree

/-! The actual third Veronese of the original invariant ring is the displayed
cubic quotient. The map is induced by A=e₁³, B=e₁e₂, C=e₃ and D=δ. -/

noncomputable section

namespace Cubic.SurfaceGeometry.CubicPresentation

open MvPolynomial InvariantCubicData VeroneseData CubicPresentationData

theorem evaluation_range : cubicEvaluation.range = thirdVeronese := by
  rw [cubicEvaluation, ← Algebra.adjoin_range_eq_range_aeval]
  simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, cubicGenerators] using ThirdVeroneseGeneration.generated

def evaluation : CubicRing →ₐ[ℤ] thirdVeronese :=
  cubicEvaluation.codRestrict thirdVeronese (fun p =>
    evaluation_range ▸ (show cubicEvaluation p ∈ cubicEvaluation.range from ⟨p,rfl⟩))

theorem evaluation_surjective : Function.Surjective evaluation := by
  intro f
  have hf : f.val ∈ cubicEvaluation.range := evaluation_range.symm ▸ f.property
  obtain ⟨p,hp⟩ := hf
  exact ⟨p, Subtype.ext hp⟩

theorem evaluation_kernel : RingHom.ker evaluation.toRingHom = Ideal.span {cubic} := by
  rw [← CubicPresentationElimination.kernel]
  ext p
  rw [RingHom.mem_ker, RingHom.mem_ker, Subtype.ext_iff]
  rfl

def presentation : (CubicRing ⧸ Ideal.span {cubic}) ≃ₐ[ℤ] thirdVeronese :=
  (Ideal.quotientEquivAlgOfEq ℤ evaluation_kernel.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective evaluation_surjective)

theorem presentation_mk (p : CubicRing) :
    (presentation (Ideal.Quotient.mk _ p)).val = cubicEvaluation p := by
  simp only [presentation, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  rfl

theorem thirdVeronese_flat : Module.Flat ℤ thirdVeronese := by infer_instance

end Cubic.SurfaceGeometry.CubicPresentation
