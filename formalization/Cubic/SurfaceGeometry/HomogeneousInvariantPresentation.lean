import Cubic.SurfaceGeometry.IntegralInvariantPresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

namespace Cubic.SurfaceGeometry.HomogeneousInvariantPresentation

open InvariantCubicData Cubic.ToricHeights.TernaryCyclicInvariants

theorem evaluation_mem (p : Polynomial SymmetricCoefficients) :
    p.eval₂ symmetricEval.toRingHom delta ∈ invariants := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add]
    exact invariants.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    apply invariants.mul_mem
    · exact IntegralInvariantNormalForm.symmetricEval_symmetric a (finRotate 3)
    · exact invariants.pow_mem Cubic.ToricHeights.CyclicSymmetricDecomposition.rename_cycle_delta n

def evaluation : Polynomial SymmetricCoefficients →ₐ[ℤ] invariants :=
  (Polynomial.eval₂AlgHom' symmetricEval delta (fun _ => Commute.all _ _)).codRestrict
    invariants evaluation_mem

theorem evaluation_surjective : Function.Surjective evaluation := by
  intro f
  obtain ⟨⟨a,b⟩,hab,_⟩ := IntegralInvariantNormalForm.exists_unique_normalForm f.val f.property
  refine ⟨Polynomial.C a + Polynomial.C b * Polynomial.X, Subtype.ext ?_⟩
  change (Polynomial.C a + Polynomial.C b * Polynomial.X).eval₂
    symmetricEval.toRingHom delta = f.val
  simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X] using hab

theorem evaluation_kernel : RingHom.ker evaluation.toRingHom =
    Ideal.span {relationPolynomial} := by
  ext p
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change (⟨p.eval₂ symmetricEval.toRingHom delta, evaluation_mem p⟩ : invariants) = 0 ↔ _
  rw [Subtype.ext_iff]
  exact IntegralInvariantPresentation.relations_iff p

/-- The complete invariant ring has the single monic quadratic presentation. -/
def presentation :
    (Polynomial SymmetricCoefficients ⧸ Ideal.span {relationPolynomial}) ≃ₐ[ℤ] invariants :=
  (Ideal.quotientEquivAlgOfEq ℤ evaluation_kernel.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective evaluation_surjective)

end Cubic.SurfaceGeometry.HomogeneousInvariantPresentation
