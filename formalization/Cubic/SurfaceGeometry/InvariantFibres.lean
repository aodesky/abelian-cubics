import Cubic.SurfaceGeometry.FixedRingNormality
import Cubic.ToricHeights.C3Invariants
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section

namespace Cubic.SurfaceGeometry.InvariantFibres

theorem integral_invariants_flat :
    Module.Flat ℤ Cubic.ToricHeights.TernaryCyclicInvariants.invariants := by
  infer_instance

def fieldInvariants (k : Type*) [Field k] : Subalgebra k (MvPolynomial (Fin 3) k) :=
  AlgHom.equalizer (MvPolynomial.rename (finRotate 3)) (AlgHom.id k _)

/-- Normality holds in every characteristic and after arbitrary field extensions. -/
theorem field_invariants_normal (k : Type*) [Field k] :
    IsIntegrallyClosed (fieldInvariants k) := by
  unfold fieldInvariants
  exact FixedRingNormality.equalizer_normal _

end Cubic.SurfaceGeometry.InvariantFibres
