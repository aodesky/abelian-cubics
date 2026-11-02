import Cubic.QuadraticCorrespondence.CyclotomicConjugation
import Cubic.QuadraticCorrespondence.SplitCoverGalois
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The cyclotomic Galois action on the cover and quotient rings

Instantiate the semilinear comparison with the field `E = ℚ(ζ₃)`.
The cover and quotient fixed rings are isomorphic as rational algebras.
For any commutative rational algebra `A`, conjugation on `E ⊗[ℚ] A` is
compatible with the original augmentation-one units and their Laurent
presentation. This constructs the concrete descent data. Their effectiveness
and natural base-change comparisons are proved in `CyclotomicTorusDescent`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicTorusGalois

open scoped TensorProduct
open CyclotomicField SplitLaurentInvariants SplitCoverFunctor
open Cubic.OrbitParametrization.CyclicGroupAlgebra

/-- The fixed Laurent algebra associated with the original split cover. -/
def coverFixedRing : Subalgebra ℚ (LaurentRing (K := E)) :=
  SplitLaurentGalois.fixedRing conjugation

/-- The cover's functions fixed by both its cyclic action and rational Galois action. -/
def quotientFixedRing : Subalgebra ℚ (LaurentRing (K := E)) :=
  SplitLaurentGalois.fixedInvariantRing conjugation (rootUnit zeta zeta_relation)

/-- The paper's quotient-character map identifies these fixed algebras. -/
def fixedRingEquiv : coverFixedRing ≃ₐ[ℚ] quotientFixedRing :=
  SplitLaurentGalois.fixedQuotientEquiv conjugation (rootUnit zeta zeta_relation)
    (rootUnit_primitive zeta zeta_relation)

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Extend the field conjugation to each scalar extension used in descent. -/
def baseChangeConjugation : (E ⊗[ℚ] A) ≃ₐ[ℚ] (E ⊗[ℚ] A) :=
  Algebra.TensorProduct.congr conjugation (AlgEquiv.refl : A ≃ₐ[ℚ] A)

theorem baseChangeConjugation_algebraMap (c : E) :
    baseChangeConjugation A (algebraMap E (E ⊗[ℚ] A) c) =
      algebraMap E (E ⊗[ℚ] A) (conjugation c) := by
  simp [baseChangeConjugation, Algebra.TensorProduct.algebraMap_apply]

theorem baseChangeConjugation_involutive : Function.Involutive (baseChangeConjugation A) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp only [baseChangeConjugation, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    change conjugation (conjugation e) ⊗ₜ[ℚ] a = e ⊗ₜ[ℚ] a
    rw [conjugation_involutive e]
  | add x y hx hy => simp [hx, hy]

/-- On every scalar extension the original cover induces exactly the
semilinear Laurent action used to define the fixed rings. -/
theorem coverPoint_baseChangeConjugation (g : traceOneUnits (E ⊗[ℚ] A))
    (f : LaurentRing (K := E)) :
    coverPointEquiv zeta zeta_relation
        (mapUnits (baseChangeConjugation A).toRingHom g)
        (SplitLaurentGalois.conjugate conjugation f) =
      baseChangeConjugation A (coverPointEquiv zeta zeta_relation g f) :=
  SplitCoverGalois.coverPointEquiv_conjugate zeta zeta_relation conjugation
    conjugation_zeta_sq (baseChangeConjugation A) (baseChangeConjugation_algebraMap A) g f

end Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
