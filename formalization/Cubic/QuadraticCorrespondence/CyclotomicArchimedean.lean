import Cubic.QuadraticCorrespondence.QuotientLocalTopology
import Cubic.QuadraticCorrespondence.QuotientLocalCharacters
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The original quotient at the archimedean place

Identify the real cyclotomic tensor algebra with `ℂ`, fixing the
embedding by `ζ ↦ -1/2 + sqrt(3)/2 i`. The quotient's evaluation topology
then gives a topological group isomorphism to `ℂˣ`.
Complex conjugation is compared with the original Galois action on generators.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicArchimedean

open Polynomial CyclotomicLocalAlgebra CyclotomicField CyclotomicTorusGalois
open CyclotomicRestrictionScalars QuotientLocalCharacters
open scoped TensorProduct CyclotomicLocalAlgebra CyclotomicTensorTopology CyclotomicBaseChange
  RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

/-- The chosen complex place sends the distinguished cube root to the upper half-plane. -/
def zeta : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem zeta_relation : zeta ^ 2 + zeta + 1 = 0 := by
  apply Complex.ext <;> norm_num [zeta, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem zeta_im_ne_zero : zeta.im ≠ 0 := by
  dsimp [zeta]
  positivity

theorem conjugate_zeta : star zeta = -1 - zeta := by
  apply Complex.ext <;> norm_num [zeta]

/-- Evaluation of the real cyclotomic quotient in the chosen complex place. -/
def evaluation : Model ℝ →ₐ[ℝ] ℂ :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId ℝ ℂ) zeta
    (by simpa [cyclotomic_three] using zeta_relation)

@[simp]
theorem evaluation_root : evaluation (AdjoinRoot.root (cyclotomic 3 ℝ)) = zeta := by
  simp [evaluation]

theorem evaluation_surjective : Function.Surjective evaluation := by
  intro z
  let b : ℝ := z.im / zeta.im
  let a : ℝ := z.re - b * zeta.re
  refine ⟨algebraMap ℝ (Model ℝ) a +
    algebraMap ℝ (Model ℝ) b * AdjoinRoot.root (cyclotomic 3 ℝ), ?_⟩
  simp only [map_add, map_mul, AlgHom.commutes, evaluation_root]
  apply Complex.ext <;> simp [a, b, Complex.mul_re, Complex.mul_im, zeta_im_ne_zero]

/-- The real local cyclotomic algebra is `ℂ`, with its generator specified. -/
def quotientEquiv : Model ℝ ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofBijective evaluation ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_model, Complex.finrank_real_complex])
      (f := evaluation.toLinearMap)).mpr evaluation_surjective,
    evaluation_surjective⟩

@[simp]
theorem quotientEquiv_root : quotientEquiv (AdjoinRoot.root (cyclotomic 3 ℝ)) = zeta :=
  evaluation_root

private instance : IsModuleTopology ℝ ℂ :=
  IsModuleTopology.iso Complex.equivRealProdCLM.symm

def quotientContinuousEquiv : Model ℝ ≃A[ℝ] ℂ where
  __ := quotientEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap quotientEquiv.toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap quotientEquiv.symm.toLinearMap

/-- The complex place on the tensor algebra in the paper's order. -/
def place : E ⊗[ℚ] ℝ ≃ₐ[ℚ] ℂ :=
  (CyclotomicBaseChange.paperPresentation ℝ).trans (quotientEquiv.restrictScalars ℚ)

@[simp]
theorem place_zeta : place (CyclotomicField.zeta ⊗ₜ[ℚ] (1 : ℝ)) = zeta := by
  simp [place]

@[simp]
theorem place_scalar (a : ℝ) : place ((1 : E) ⊗ₜ[ℚ] a) = (a : ℂ) := by
  simp [place, CyclotomicBaseChange.paperPresentation,
    CyclotomicBaseChange.presentation]
  exact quotientEquiv.commutes a

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The same algebra map preserves the natural real module topology. -/
def placeContinuousEquiv : E ⊗[ℚ] ℝ ≃A[ℝ] ℂ :=
  (CyclotomicTensorTopology.commContinuousEquiv ℝ).trans
    ((CyclotomicBaseChange.presentationContinuousEquiv ℝ).trans quotientContinuousEquiv)

theorem placeContinuousEquiv_apply (x : E ⊗[ℚ] ℝ) : placeContinuousEquiv x = place x := rfl

theorem place_conjugation (x : E ⊗[ℚ] ℝ) :
    place (baseChangeConjugation ℝ x) = star (place x) := by
  apply map_baseChangeConjugation ℝ place.toAlgHom (Complex.conjAe.restrictScalars ℚ)
  · simpa using conjugate_zeta
  · intro a
    simp

/-- Original real quotient points with their evaluation topology are the complex unit group. -/
def pointEquiv : (quotientFixedRing →ₐ[ℚ] ℝ) ≃ₜ* ℂˣ :=
  (QuotientLocalTopology.quotientRestrictionScalarsContinuousMulEquiv ℝ).trans
    (Units.mapContinuousMulEquiv {
      __ := placeContinuousEquiv.toAlgEquiv.toMulEquiv
      __ := placeContinuousEquiv.toHomeomorph })

theorem pointEquiv_apply (P : quotientFixedRing →ₐ[ℚ] ℝ) :
    pointEquiv P = Units.map place.toMonoidHom (quotientRestrictionScalarsEquiv ℝ P) := rfl

theorem mapped_conjugate (u : (E ⊗[ℚ] ℝ)ˣ) :
    Units.map place.toMonoidHom (conjugateUnit ℝ u) =
      Units.map Complex.conjAe.toMonoidHom (Units.map place.toMonoidHom u) := by
  apply Units.ext
  exact place_conjugation u

end Cubic.QuadraticCorrespondence.CyclotomicArchimedean
