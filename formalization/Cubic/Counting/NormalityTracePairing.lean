import Cubic.OrbitParametrization.NormalUnit
import Cubic.Counting.NormalityDeterminant
import Mathlib.RingTheory.Discriminant

/-!
# The trace Gram matrix of the conjugates

Supporting steps for `lemma:normalityCriterion`. The trace is the actual trace
of multiplication on the rational algebra. Its nondegeneracy makes normality
equivalent to nonsingularity of the rational Gram matrix. After mapping its
entries into `K`, this matrix is `Aᵀ A`, where `A` represents multiplication
by the conjugate-coefficient element of `K[C₃]`.
-/

noncomputable section

namespace Cubic.Counting.NormalityTracePairing

open Cubic.OrbitParametrization Cubic.OrbitParametrization.C3Algebra

variable (K : C3Alg)

/-- For both the field and split models, the algebra trace is the conjugate sum. -/
theorem algebraMap_trace (x : K.carrier) :
    algebraMap ℚ K.carrier (Algebra.trace ℚ K.carrier x) = traceSum K x := by
  classical
  rcases K.model with ⟨hK, hdim, hinj⟩ | ⟨e, he⟩
  · letI : Field K.carrier := hK.toField
    haveI : IsGalois ℚ K.carrier := IsGalois.of_fixedField_eq_bot ℚ K.carrier (by
      apply le_antisymm ?_ bot_le
      intro y hy
      rw [IntermediateField.mem_bot]
      apply fixed_rational K y
      intro g
      rw [IntermediateField.mem_fixedField_iff] at hy
      exact hy (K.act g) (Subgroup.mem_top _))
    have hbij : Function.Bijective K.act :=
      (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, by
        rw [IsGalois.card_aut_eq_finrank, hdim]
        rw [Nat.card_eq_fintype_card]
        rfl⟩
    rw [trace_eq_sum_automorphisms, traceSum, hbij.sum_comp (fun τ => τ x)]
  · have htr : Algebra.trace ℚ (ZMod 3 → ℚ) (e x) = ∑ i, e x i := by
      rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℚ (ZMod 3))]
      simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_apply]
    apply e.injective
    ext h
    rw [AlgEquiv.commutes]
    change Algebra.trace ℚ K.carrier x = e (traceSum K x) h
    rw [← Algebra.trace_eq_of_algEquiv e x, htr]
    simp only [traceSum, map_sum, Finset.sum_apply, he]
    rw [← Equiv.sum_comp Multiplicative.ofAdd]
    simp only [toAdd_ofAdd]
    exact (Equiv.sum_comp (Equiv.addLeft h) (e x)).symm

/-- Nondegeneracy is proved in the existing field and split models. -/
theorem traceForm_nondegenerate : (Algebra.traceForm ℚ K.carrier).Nondegenerate := by
  have hleft : (Algebra.traceForm ℚ K.carrier).SeparatingLeft := by
    intro x hx
    by_contra hne
    obtain ⟨y, hy⟩ := pairing_nondegenerate K x hne
    apply hy
    rw [← algebraMap_trace]
    simpa only [Algebra.traceForm_apply, map_zero] using
      congrArg (algebraMap ℚ K.carrier) (hx y)
  exact ⟨hleft, fun y hy => hleft y (fun x => by
    simpa only [Algebra.traceForm_apply, mul_comm] using hy x)⟩

/-- The three conjugates, indexed in the order used in the paper. -/
def conjugateFamily (x : K.carrier) (i : Fin 3) : K.carrier :=
  K.act (Multiplicative.ofAdd (i : ZMod 3)) x

/-- The rational trace Gram matrix `B`. -/
def gram (x : K.carrier) : Matrix (Fin 3) (Fin 3) ℚ :=
  Algebra.traceMatrix ℚ (conjugateFamily K x)

/-- The orbit is a rational basis exactly when its trace Gram matrix is nonsingular. -/
theorem normal_iff_gram_det_ne_zero (x : K.carrier) :
    C3Algebra.IsNormal K x ↔ (gram K x).det ≠ 0 := by
  rw [C3Algebra.IsNormal, ← linearIndependent_equiv (Multiplicative.ofAdd : Fin 3 ≃ C3)]
  change LinearIndependent ℚ (conjugateFamily K x) ↔ (gram K x).det ≠ 0
  constructor
  · intro hx
    let b := basisOfLinearIndependentOfCardEqFinrank hx
      (by rw [finrank_eq_three]; rfl)
    have hb : ⇑b = conjugateFamily K x := by
      exact coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
      (traceForm_nondegenerate K)
    rw [← Algebra.traceMatrix_of_basis, hb] at h
    exact h
  · intro hx
    by_contra h
    exact hx (Algebra.discr_zero_of_not_linearIndependent ℚ h)

/-- Entrywise trace computation: `B = Aᵀ A` in `K`. -/
theorem gram_map (x : K.carrier) :
    (gram K x).map (algebraMap ℚ K.carrier) =
      (groupAlgebraMulMatrix x (K.act σ x) (K.act (σ ^ 2) x)).transpose *
        groupAlgebraMulMatrix x (K.act σ x) (K.act (σ ^ 2) x) := by
  ext i j
  simp only [gram, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, algebraMap_trace, traceSum_eq, map_mul]
  fin_cases i <;> fin_cases j <;>
    simp [conjugateFamily, groupAlgebraMulMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      show Multiplicative.ofAdd (0 : ZMod 3) = (1 : C3) by decide,
      show Multiplicative.ofAdd (1 : ZMod 3) = σ by rfl,
      show Multiplicative.ofAdd (2 : ZMod 3) = σ ^ 2 by decide,
      act_σ_σ, act_σ_σ2, act_σ2_σ, act_σ2_σ2, -map_pow] <;> ring

/-- Taking determinants in `B = Aᵀ A` gives the square of the group determinant. -/
theorem gram_det (x : K.carrier) :
    algebraMap ℚ K.carrier (gram K x).det =
      (groupAlgebraMulMatrix x (K.act σ x) (K.act (σ ^ 2) x)).det ^ 2 := by
  rw [(algebraMap ℚ K.carrier).map_det, RingHom.mapMatrix_apply, gram_map,
    Matrix.det_mul, Matrix.det_transpose]
  ring

end Cubic.Counting.NormalityTracePairing
