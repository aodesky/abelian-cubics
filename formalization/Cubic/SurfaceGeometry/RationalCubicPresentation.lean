import Cubic.SurfaceGeometry.RationalFormData
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section

namespace Cubic.SurfaceGeometry.RationalCubicPresentation

open MvPolynomial RationalFormData CubicData

private abbrev K := FractionRing Ambient
private def embed : Ambient →+* K := algebraMap Ambient K
private theorem embed_injective : Function.Injective embed := IsFractionRing.injective Ambient K
private theorem embed_C (q : ℚ) : embed (C q) = algebraMap ℚ K q :=
  (IsScalarTower.algebraMap_apply ℚ Ambient K q).symm

theorem forward_X (i : Fin 4) : normToOriginal (X i) = coordinateForms i := aeval_X _ _
theorem backward_X (i : Fin 4) : originalToNorm (X i) = inverseForms i := aeval_X _ _

theorem coordinateForms_homogeneous (i : Fin 4) : (coordinateForms i).IsHomogeneous 1 := by
  have h (j : Fin 4) := isHomogeneous_X ℚ j
  fin_cases i
  · exact h 0
  · exact ((h 0).sub ((h 1).C_mul (9/2))).add ((h 2).C_mul (27/2))
  · simpa only [map_ofNat] using
      (((h 3).C_mul 3).sub ((h 1).C_mul (3/2))).add ((h 2).C_mul (9/2))
  · simpa only [map_ofNat] using (h 0).sub ((h 1).C_mul 3)

theorem inverseForms_homogeneous (i : Fin 4) : (inverseForms i).IsHomogeneous 1 := by
  have h (j : Fin 4) := isHomogeneous_X ℚ j
  fin_cases i
  · exact h 0
  · exact ((h 0).sub (h 3)).C_mul (1/3)
  · simpa only [map_ofNat] using
      ((((h 1).C_mul 2).add (h 0)).sub ((h 3).C_mul 3)).C_mul (1/27)
  · simpa only [map_ofNat] using
      ((((h 2).C_mul 3).add (h 0)).sub (h 1)).C_mul (1/9)

theorem forward_homogeneous {p : Ambient} {n : ℕ} (hp : p.IsHomogeneous n) :
    (normToOriginal p).IsHomogeneous n := by
  simpa only [one_mul] using hp.aeval coordinateForms coordinateForms_homogeneous

theorem backward_homogeneous {p : Ambient} {n : ℕ} (hp : p.IsHomogeneous n) :
    (originalToNorm p).IsHomogeneous n := by
  simpa only [one_mul] using hp.aeval inverseForms inverseForms_homogeneous

theorem forward_equation : normToOriginal normEquation = 27 * rationalEquation := by
  simp only [normEquation,normCubic,map_sub,map_add,map_mul,map_pow,map_ofNat,forward_X]
  apply embed_injective
  simp only [coordinateForms,rationalEquation,F,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    map_add,map_sub,map_mul,map_pow,map_ofNat,MvPolynomial.algebraMap_eq,embed_C,map_div₀,map_one,Fin.reduceFinMk]
  ring

theorem backward_forward : originalToNorm.comp normToOriginal = AlgHom.id ℚ Ambient := by
  ext i : 1
  change originalToNorm (normToOriginal (X i)) = X i
  rw [forward_X]
  fin_cases i <;> simp only [coordinateForms,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    map_add,map_sub,map_mul,map_ofNat,backward_X]
  all_goals simp only [originalToNorm,aeval_C,inverseForms,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  all_goals apply embed_injective
  all_goals try simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,MvPolynomial.algebraMap_eq,embed_C,map_div₀,map_one,Fin.reduceFinMk]
  all_goals ring

theorem forward_backward : normToOriginal.comp originalToNorm = AlgHom.id ℚ Ambient := by
  ext i : 1
  change normToOriginal (originalToNorm (X i)) = X i
  rw [backward_X]
  fin_cases i <;> simp only [inverseForms,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    map_add,map_sub,map_mul,map_ofNat,forward_X]
  all_goals simp only [normToOriginal,aeval_C,coordinateForms,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  all_goals apply embed_injective
  all_goals try simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,MvPolynomial.algebraMap_eq,embed_C,map_div₀,map_one,Fin.reduceFinMk]
  all_goals ring

theorem backward_equation : originalToNorm rationalEquation = C (1 / 27) * normEquation := by
  have h := congrArg originalToNorm forward_equation
  have he := DFunLike.congr_fun backward_forward normEquation
  change originalToNorm (normToOriginal normEquation) = normEquation at he
  rw [he,map_mul,map_ofNat] at h
  apply embed_injective
  have h' := congrArg embed h
  simp only [map_mul,map_ofNat] at h'
  simp only [map_mul,embed_C,map_div₀,map_one,map_ofNat]
  linear_combination -(1 / 27 : K) * h'

def forward : NormCubicRing →ₐ[ℚ] RationalCubicRing :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℚ _).comp normToOriginal) (by
    change Ideal.span {normEquation} ≤ RingHom.ker _
    rw [Ideal.span_singleton_le_iff_mem]
    change Ideal.Quotient.mk _ (normToOriginal normEquation) = 0
    rw [forward_equation,map_mul]
    have hf : Ideal.Quotient.mk (Ideal.span {rationalEquation}) rationalEquation = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [hf,mul_zero])

def backward : RationalCubicRing →ₐ[ℚ] NormCubicRing :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℚ _).comp originalToNorm) (by
    change Ideal.span {rationalEquation} ≤ RingHom.ker _
    rw [Ideal.span_singleton_le_iff_mem]
    change Ideal.Quotient.mk _ (originalToNorm rationalEquation) = 0
    rw [backward_equation,map_mul]
    have hf : Ideal.Quotient.mk (Ideal.span {normEquation}) normEquation = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [hf,mul_zero])

def presentation : NormCubicRing ≃ₐ[ℚ] RationalCubicRing :=
  AlgEquiv.ofAlgHom forward backward
    (by
      apply Ideal.Quotient.algHom_ext
      apply AlgHom.ext
      intro p
      change Ideal.Quotient.mk _ (normToOriginal (originalToNorm p)) = Ideal.Quotient.mk _ p
      exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun forward_backward p))
    (by
      apply Ideal.Quotient.algHom_ext
      apply AlgHom.ext
      intro p
      change Ideal.Quotient.mk _ (originalToNorm (normToOriginal p)) = Ideal.Quotient.mk _ p
      exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun backward_forward p))

theorem presentation_mk (p : Ambient) :
    presentation (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (normToOriginal p) := rfl

end Cubic.SurfaceGeometry.RationalCubicPresentation
