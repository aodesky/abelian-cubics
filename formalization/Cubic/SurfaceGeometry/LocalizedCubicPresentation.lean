import Cubic.SurfaceGeometry.LocalizedCubicData
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

noncomputable section

namespace Cubic.SurfaceGeometry.LocalizedCubicPresentation

open MvPolynomial LocalizedCubicData CubicData

/-- The canonical inclusion of ℤ[1/6] in ℚ, used only to check polynomial identities. -/
def toRat : Base →+* ℚ :=
  IsLocalization.Away.lift (6 : ℤ) (g := Int.castRingHom ℚ) (by norm_num)

theorem toRat_injective : Function.Injective toRat := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (6 : ℤ)) Base toRat
  intro x hx
  have h : (x : ℚ) = 0 := by simpa [toRat] using hx
  have hx0 : x = 0 := by exact_mod_cast h
  simp [hx0]

@[simp] theorem toRat_invSix : toRat invSix = (1 / 6 : ℚ) := by
  have h := congrArg toRat (IsLocalization.Away.mul_invSelf (6 : ℤ) (S := Base))
  have h' : (6 : ℚ) * toRat invSix = 1 := by
    simpa only [map_mul, map_one, map_ofNat, Int.cast_ofNat, invSix,
      show algebraMap ℤ Base (6 : ℤ) = (6 : Base) by norm_num] using h
  apply (eq_div_iff (by norm_num : (6 : ℚ) ≠ 0)).2
  simpa [mul_comm] using h'

private abbrev RationalAmbient := MvPolynomial (Fin 4) ℚ
private abbrev K := FractionRing RationalAmbient
private def embed : Ambient →+* K :=
  (algebraMap RationalAmbient K).comp (MvPolynomial.map toRat)
private theorem embed_injective : Function.Injective embed :=
  (IsFractionRing.injective RationalAmbient K).comp (MvPolynomial.map_injective _ toRat_injective)
private theorem embed_C (q : Base) : embed (C q) = algebraMap ℚ K (toRat q) := by
  simp only [embed, RingHom.comp_apply, MvPolynomial.map_C]
  exact (IsScalarTower.algebraMap_apply ℚ RationalAmbient K (toRat q)).symm

theorem forward_X (i : Fin 4) : normToOriginal (X i) = coordinateForms i := aeval_X _ _
theorem backward_X (i : Fin 4) : originalToNorm (X i) = inverseForms i := aeval_X _ _

theorem coordinateForms_homogeneous (i : Fin 4) : (coordinateForms i).IsHomogeneous 1 := by
  have h (j : Fin 4) := isHomogeneous_X Base j
  fin_cases i
  · exact h 0
  · exact ((h 0).sub ((h 1).C_mul (27 * invSix))).add ((h 2).C_mul (81 * invSix))
  · simpa only [map_ofNat] using
      (((h 3).C_mul 3).sub ((h 1).C_mul (9 * invSix))).add ((h 2).C_mul (27 * invSix))
  · simpa only [map_ofNat] using (h 0).sub ((h 1).C_mul 3)

theorem inverseForms_homogeneous (i : Fin 4) : (inverseForms i).IsHomogeneous 1 := by
  have h (j : Fin 4) := isHomogeneous_X Base j
  fin_cases i
  · exact h 0
  · exact ((h 0).sub (h 3)).C_mul (2 * invSix)
  · simpa only [map_ofNat] using
      ((((h 1).C_mul 2).add (h 0)).sub ((h 3).C_mul 3)).C_mul (8 * invSix ^ 3)
  · simpa only [map_ofNat] using
      ((((h 2).C_mul 3).add (h 0)).sub (h 1)).C_mul (4 * invSix ^ 2)

theorem forward_homogeneous {p : Ambient} {n : ℕ} (hp : p.IsHomogeneous n) :
    (normToOriginal p).IsHomogeneous n := by
  simpa only [one_mul] using hp.aeval coordinateForms coordinateForms_homogeneous

theorem backward_homogeneous {p : Ambient} {n : ℕ} (hp : p.IsHomogeneous n) :
    (originalToNorm p).IsHomogeneous n := by
  simpa only [one_mul] using hp.aeval inverseForms inverseForms_homogeneous

theorem forward_equation : normToOriginal normEquation = 27 * originalEquation := by
  simp only [normEquation,normCubic,map_sub,map_add,map_mul,map_pow,map_ofNat,forward_X]
  apply embed_injective
  simp only [coordinateForms,originalEquation,F,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    map_add,map_sub,map_mul,map_pow,map_ofNat,embed_C,toRat_invSix,map_div₀,map_one]
  ring

theorem backward_forward : originalToNorm.comp normToOriginal = AlgHom.id Base Ambient := by
  ext i : 1
  change originalToNorm (normToOriginal (X i)) = X i
  rw [forward_X]
  fin_cases i <;> simp only [coordinateForms,Matrix.cons_val_zero',Matrix.cons_val_succ',
    map_add,map_sub,map_mul,map_ofNat,backward_X]
  all_goals simp only [originalToNorm,aeval_C,inverseForms,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  all_goals apply embed_injective
  all_goals try simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,
    MvPolynomial.algebraMap_eq,embed_C,toRat_invSix,map_div₀,map_one,Fin.reduceFinMk]
  all_goals ring

theorem forward_backward : normToOriginal.comp originalToNorm = AlgHom.id Base Ambient := by
  ext i : 1
  change normToOriginal (originalToNorm (X i)) = X i
  rw [backward_X]
  fin_cases i <;> simp only [inverseForms,Matrix.cons_val_zero',Matrix.cons_val_succ',
    map_add,map_sub,map_mul,map_ofNat,forward_X]
  all_goals simp only [normToOriginal,aeval_C,coordinateForms,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  all_goals apply embed_injective
  all_goals try simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,
    MvPolynomial.algebraMap_eq,embed_C,toRat_invSix,map_div₀,map_one,Fin.reduceFinMk]
  all_goals ring

theorem backward_equation : originalToNorm originalEquation = C (8 * invSix ^ 3) * normEquation := by
  have h := congrArg originalToNorm forward_equation
  have he := DFunLike.congr_fun backward_forward normEquation
  change originalToNorm (normToOriginal normEquation) = normEquation at he
  rw [he,map_mul,map_ofNat] at h
  apply embed_injective
  have h' := congrArg embed h
  simp only [map_mul,map_ofNat] at h'
  simp only [map_mul,map_pow,embed_C,toRat_invSix,map_div₀,map_one,map_ofNat]
  linear_combination -(1 / 27 : K) * h'

def forward : NormCubicRing →ₐ[Base] OriginalCubicRing :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ Base _).comp normToOriginal) (by
    change Ideal.span {normEquation} ≤ RingHom.ker _
    rw [Ideal.span_singleton_le_iff_mem]
    change Ideal.Quotient.mk _ (normToOriginal normEquation) = 0
    rw [forward_equation,map_mul]
    have hf : Ideal.Quotient.mk (Ideal.span {originalEquation}) originalEquation = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [hf,mul_zero])

def backward : OriginalCubicRing →ₐ[Base] NormCubicRing :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ Base _).comp originalToNorm) (by
    change Ideal.span {originalEquation} ≤ RingHom.ker _
    rw [Ideal.span_singleton_le_iff_mem]
    change Ideal.Quotient.mk _ (originalToNorm originalEquation) = 0
    rw [backward_equation,map_mul]
    have hf : Ideal.Quotient.mk (Ideal.span {normEquation}) normEquation = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [hf,mul_zero])

def presentation : NormCubicRing ≃ₐ[Base] OriginalCubicRing :=
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

end Cubic.SurfaceGeometry.LocalizedCubicPresentation
