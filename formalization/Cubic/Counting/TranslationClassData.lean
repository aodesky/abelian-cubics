import Cubic.Counting.GeneralHeightReduction
import Mathlib.Algebra.CubicDiscriminant

/-!
# Translation classes of monic abelian cubics

Objects for `rem:translationClasses` and the Bhargava–Shankar-height count of the
introduction. Two polynomials of `F_mon` are equivalent when `g(t) = f(t + k)` for some
`k ∈ ℤ`, that is, when the roots of `g` are those of `f` translated by the integer `-k`.
A translation class is an equivalence class of this relation.

For `f(t) = t³ + a₁t² + a₂t + a₃` (Lean coefficients `a₁ = f.coeff 2`, `a₂ = f.coeff 1`,
`a₃ = f.coeff 0`) the paper puts `I = a₁² - 3a₂`, `J = -2a₁³ + 9a₁a₂ - 27a₃` and
`H_BS(f) = max(|I|³, J²/4)`. Both `I` and `J` are invariant under integral translation, so
they and `H_BS` are defined on translation classes.
-/

noncomputable section

namespace Cubic.Counting.TranslationClassData

open Polynomial Cubic.Counting.GeneralMonicData Cubic.Counting.GeneralHeightReduction

/-- Integral translation `f(t) ↦ f(t + k)`. -/
def translate (k : ℤ) (f : ℤ[X]) : ℤ[X] := f.comp (X + C k)

theorem translate_zero (f : ℤ[X]) : translate 0 f = f := by
  simp [translate]

theorem translate_translate (k l : ℤ) (f : ℤ[X]) :
    translate l (translate k f) = translate (k + l) f := by
  simp only [translate, comp_assoc, add_comp, X_comp, C_comp]
  congr 1
  rw [map_add]; ring

/-- Translation on coefficients. -/
theorem translate_monicCubic (k a₂ a₁ a₀ : ℤ) :
    translate k (monicCubic a₂ a₁ a₀) =
      monicCubic (3 * k + a₂) (3 * k ^ 2 + 2 * a₂ * k + a₁) (k ^ 3 + a₂ * k ^ 2 + a₁ * k + a₀) := by
  simp only [translate, monicCubic, add_comp, mul_comp, C_comp, X_comp, X_pow_comp,
    map_add, map_mul, map_pow, map_ofNat]
  ring

/-- Equivalence of polynomials of `F_mon` under integral translation. -/
def translationSetoid : Setoid monicCyclic where
  r f g := ∃ k : ℤ, (g : ℤ[X]) = translate k f
  iseqv := by
    refine ⟨fun f => ⟨0, (translate_zero _).symm⟩, ?_, ?_⟩
    · rintro f g ⟨k, h⟩
      exact ⟨-k, by rw [h, translate_translate, add_neg_cancel, translate_zero]⟩
    · rintro f g h ⟨k, hk⟩ ⟨l, hl⟩
      exact ⟨k + l, by rw [hl, hk, translate_translate]⟩

/-- Translation classes of monic integral cubics with Galois group `C₃`. -/
def TranslationClass : Type := Quotient translationSetoid

/-- The class of `f`. -/
def TranslationClass.mk (f : monicCyclic) : TranslationClass := Quotient.mk translationSetoid f

/-- `I = a₁² - 3a₂`. -/
def bsI (f : ℤ[X]) : ℤ := f.coeff 2 ^ 2 - 3 * f.coeff 1

/-- `J = -2a₁³ + 9a₁a₂ - 27a₃`. -/
def bsJ (f : ℤ[X]) : ℤ := -2 * f.coeff 2 ^ 3 + 9 * f.coeff 2 * f.coeff 1 - 27 * f.coeff 0

/-- `H_BS(f) = max(|I|³, J²/4)`. -/
def bsHeight (f : ℤ[X]) : ℝ := max (|(bsI f : ℝ)| ^ 3) ((bsJ f : ℝ) ^ 2 / 4)

/-- The discriminant of the monic cubic `t³ + a₁t² + a₂t + a₃` (mathlib's `Cubic.discr`). -/
def discriminant (f : ℤ[X]) : ℤ :=
  (⟨1, f.coeff 2, f.coeff 1, f.coeff 0⟩ : _root_.Cubic ℤ).discr

theorem bsI_translate (k : ℤ) {f : ℤ[X]} (hf : f ∈ monicCyclic) :
    bsI (translate k f) = bsI f := by
  obtain ⟨⟨a₂, a₁, a₀, rfl⟩, -⟩ := hf
  simp only [bsI, translate_monicCubic, monicCubic_coeff_two, monicCubic_coeff_one]
  ring

theorem bsJ_translate (k : ℤ) {f : ℤ[X]} (hf : f ∈ monicCyclic) :
    bsJ (translate k f) = bsJ f := by
  obtain ⟨⟨a₂, a₁, a₀, rfl⟩, -⟩ := hf
  simp only [bsJ, translate_monicCubic, monicCubic_coeff_two, monicCubic_coeff_one,
    monicCubic_coeff_zero]
  ring

/-- `I` of a translation class. -/
def TranslationClass.I : TranslationClass → ℤ :=
  Quotient.lift (fun f : monicCyclic => bsI f) (by
    rintro f g ⟨k, h⟩
    simp only [h, bsI_translate k f.2])

/-- `J` of a translation class. -/
def TranslationClass.J : TranslationClass → ℤ :=
  Quotient.lift (fun f : monicCyclic => bsJ f) (by
    rintro f g ⟨k, h⟩
    simp only [h, bsJ_translate k f.2])

/-- `H_BS` of a translation class. -/
def TranslationClass.bsHeight (c : TranslationClass) : ℝ :=
  max (|(c.I : ℝ)| ^ 3) ((c.J : ℝ) ^ 2 / 4)

theorem TranslationClass.I_mk (f : monicCyclic) : (TranslationClass.mk f).I = bsI f := rfl

theorem TranslationClass.J_mk (f : monicCyclic) : (TranslationClass.mk f).J = bsJ f := rfl

theorem TranslationClass.bsHeight_mk (f : monicCyclic) :
    (TranslationClass.mk f).bsHeight = Cubic.Counting.TranslationClassData.bsHeight f := rfl

/-- The translation classes with `I ≤ Y`. -/
def classesUpTo (Y : ℝ) : Set TranslationClass := {c | (c.I : ℝ) ≤ Y}

/-- `C(Y)`, the number of translation classes with `I ≤ Y`. -/
def classCount (Y : ℝ) : ℕ := Nat.card (classesUpTo Y)

/-- The translation classes with `H_BS ≤ H`. -/
def bsClasses (H : ℝ) : Set TranslationClass := {c | c.bsHeight ≤ H}

/-- `#{f : H_BS(f) ≤ H}`, with `f` ranging over translation classes. -/
def bsCount (H : ℝ) : ℕ := Nat.card (bsClasses H)

end Cubic.Counting.TranslationClassData
