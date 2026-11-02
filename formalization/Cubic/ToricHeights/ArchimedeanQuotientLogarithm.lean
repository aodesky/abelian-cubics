import Cubic.QuadraticCorrespondence.CyclotomicArchimedean
import Cubic.ToricHeights.LocalLogarithmNormalization

/-!
# Archimedean character logarithms on the original quotient

Evaluate the original quotient characters through the complex place.
Their order is `-log ‖z‖`; the two basis orders determine a real cocharacter
by the dual character pairing. Only then compare it with the radial coordinate
on `ℂˣ`. The place weight `log(exp 2)/[E:ℚ]` is one, and the same cancellation
gives the support-function exponential in the archimedean inverse height.
-/

noncomputable section

namespace Cubic.ToricHeights.ArchimedeanQuotientLogarithm

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois
open CyclotomicArchimedean QuotientLocalCharacters
open LocalLogarithmNormalization
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

abbrev Points := quotientFixedRing →ₐ[ℚ] ℝ

/-- Complex order normalized by `q_w = exp 2` and the complex absolute value `‖z‖²`. -/
def order : ℂˣ →* Multiplicative ℝ where
  toFun z := Multiplicative.ofAdd (-Real.log ‖(z : ℂ)‖)
  map_one' := by simp
  map_mul' z w := by
    change -Real.log ‖((z * w : ℂˣ) : ℂ)‖ =
      -Real.log ‖(z : ℂ)‖ + -Real.log ‖(w : ℂ)‖
    rw [Units.val_mul, norm_mul, Real.log_mul
      (norm_ne_zero_iff.mpr z.ne_zero) (norm_ne_zero_iff.mpr w.ne_zero)]
    ring

theorem order_conjugate (z : ℂˣ) : order (Units.map Complex.conjAe.toMonoidHom z) = order z := by
  change Multiplicative.ofAdd (-Real.log ‖star (z : ℂ)‖) = _
  simp only [norm_star]
  rfl

/-- The place image of any invariant character, including negative exponents. -/
theorem characterValue_eq (P : Points) (m : ℤ × ℤ) :
    localCharacter ℝ place.toRingHom P (Multiplicative.ofAdd m) =
      pointEquiv P ^ m.1 * Units.map Complex.conjAe.toMonoidHom (pointEquiv P) ^ m.2 := by
  change Units.map place.toMonoidHom (characterValues ℝ P (Multiplicative.ofAdd m)) = _
  rw [characterValues_formula]
  simp only [map_mul, map_zpow]
  rw [mapped_conjugate]
  rfl

theorem character_order (P : Points) (m : ℤ × ℤ) :
    (order (localCharacter ℝ place.toRingHom P (Multiplicative.ofAdd m))).toAdd =
      (m.1 : ℝ) * (order (pointEquiv P)).toAdd +
        (m.2 : ℝ) * (order (pointEquiv P)).toAdd := by
  rw [characterValue_eq]
  rw [map_mul, map_zpow, map_zpow, order_conjugate]
  simp [zsmul_eq_mul]

/-- Orders of the two quotient characters. -/
def basisLogarithms (P : Points) : ℝ × ℝ :=
  ((order (localCharacter ℝ place.toRingHom P (Multiplicative.ofAdd (1, 0)))).toAdd,
    (order (localCharacter ℝ place.toRingHom P (Multiplicative.ofAdd (0, 1)))).toAdd)

/-- The real cocharacter determined by the original character pairing, in ray coordinates. -/
def localCocharacter (P : Points) : ℝ × ℝ :=
  let b := basisLogarithms P
  ((2 * b.1 + b.2) / 3, (b.1 + 2 * b.2) / 3)

/-- Radial coordinate under the proved original-point parametrization. -/
def coordinate (P : Points) : ℝ := Real.log ‖(pointEquiv P : ℂ)‖

theorem basisLogarithms_eq (P : Points) : basisLogarithms P = (-coordinate P, -coordinate P) := by
  rw [basisLogarithms, character_order, character_order]
  simp [order, coordinate]

theorem localCocharacter_eq (P : Points) : localCocharacter P = (-coordinate P, -coordinate P) := by
  rw [localCocharacter, basisLogarithms_eq]
  ext <;> dsimp <;> ring

/-- Pairing with every original character recovers its archimedean order. -/
theorem localCocharacter_pairing (P : Points) (m : ℤ × ℤ) :
    ((CharacterLattice.pullback m).1 : ℝ) * (localCocharacter P).1 +
      ((CharacterLattice.pullback m).2 : ℝ) * (localCocharacter P).2 =
        (order (localCharacter ℝ place.toRingHom P (Multiplicative.ofAdd m))).toAdd := by
  rw [localCocharacter_eq, character_order]
  simp [CharacterLattice.pullback, order, coordinate]
  ring

/-- The character pairing uniquely specifies the real cocharacter. -/
theorem localCocharacter_unique (P : Points) (n : ℝ × ℝ)
    (hn : ∀ m : ℤ × ℤ,
      ((CharacterLattice.pullback m).1 : ℝ) * n.1 +
        ((CharacterLattice.pullback m).2 : ℝ) * n.2 =
          (order (localCharacter ℝ place.toRingHom P (Multiplicative.ofAdd m))).toAdd) :
    n = localCocharacter P := by
  have h₁ := (hn (1, 0)).trans (localCocharacter_pairing P (1, 0)).symm
  have h₂ := (hn (0, 1)).trans (localCocharacter_pairing P (0, 1)).symm
  norm_num [CharacterLattice.pullback] at h₁ h₂
  ext <;> linarith

/-- The complex splitting-field place contribution with its global-degree weight. -/
def logarithm (P : Points) : ℝ × ℝ :=
  placeContribution (Module.finrank ℚ CyclotomicField.E) (Real.exp 2) (localCocharacter P)

theorem logarithm_eq_cocharacter (P : Points) : logarithm P = localCocharacter P := by
  simp [logarithm, placeContribution, CyclotomicField.finrank_eq_two]

theorem logarithm_eq (P : Points) : logarithm P = (-coordinate P, -coordinate P) := by
  rw [logarithm_eq_cocharacter, localCocharacter_eq]

/-- The archimedean splitting-field inverse-height factor before simplification. -/
def inverseHeight (s₀ σ : ℂ) (P : Points) : ℂ :=
  (Real.exp 2 : ℂ) ^
    (supportFunction s₀ σ (localCocharacter P) / Module.finrank ℚ CyclotomicField.E)

theorem inverseHeight_eq (s₀ σ : ℂ) (P : Points) :
    inverseHeight s₀ σ P = Complex.exp (supportFunction s₀ σ (-coordinate P, -coordinate P)) := by
  rw [inverseHeight, CyclotomicField.finrank_eq_two,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero (2 : ℝ)),
    ← Complex.ofReal_log (Real.exp_pos 2).le, Real.log_exp, localCocharacter_eq]
  congr 1
  push_cast
  ring

@[simp]
theorem coordinate_one : coordinate 1 = 0 := by simp [coordinate]

@[simp]
theorem logarithm_one : logarithm 1 = 0 := by simp [logarithm_eq]

@[simp]
theorem inverseHeight_one (s₀ σ : ℂ) : inverseHeight s₀ σ 1 = 1 := by
  simp [inverseHeight_eq, supportFunction]

theorem coordinate_mul (P Q : Points) : coordinate (P * Q) = coordinate P + coordinate Q := by
  simp only [coordinate, map_mul, Units.val_mul, norm_mul]
  exact Real.log_mul (norm_ne_zero_iff.mpr (pointEquiv P).ne_zero)
    (norm_ne_zero_iff.mpr (pointEquiv Q).ne_zero)

theorem continuous_coordinate : Continuous coordinate :=
  (continuous_norm.comp (Units.continuous_val.comp pointEquiv.continuous)).log
    (fun P => norm_ne_zero_iff.mpr (pointEquiv P).ne_zero)

theorem continuous_logarithm : Continuous logarithm := by
  have h : logarithm = fun P => (-coordinate P, -coordinate P) := funext logarithm_eq
  rw [h]
  exact continuous_coordinate.neg.prodMk continuous_coordinate.neg

theorem logarithm_mul (P Q : Points) : logarithm (P * Q) = logarithm P + logarithm Q := by
  simp [logarithm_eq, coordinate_mul, add_comm]

theorem continuous_inverseHeight (s₀ σ : ℂ) : Continuous (inverseHeight s₀ σ) := by
  have h : inverseHeight s₀ σ = fun P =>
      Complex.exp (supportFunction s₀ σ (-coordinate P, -coordinate P)) :=
    funext (inverseHeight_eq s₀ σ)
  rw [h]
  exact Complex.continuous_exp.comp ((supportFunction_continuous s₀ σ).comp
    (continuous_coordinate.neg.prodMk continuous_coordinate.neg))

private theorem exponential_formula (t : ℝ) (P : Points) :
    Circle.exp (2 * Real.pi * spectralPairing t (logarithm P)) =
      Circle.exp (2 * Real.pi * t * coordinate P) := by
  rw [logarithm_eq]
  congr 1
  dsimp [spectralPairing]
  ring

/-- The archimedean spectral character uses the same positive exponential convention. -/
def character (t : ℝ) : PontryaginDual Points where
  toFun P := Circle.exp (2 * Real.pi * spectralPairing t (logarithm P))
  map_one' := by rw [exponential_formula]; simp
  map_mul' P Q := by
    simp only [exponential_formula, coordinate_mul, mul_add, Circle.exp_add]
  continuous_toFun := by
    have h : (fun P => Circle.exp (2 * Real.pi * spectralPairing t (logarithm P))) =
        fun P => Circle.exp (2 * Real.pi * t * coordinate P) := funext (exponential_formula t)
    rw [h]
    exact Circle.exp.continuous.comp (continuous_const.mul continuous_coordinate)

theorem character_eq (t : ℝ) (P : Points) :
    character t P = Circle.exp (2 * Real.pi * t * coordinate P) := exponential_formula t P

@[simp]
theorem character_zero : character 0 = 1 := by
  apply DFunLike.ext
  intro P
  change Circle.exp (2 * Real.pi * spectralPairing 0 (logarithm P)) = 1
  simp [spectralPairing]

/-- The norm character is the product of the two original quotient characters. -/
theorem normCharacterValue_eq (P : Points) :
    (localCharacter ℝ place.toRingHom P (Multiplicative.ofAdd (1, 1)) : ℂ) =
      (‖(pointEquiv P : ℂ)‖ ^ 2 : ℝ) := by
  rw [characterValue_eq]
  change ((pointEquiv P : ℂ) ^ (1 : ℤ)) * star (pointEquiv P : ℂ) ^ (1 : ℤ) = _
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The minus sign in the norm-character pairing is inherited from the order convention. -/
theorem logarithm_normCharacter (P : Points) :
    (logarithm P).1 + (logarithm P).2 =
      -Real.log ‖(localCharacter ℝ place.toRingHom P (Multiplicative.ofAdd (1, 1)) : ℂ)‖ := by
  rw [logarithm_eq_cocharacter]
  simpa [CharacterLattice.pullback, order] using localCocharacter_pairing P (1, 1)

/-- The paper's positive radial section, as a point of the original quotient. -/
def radialSection (u : ℝ) : Points :=
  pointEquiv.symm (Units.mk0 (Real.exp u : ℂ)
    (by exact_mod_cast Real.exp_ne_zero u))

theorem continuous_radialSection : Continuous radialSection := by
  apply pointEquiv.symm.continuous.comp
  apply Units.continuous_iff.mpr
  constructor
  · exact Complex.continuous_ofReal.comp Real.continuous_exp
  · exact (Complex.continuous_ofReal.comp Real.continuous_exp).inv₀
      (fun u => Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u))

@[simp]
theorem coordinate_radialSection (u : ℝ) : coordinate (radialSection u) = u := by
  simp [coordinate, radialSection]

theorem radialSection_add (u v : ℝ) : radialSection (u + v) = radialSection u * radialSection v := by
  apply pointEquiv.injective
  simp only [radialSection, map_mul, ContinuousMulEquiv.apply_symm_apply]
  apply Units.ext
  simp [Real.exp_add]

theorem coordinate_surjective : Function.Surjective coordinate :=
  fun u => ⟨radialSection u, coordinate_radialSection u⟩

/-- `ell(a(u)) = u v₀`, with `v₀ = (-1,-1)` in ray coordinates. -/
theorem logarithm_radialSection (u : ℝ) : logarithm (radialSection u) = (-u, -u) := by
  rw [logarithm_eq, coordinate_radialSection]

theorem inverseHeight_radialSection (s₀ σ : ℂ) (u : ℝ) :
    inverseHeight s₀ σ (radialSection u) = Complex.exp (supportFunction s₀ σ (-u, -u)) := by
  rw [inverseHeight_eq, coordinate_radialSection]

theorem character_radialSection (t u : ℝ) :
    character t (radialSection u) = Circle.exp (2 * Real.pi * t * u) := by
  rw [character_eq, coordinate_radialSection]

end Cubic.ToricHeights.ArchimedeanQuotientLogarithm
