import CubicTargets.ToricHeights.LocalHeightFormula
import Cubic.ToricHeights.LocalWeightHeight
import Cubic.QuadraticCorrespondence.CyclotomicInertResidueField
import Cubic.QuadraticCorrespondence.CyclotomicRamifiedResidueField

/-!
# Proof of `eqn:localHeight`

The paper's argument: by [Fulton, p. 68] the support function of `3D₀` is the minimum of
the pairings with the four weights `0, a'+b', 2a'+b', a'+2b'` of `H⁰(S_E, O(3D₀))`, and
`q_w^{-⟨u, ℓ_w(x)⟩} = |χ^u(x)|_w`; the weight-vector values are `1-3e₂` and `z±`.
In Lean:

* `LocalWeightHeight.triangle_min` (Fulton's step for this triangle) and
  `finite_localHeight` / `archimedean_localHeight` give the local factor as the maximum of
  `1` and the three character absolute values;
* `WeightVectors.normCharacter_value` and `character_eq_weightValue`
  (`eqn:formulaForNormCharacter`, `eqn:formulaForNormCharacter2` at points of `T`) identify
  the character values with `1-3e₂`, `z₊ = χ^{2a'+b'}` and `z₋ = χ^{a'+2b'}`. Being unit
  values, they are nonzero.

The generic finite statement (`finite_formula`) is then specialized to each place.
-/

noncomputable section

namespace Cubic.ToricHeights.LocalHeightFormula

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois DescendedCoefficients QuotientLocalCharacters
open CubicTargets.ToricHeights.LocalHeightFormula

section Local

variable {A : Type*} [CommRing A] [Algebra ℚ A] {L : Type*} [Field L] [CharZero L]
variable (place : E ⊗[ℚ] A →+* L) (P : quotientFixedRing →ₐ[ℚ] A)

theorem normValue_eq :
    normValue place P = ((localCharacter A place P (Multiplicative.ofAdd (1, 1)) : Lˣ) : L) :=
  (WeightVectors.normCharacter_value A place P).symm

theorem weightValue_eq (sign : ℤ) :
    weightValue place P sign = WeightVectors.weightValue A place sign P := by
  rw [WeightVectors.weightValue, WeightVectors.place_tmul, weightValue, value, value, value,
    sqrtNegTwentySeven]
  ring

theorem weightValue_plus :
    weightValue place P 1 = ((localCharacter A place P (Multiplicative.ofAdd (2, 1)) : Lˣ) : L) := by
  rw [weightValue_eq, (WeightVectors.character_eq_weightValue A place P).1]

theorem weightValue_minus :
    weightValue place P (-1) =
      ((localCharacter A place P (Multiplicative.ofAdd (1, 2)) : Lˣ) : L) := by
  rw [weightValue_eq, (WeightVectors.character_eq_weightValue A place P).2]

variable (ord : Lˣ →* Multiplicative ℤ)

omit [CharZero L] in
theorem wAbs_eq (q : ℕ) (m : ℤ × ℤ) (y : L) (hy : y ≠ 0)
    (h : y = ((localCharacter A place P (Multiplicative.ofAdd m) : Lˣ) : L)) :
    wAbs q ord y hy = LocalWeightHeight.characterAbs A place ord q P m := by
  have hu : Units.mk0 y hy = localCharacter A place P (Multiplicative.ofAdd m) :=
    Units.ext (by rw [Units.val_mk0, h])
  rw [wAbs, hu]
  rfl

/-- `eqn:localHeight` at an arbitrary finite place. -/
theorem finite_formula (q : ℕ) (hq : 1 < q) :
    FiniteFormula place P q ord ((q : ℂ) ^ (supportFunction (-3) 0
      (QuotientFiniteHeight.realCoordinates (localCocharacter A place ord P)) /
        Module.finrank ℚ E)) := by
  have hN : normValue place P ≠ 0 := by rw [normValue_eq]; exact Units.ne_zero _
  have hp : weightValue place P 1 ≠ 0 := by rw [weightValue_plus]; exact Units.ne_zero _
  have hm : weightValue place P (-1) ≠ 0 := by rw [weightValue_minus]; exact Units.ne_zero _
  refine ⟨hN, hm, hp, ?_⟩
  rw [LocalWeightHeight.finite_localHeight A place ord q hq P,
    wAbs_eq place P ord q (1, 1) _ hN (normValue_eq place P),
    wAbs_eq place P ord q (1, 2) _ hm (weightValue_minus place P),
    wAbs_eq place P ord q (2, 1) _ hp (weightValue_plus place P),
    CyclotomicField.finrank_eq_two, max_comm (LocalWeightHeight.characterAbs A place ord q P (1, 2))]
  norm_num

end Local

/-- The complex image of `√-27 = 3(2ζ+1)` is `i√27`. -/
theorem complex_sqrtNegTwentySeven :
    CyclotomicArchimedean.place (WeightVectors.sqrtNegTwentySeven ⊗ₜ[ℚ] (1 : ℝ)) =
      Complex.I * Real.sqrt 27 := by
  have hinc : ∀ x : E, CyclotomicArchimedean.place (x ⊗ₜ[ℚ] (1 : ℝ)) =
      (CyclotomicArchimedean.place.toAlgHom.comp Algebra.TensorProduct.includeLeft) x :=
    fun _ => rfl
  rw [hinc, WeightVectors.sqrtNegTwentySeven, CyclotomicField.sqrtNegThree]
  simp only [map_mul, map_add, map_ofNat, map_one]
  rw [← hinc, CyclotomicArchimedean.place_zeta]
  have h27 : Real.sqrt 27 = 3 * Real.sqrt 3 := by
    rw [show (27 : ℝ) = 3 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  apply Complex.ext <;> simp [CyclotomicArchimedean.zeta, h27] <;> ring

theorem complex_value (P : quotientFixedRing →ₐ[ℚ] ℝ) (f : quotientFixedRing) :
    value CyclotomicArchimedean.place.toRingHom P f = (P f : ℂ) :=
  CyclotomicArchimedean.place_scalar _

theorem complexWeightValue_eq (P : quotientFixedRing →ₐ[ℚ] ℝ) (sign : ℤ) :
    complexWeightValue P sign = weightValue CyclotomicArchimedean.place.toRingHom P sign := by
  rw [complexWeightValue, weightValue, complex_value, complex_value, complex_value,
    CubicTargets.ToricHeights.LocalHeightFormula.sqrtNegTwentySeven]
  change _ = _ + _ * (CyclotomicArchimedean.place
    (WeightVectors.sqrtNegTwentySeven ⊗ₜ[ℚ] (1 : ℝ)) / 2) * _
  rw [complex_sqrtNegTwentySeven]

theorem complex_formula (P : quotientFixedRing →ₐ[ℚ] ℝ) :
    ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 P =
      ((max (max 1 (‖1 - 3 * (P linearCoefficient : ℂ)‖ ^ 2))
        (max (‖complexWeightValue P (-1)‖ ^ 2) (‖complexWeightValue P 1‖ ^ 2))) ^
          (1 / (Module.finrank ℚ E : ℝ)) : ℝ) := by
  have hN : (1 - 3 * (P linearCoefficient : ℂ)) =
      ((localCharacter ℝ CyclotomicArchimedean.place.toRingHom P (Multiplicative.ofAdd (1, 1)) :
        ℂˣ) : ℂ) := by
    rw [← normValue_eq, normValue, complex_value]
  rw [LocalWeightHeight.archimedean_localHeight, LocalWeightHeight.archimedeanAbs_eq,
    LocalWeightHeight.archimedeanAbs_eq, LocalWeightHeight.archimedeanAbs_eq, hN,
    complexWeightValue_eq, complexWeightValue_eq, weightValue_plus, weightValue_minus,
    CyclotomicField.finrank_eq_two,
    max_comm (‖((localCharacter ℝ CyclotomicArchimedean.place.toRingHom P
      (Multiplicative.ofAdd (2, 1)) : ℂˣ) : ℂ)‖ ^ 2)]
  norm_num

theorem «eqn:localHeight» : Claim where
  split_first p _ _ P := finite_formula _ P _ _ (by
    rw [LocalLogarithmNormalization.padic_residue_cardinality]; exact (Fact.out : p.Prime).one_lt)
  split_second p _ _ P := finite_formula _ P _ _ (by
    rw [LocalLogarithmNormalization.padic_residue_cardinality]; exact (Fact.out : p.Prime).one_lt)
  inert p _ _ P := finite_formula _ P _ _ (by
    rw [CyclotomicInertField.card_residueField]
    exact Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt)
  ramified P := finite_formula _ P _ _ (by
    rw [CyclotomicRamifiedField.card_residueField]; norm_num)
  complex := complex_formula

end Cubic.ToricHeights.LocalHeightFormula
