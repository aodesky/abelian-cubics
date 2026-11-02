import CubicTargets.SantensComparison.SantensLocalHeight
import Cubic.ToricHeights.LocalHeightFormula

noncomputable section

namespace Cubic.SantensComparison.SantensLocalHeight

open scoped TensorProduct
open LocalHeightData
open Cubic.ToricHeights Cubic.QuadraticCorrespondence CyclotomicField CyclotomicTorusGalois
open QuotientLocalCharacters DescendedCoefficients

variable {A : Type*} [CommRing A] [Algebra ℚ A] {L : Type*} [Field L]
  (place : E ⊗[ℚ] A →+* L) (P : quotientFixedRing →ₐ[ℚ] A)

theorem character_formula (m : ℤ × ℤ) :
    localCharacter A place P (Multiplicative.ofAdd m) =
      nu place P ^ m.1 * nuBar place P ^ m.2 := by
  simp [localCharacter, characterValues_formula, nu, nuBar]

theorem norm_coefficient [CharZero L] :
    1 - 3 * CubicTargets.ToricHeights.LocalHeightFormula.value place P linearCoefficient =
      ((nu place P * nuBar place P : Lˣ) : L) := by
  change CubicTargets.ToricHeights.LocalHeightFormula.normValue place P = _
  rw [LocalHeightFormula.normValue_eq, character_formula]
  simp

theorem trace_coefficient [CharZero L] :
    2 - 9 * CubicTargets.ToricHeights.LocalHeightFormula.value place P linearCoefficient -
      27 * CubicTargets.ToricHeights.LocalHeightFormula.value place P constantCoefficient =
      ((nu place P ^ 2 * nuBar place P : Lˣ) : L) +
        ((nu place P * nuBar place P ^ 2 : Lˣ) : L) := by
  have hp := LocalHeightFormula.weightValue_plus place P
  have hm := LocalHeightFormula.weightValue_minus place P
  rw [character_formula] at hp hm
  simp only [zpow_ofNat, pow_one] at hp hm
  rw [← hp, ← hm]
  simp only [CubicTargets.ToricHeights.LocalHeightFormula.weightValue, Int.cast_one,
    Int.cast_neg, one_mul, neg_one_mul]
  ring

theorem finite_formula (q : ℕ) (hq : 1 < q) (ord : Lˣ →* Multiplicative ℤ) :
    (q : ℂ) ^ (supportFunction (-3) 0
      (QuotientFiniteHeight.realCoordinates (localCocharacter A place ord P)) /
        Module.finrank ℚ E) = (finiteFactor place P q ord : ℂ) := by
  rw [LocalWeightHeight.finite_localHeight A place ord q hq P]
  simp only [finiteFactor, LocalWeightHeight.characterAbs, LocalWeightHeight.localAbs,
    character_formula, zpow_ofNat, pow_one, unitAbs]

theorem complex_formula (P : quotientFixedRing →ₐ[ℚ] ℝ) :
    ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 P = (complexFactor P : ℂ) := by
  rw [LocalWeightHeight.archimedean_localHeight]
  simp only [LocalWeightHeight.archimedeanAbs_eq, character_formula,
    complexFactor, zpow_ofNat, pow_one]

theorem «eqn:santensLocalHeight» : CubicTargets.SantensComparison.SantensLocalHeight.Claim where
  split p _ _ P := by
    rw [QuotientFiniteHeight.splitInverseHeight, Complex.ofReal_mul]
    congr 1
    · exact finite_formula _ P _ (by
        rw [LocalLogarithmNormalization.padic_residue_cardinality]
        exact (Fact.out : p.Prime).one_lt) _
    · exact finite_formula _ P _ (by
        rw [LocalLogarithmNormalization.padic_residue_cardinality]
        exact (Fact.out : p.Prime).one_lt) _
  inert p _ _ P := finite_formula _ P _ (by
    rw [CyclotomicInertField.card_residueField]
    exact Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt) _
  ramified P := finite_formula _ P _ (by
    rw [CyclotomicRamifiedField.card_residueField]; norm_num) _
  complex := complex_formula

end Cubic.SantensComparison.SantensLocalHeight
