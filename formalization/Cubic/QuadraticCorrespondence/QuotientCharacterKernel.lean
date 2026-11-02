import Cubic.QuadraticCorrespondence.CharacterCoefficients
import Cubic.QuadraticCorrespondence.GroupAlgebraSplitting
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The kernel and fibres of the quotient-character map

Over a characteristic-zero field containing the third roots of unity, the
map on the original augmentation-one group-algebra units has kernel exactly
the embedded `C₃`. Its fibres are precisely the cyclic orbits. No assertion
that all rational points of the quotient lift to the cover is made here.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CharacterCoefficients

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters

variable {K : Type*} [Field K] [CharZero K]
variable (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0)

/-- The kernel consists of the original group-algebra basis units. -/
theorem quotientCharacters_eq_one_iff (g : traceOneUnits K) :
    quotientCharacters ζ hζ g = 1 ↔ ∃ i, cyclicUnits K i = g := by
  constructor
  · intro hg
    have hcube : firstCharacter ζ hζ g ^ 3 = 1 := by
      have h := quotient_first_monomial ζ hζ g
      rw [hg] at h
      simpa using h.symm
    have hsecond : secondCharacter ζ hζ g = firstCharacter ζ hζ g ^ 2 := by
      have h := congrArg Prod.fst hg
      change firstCharacter ζ hζ g ^ 2 * (secondCharacter ζ hζ g)⁻¹ = 1 at h
      exact (mul_inv_eq_one.mp h).symm
    have hprim : IsPrimitiveRoot ζ 3 := Polynomial.isRoot_cyclotomic_iff.mp (by
      simpa [Polynomial.cyclotomic_three, Polynomial.IsRoot.def] using hζ)
    have hc : (firstCharacter ζ hζ g : K) ^ 3 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hcube
    obtain ⟨j, hj, hjval⟩ := hprim.eq_pow_of_pow_eq_one hc
    let i : Multiplicative (ZMod 3) := Multiplicative.ofAdd (j : ZMod 3)
    have hfirst : firstCharacter ζ hζ (cyclicUnits K i) = firstCharacter ζ hζ g := by
      apply Units.ext
      change (character K ζ _ (cyclicUnits K i) : K) = _
      rw [character_cyclicUnits]
      change ζ ^ (j : ZMod 3).val = _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hj]
      exact hjval
    have hother : secondCharacter ζ hζ (cyclicUnits K i) = secondCharacter ζ hζ g := by
      apply Units.ext
      rw [hsecond, Units.val_pow_eq_pow_val, ← hjval]
      change (character K (ζ ^ 2) _ (cyclicUnits K i) : K) = _
      rw [character_cyclicUnits]
      change (ζ ^ 2) ^ (j : ZMod 3).val = (ζ ^ j) ^ 2
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hj, ← pow_mul, ← pow_mul, Nat.mul_comm]
    exact ⟨i, GroupAlgebraSplitting.characters_injective ζ hζ (Prod.ext hfirst hother)⟩
  · rintro ⟨i, rfl⟩
    exact quotientCharacters_cyclicUnits ζ hζ i

theorem ker_quotientCharacters :
    (quotientCharacters ζ hζ).ker = (cyclicUnits K).range := by
  ext g
  exact quotientCharacters_eq_one_iff ζ hζ g

/-- Equality of quotient-character values is exactly membership in the same
cyclic orbit on the cover. This does not assert surjectivity of the map. -/
theorem quotientCharacters_eq_iff (g h : traceOneUnits K) :
    quotientCharacters ζ hζ g = quotientCharacters ζ hζ h ↔
      ∃ i, g = cyclicUnits K i * h := by
  constructor
  · intro heq
    have hker : quotientCharacters ζ hζ (g / h) = 1 := by
      simp [map_div, heq]
    obtain ⟨i, hi⟩ := (quotientCharacters_eq_one_iff ζ hζ (g / h)).mp hker
    exact ⟨i, by rw [hi, div_mul_cancel]⟩
  · rintro ⟨i, rfl⟩
    exact quotientCharacters_cyclic_mul ζ hζ i h

end Cubic.QuadraticCorrespondence.CharacterCoefficients
