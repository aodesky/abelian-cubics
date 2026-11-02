import Cubic.QuadraticCorrespondence.QuotientCharacterKernel
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The lifting obstruction for quotient-character values

A pair `(a,b)` of nonzero values lies in the image of the original cover
exactly when `a²b` has a cube root in the base field. Thus the quotient-character
map is surjective over an algebraically closed field. The criterion keeps
the obstruction over smaller fields explicit; it does not identify their
quotient-torus points with a quotient of points of the cover.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CharacterCoefficients

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters

variable {K : Type*} [Field K] [CharZero K]
variable (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0)

/-- The precise obstruction to lifting a pair of quotient-character values. -/
theorem mem_range_quotientCharacters_iff (x : Kˣ × Kˣ) :
    x ∈ (quotientCharacters ζ hζ).range ↔ ∃ c : Kˣ, c ^ 3 = x.1 ^ 2 * x.2 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨firstCharacter ζ hζ g, (quotient_first_monomial ζ hζ g).symm⟩
  · rintro ⟨c, hc⟩
    let g := (GroupAlgebraSplitting.charactersEquiv ζ hζ).symm (c, x.1 * x.2 / c)
    have hg := (GroupAlgebraSplitting.charactersEquiv ζ hζ).apply_symm_apply
      (c, x.1 * x.2 / c)
    have hfirst : firstCharacter ζ hζ g = c := congrArg Prod.fst hg
    have hsecond : secondCharacter ζ hζ g = x.1 * x.2 / c := congrArg Prod.snd hg
    refine ⟨g, Prod.ext ?_ ?_⟩
    · change firstCharacter ζ hζ g ^ 2 / secondCharacter ζ hζ g = x.1
      rw [hfirst, hsecond, div_div_eq_mul_div, ← pow_succ, hc]
      simp [pow_two, mul_assoc]
    · change secondCharacter ζ hζ g ^ 2 / firstCharacter ζ hζ g = x.2
      rw [hfirst, hsecond, div_pow, div_div, ← pow_succ, hc, mul_pow,
        mul_div_mul_left_eq_div]
      simp [pow_succ]

/-- Over an algebraically closed field the cube-root obstruction vanishes.
This is a statement about geometric points, not arbitrary rational points. -/
theorem quotientCharacters_surjective [IsAlgClosed K] :
    Function.Surjective (quotientCharacters ζ hζ) := by
  intro x
  change x ∈ (quotientCharacters ζ hζ).range
  apply (mem_range_quotientCharacters_iff ζ hζ x).mpr
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((x.1 ^ 2 * x.2 : Kˣ) : K)
    (by decide : 0 < (3 : ℕ))
  have hcnz : c ≠ 0 := by
    intro hzero
    apply (x.1 ^ 2 * x.2).ne_zero
    rw [hzero, zero_pow (by decide)] at hc
    exact hc.symm
  refine ⟨Units.mk0 c hcnz, ?_⟩
  apply Units.ext
  exact hc

end Cubic.QuadraticCorrespondence.CharacterCoefficients
