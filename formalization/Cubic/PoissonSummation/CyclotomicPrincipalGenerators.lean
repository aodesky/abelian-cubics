import Cubic.PoissonSummation.CyclotomicIntegerLocal
import Mathlib.Analysis.Normed.Ring.Ultra

/-!
# Local norms of global principal generators

Expand the paper's class-number-one input using ideals in the actual ring of
integers. A generator of `(a,b)` has local norm `max(‖a‖,‖b‖)` because every
global integer has local norm at most one. In particular the ideals
`(p,ζ-r)` can select one of the two places above a split prime.
-/

noncomputable section

namespace Cubic.PoissonSummation.CyclotomicPrincipalGenerators

open Cubic.QuadraticCorrespondence CyclotomicIntegerUnits

/-- A Bézout ideal generator realizes the minimum valuation of its two generators. -/
theorem norm_gcd_image {R F : Type*} [CommRing R] [IsBezout R]
    [NormedField F] [IsUltrametricDist F]
    (f : R →+* F) (hf : ∀ x, ‖f x‖ ≤ 1) (a b : R) :
    ‖f (IsBezout.gcd a b)‖ = max ‖f a‖ ‖f b‖ := by
  apply le_antisymm
  · obtain ⟨u, v, huv⟩ := IsBezout.gcd_eq_sum a b
    rw [← huv, map_add, map_mul, map_mul]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le_max
    · simpa only [norm_mul, one_mul] using
        mul_le_mul_of_nonneg_right (hf u) (norm_nonneg (f a))
    · simpa only [norm_mul, one_mul] using
        mul_le_mul_of_nonneg_right (hf v) (norm_nonneg (f b))
  · apply max_le
    · obtain ⟨c, hc⟩ := IsBezout.gcd_dvd_left a b
      calc
        ‖f a‖ = ‖f (IsBezout.gcd a b)‖ * ‖f c‖ := by
          conv_lhs => rw [hc, map_mul, norm_mul]
        _ ≤ ‖f (IsBezout.gcd a b)‖ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hf c) (norm_nonneg (f (IsBezout.gcd a b)))
    · obtain ⟨c, hc⟩ := IsBezout.gcd_dvd_right a b
      calc
        ‖f b‖ = ‖f (IsBezout.gcd a b)‖ * ‖f c‖ := by
          conv_lhs => rw [hc, map_mul, norm_mul]
        _ ≤ ‖f (IsBezout.gcd a b)‖ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hf c) (norm_nonneg (f (IsBezout.gcd a b)))

/-- Global cyclotomic integers are integral in every nonarchimedean field realization. -/
theorem norm_integer_image {F : Type*} [NormedField F] [IsUltrametricDist F]
    (f : Integers →+* F) (x : Integers) : ‖f x‖ ≤ 1 := by
  have hz : ‖f zetaInteger‖ = 1 := norm_unit_image f zetaUnit
  obtain ⟨q, rfl⟩ := integralPowerBasis.exists_eq_aeval' x
  rw [integralPowerBasis_gen]
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    rw [map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hq hr)
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      zsmul_eq_mul, mul_one, map_mul, map_intCast, map_pow, norm_mul, norm_pow, hz,
      one_pow, mul_one]
    exact IsUltrametricDist.norm_intCast_le_one F a

local instance : IsPrincipalIdealRing Integers := integers_principal

/-- A chosen generator of the actual ideal `(p,ζ-r)`; no local norm is built into its definition. -/
def splitGenerator (p r : ℕ) : Integers := IsBezout.gcd (p : Integers) (zetaInteger - r)

theorem norm_splitGenerator {F : Type*} [NormedField F] [IsUltrametricDist F]
    (f : Integers →+* F) (p r : ℕ) :
    ‖f (splitGenerator p r)‖ = max ‖(p : F)‖ ‖f zetaInteger - r‖ := by
  simpa only [splitGenerator, map_natCast, map_sub] using
    norm_gcd_image f (norm_integer_image f) (p : Integers) (zetaInteger - r)

/-- At a place where `p` is a unit, the same global generator is a unit. -/
theorem norm_splitGenerator_eq_one {F : Type*} [NormedField F] [IsUltrametricDist F]
    (f : Integers →+* F) (p r : ℕ) (hp : ‖(p : F)‖ = 1) :
    ‖f (splitGenerator p r)‖ = 1 := by
  rw [norm_splitGenerator, hp, max_eq_left]
  simpa only [map_sub, map_natCast] using norm_integer_image f (zetaInteger - r)

theorem splitGenerator_ne_zero (p r : ℕ) (hp : p ≠ 0) : splitGenerator p r ≠ 0 := by
  intro h
  have hd := IsBezout.gcd_dvd_left (p : Integers) (zetaInteger - r)
  change splitGenerator p r ∣ (p : Integers) at hd
  rw [h, zero_dvd_iff] at hd
  exact hp (Nat.cast_eq_zero.mp hd)

end Cubic.PoissonSummation.CyclotomicPrincipalGenerators
