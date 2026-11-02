import Cubic.BoxAsymptotic.HeckeFiniteCharacter
import Cubic.BoxAsymptotic.HeckeSeriesConvergence
import Cubic.PoissonSummation.PrimeIdealIndex

/-! The ordinary ideal-character Euler product, obtained from absolute
convergence and unique factorization of ideals. This generic form also applies
to the primitive characters before the factor at three is removed. -/

noncomputable section

namespace Cubic.BoxAsymptotic.IdealCharacterEulerProduct

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.PoissonSummation.DedekindZetaEulerProduct
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.AngularIdeals
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.HeckeFiniteCharacter

def termHom (χ : Ideal Integers →*₀ ℂ) (s : ℂ) (hs : s ≠ 0) : Ideal Integers →*₀ ℂ where
  toFun I := χ I * summand E s hs I
  map_zero' := by change χ 0 * _ = 0; rw [map_zero, zero_mul]
  map_one' := by change χ 1 * (summand E s hs) 1 = 1; rw [map_one, map_one, mul_one]
  map_mul' I J := by rw [map_mul, map_mul]; ring

theorem termHom_eq (χ : Ideal Integers →*₀ ℂ) (s : ℂ) (hs : s ≠ 0) (I : Ideal Integers) :
    termHom χ s hs I = HeckeSeriesConvergence.idealTerm (χ) s I := by
  change χ I * summand E s hs I = _
  rw [summand_eq]
  rfl

theorem termHom_absolute (χ : Ideal Integers →*₀ ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I => ‖termHom χ s (Complex.ne_zero_of_one_lt_re hs) I‖) := by
  simpa only [termHom_eq] using HeckeSeriesConvergence.ideal_series_absolute
    (χ) hχ s hs

theorem termHom_sum (χ : Ideal Integers →*₀ ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    (∑' I, termHom χ s (Complex.ne_zero_of_one_lt_re hs) I) = LSeries (HeckeSeriesConvergence.coefficient χ) s := by
  simpa only [termHom_eq] using HeckeSeriesConvergence.sum_ideals χ hχ s hs

theorem inverse_factors_multipliable (χ : Ideal Integers →*₀ ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun P : PrimeIdeals E => 1 - χ P.val * (Ideal.absNorm P.val : ℂ) ^ (-s)) := by
  have h := (termHom_absolute χ hχ s hs).subtype (fun I => Prime I)
  have he (P : PrimeIdeals E) :
      termHom χ s (Complex.ne_zero_of_one_lt_re hs) P.val =
        χ P.val * (Ideal.absNorm P.val : ℂ) ^ (-s) := rfl
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
    (by simpa only [norm_neg, Function.comp_def, he] using h :
      Summable (fun P : PrimeIdeals E => ‖-(χ P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))‖))

theorem sum_mul_inverse_product (χ : Ideal Integers →*₀ ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    LSeries (HeckeSeriesConvergence.coefficient χ) s *
      (∏' P : PrimeIdeals E, (1 - χ P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))) = 1 := by
  have h := Cubic.PoissonSummation.IdealEulerSieve.sum_mul_product
    (termHom χ s (Complex.ne_zero_of_one_lt_re hs))
    (termHom_absolute χ hχ s hs) (prime_divisor E)
  rw [termHom_sum χ hχ s hs] at h
  exact h

theorem ne_zero (χ : Ideal Integers →*₀ ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) : LSeries (HeckeSeriesConvergence.coefficient χ) s ≠ 0 := by
  intro hz
  have h := sum_mul_inverse_product χ hχ s hs
  simp [hz] at h

theorem inverse_euler_hasProd (χ : Ideal Integers →*₀ ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeals E => 1 - χ P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))
      (LSeries (HeckeSeriesConvergence.coefficient χ) s)⁻¹ := by
  have he : (∏' P : PrimeIdeals E,
      (1 - χ P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))) = (LSeries (HeckeSeriesConvergence.coefficient χ) s)⁻¹ := by
    apply mul_left_cancel₀ (ne_zero χ hχ s hs)
    rw [sum_mul_inverse_product χ hχ s hs, mul_inv_cancel₀ (ne_zero χ hχ s hs)]
  rw [← he]
  exact (inverse_factors_multipliable χ hχ s hs).hasProd

theorem euler_hasProd (χ : Ideal Integers →*₀ ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeals E => (1 - χ P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹)
      (LSeries (HeckeSeriesConvergence.coefficient χ) s) := by
  have h := (inverse_euler_hasProd χ hχ s hs).inv₀ (inv_ne_zero (ne_zero χ hχ s hs))
  simpa only [HasProd, Function.comp_def, ← Finset.prod_inv_distrib, inv_inv] using h

end Cubic.BoxAsymptotic.IdealCharacterEulerProduct
