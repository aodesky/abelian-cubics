import Cubic.BoxAsymptotic.HeckeFiniteCharacter
import Cubic.BoxAsymptotic.HeckeSeriesConvergence
import Cubic.PoissonSummation.PrimeIdealIndex

/-! The Euler product of the independently defined `L^(3)(s,psi_k)`.
The ideal sieve and absolute convergence justify all products and regrouping;
no analytic continuation or Euler identity for the cubic-norm series is assumed.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeEulerProduct

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.PoissonSummation.DedekindZetaEulerProduct
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.AngularIdeals
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.HeckeFiniteCharacter

def termHom (k : ℤ) (s : ℂ) (hs : s ≠ 0) : Ideal Integers →*₀ ℂ where
  toFun I := psi k I * summand E s hs I
  map_zero' := by simp [psi]
  map_one' := by rw [psi_one, map_one, mul_one]
  map_mul' I J := by rw [psi_mul, map_mul]; ring

theorem termHom_eq (k : ℤ) (s : ℂ) (hs : s ≠ 0) (I : Ideal Integers) :
    termHom k s hs I = HeckeSeriesConvergence.idealTerm (psi k) s I := by
  change psi k I * summand E s hs I = _
  rw [summand_eq]
  rfl

theorem termHom_absolute (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I => ‖termHom k s (Complex.ne_zero_of_one_lt_re hs) I‖) := by
  simpa only [termHom_eq] using HeckeSeriesConvergence.ideal_series_absolute
    (psi k) (HeckeSeriesConvergence.norm_psi_le k) s hs

theorem termHom_sum (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    (∑' I, termHom k s (Complex.ne_zero_of_one_lt_re hs) I) = heckeSeries k s := by
  simpa only [termHom_eq] using HeckeSeriesConvergence.hecke_sum_ideals k s hs

theorem inverse_factors_multipliable (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun P : PrimeIdeals E => 1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s)) := by
  have h := (termHom_absolute k s hs).subtype (fun I => Prime I)
  have he (P : PrimeIdeals E) :
      termHom k s (Complex.ne_zero_of_one_lt_re hs) P.val =
        psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s) := rfl
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
    (by simpa only [norm_neg, Function.comp_def, he] using h :
      Summable (fun P : PrimeIdeals E => ‖-(psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))‖))

theorem sum_mul_inverse_product (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    heckeSeries k s *
      (∏' P : PrimeIdeals E, (1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))) = 1 := by
  have h := Cubic.PoissonSummation.IdealEulerSieve.sum_mul_product
    (termHom k s (Complex.ne_zero_of_one_lt_re hs))
    (termHom_absolute k s hs) (prime_divisor E)
  rw [termHom_sum k s hs] at h
  exact h

theorem ne_zero (k : ℤ) (s : ℂ) (hs : 1 < s.re) : heckeSeries k s ≠ 0 := by
  intro hz
  have h := sum_mul_inverse_product k s hs
  simp [hz] at h

theorem inverse_euler_hasProd (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeals E => 1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))
      (heckeSeries k s)⁻¹ := by
  have he : (∏' P : PrimeIdeals E,
      (1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))) = (heckeSeries k s)⁻¹ := by
    apply mul_left_cancel₀ (ne_zero k s hs)
    rw [sum_mul_inverse_product k s hs, mul_inv_cancel₀ (ne_zero k s hs)]
  rw [← he]
  exact (inverse_factors_multipliable k s hs).hasProd

theorem euler_hasProd (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeals E => (1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹)
      (heckeSeries k s) := by
  have h := (inverse_euler_hasProd k s hs).inv₀ (inv_ne_zero (ne_zero k s hs))
  simpa only [HasProd, Function.comp_def, ← Finset.prod_inv_distrib, inv_inv] using h

theorem grouped_euler_hasProd (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      ∏' P : (Cubic.PoissonSummation.PrimeIdealIndex.rationalPrime p).primesOver Integers,
        (1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹) (heckeSeries k s) := by
  let below := Cubic.PoissonSummation.PrimeIdealIndex.below E
  have h := ((Equiv.sigmaFiberEquiv below).hasProd_iff).mpr (euler_hasProd k s hs)
  have hg := h.sigma (fun p => by
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    letI : Finite {P : PrimeIdeals E // below P = p} := Finite.of_equiv
      ((Cubic.PoissonSummation.PrimeIdealIndex.rationalPrime p).primesOver Integers)
      (Cubic.PoissonSummation.PrimeIdealIndex.fiberEquiv E p).symm
    exact Multipliable.of_finite.hasProd)
  have he (p : Nat.Primes) :
      (∏' P : {P : PrimeIdeals E // below P = p},
        (1 - psi k P.val.val * (Ideal.absNorm P.val.val : ℂ) ^ (-s))⁻¹) =
      ∏' P : (Cubic.PoissonSummation.PrimeIdealIndex.rationalPrime p).primesOver Integers,
        (1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹ :=
    (Cubic.PoissonSummation.PrimeIdealIndex.fiberEquiv E p).tprod_eq
      (fun P => (1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹)
  change HasProd (fun p => ∏' P : {P : PrimeIdeals E // below P = p},
    (1 - psi k P.val.val * (Ideal.absNorm P.val.val : ℂ) ^ (-s))⁻¹) (heckeSeries k s) at hg
  simpa only [he] using hg

end Cubic.BoxAsymptotic.HeckeEulerProduct
