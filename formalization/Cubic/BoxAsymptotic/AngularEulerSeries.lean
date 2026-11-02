import Cubic.BoxAsymptotic.HeckePrimePowerCoefficients
import Cubic.BoxAsymptotic.AngularEulerLocal
import Cubic.BoxAsymptotic.AngularSeriesConvergence
import Cubic.PoissonSummation.HeightCountingEulerProduct

/-! The Euler product of the cube-norm ideal series, derived from its
coefficients and their absolute convergence.  The local series are evaluated
separately at split, inert and ramified rational primes.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularEulerSeries

open Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.PoissonSummation.HeightCountingEulerProduct (nat_pow_cpow)
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.AngularIdeals
open Cubic.BoxAsymptotic.AngularCorrectionProduct Cubic.BoxAsymptotic.IdealNormFibers
open Cubic.BoxAsymptotic.HeckePrimePowerCoefficients

def term (k : ℤ) (s : ℂ) (n : ℕ) : ℂ := LSeries.term (idealCoefficient k) s n

theorem term_eq (k : ℤ) (s : ℂ) (n : ℕ) :
    term k s n = idealCoefficient k n * (n : ℂ) ^ (-s) :=
  LSeries.term_def₀ (by simp [idealCoefficient]) s n

theorem term_one (k : ℤ) (s : ℂ) : term k s 1 = 1 := by
  simp [term_eq, idealCoefficient_one]

theorem term_mul (k : ℤ) (s : ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    term k s (m * n) = term k s m * term k s n := by
  simp only [term_eq, idealCoefficient_mul k hmn, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  ring

theorem term_prime_pow (k : ℤ) (p j : ℕ) (s : ℂ) :
    term k s (p ^ j) = idealCoefficient k (p ^ j) * ((p : ℂ) ^ (-s)) ^ j := by
  rw [term_eq, nat_pow_cpow]

theorem euler_hasProd
    {k : ℤ} (hk : Even k) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' j, term k s ((p : ℕ) ^ j)) (idealSeries k s) := by
  have hsum : LSeriesSummable (idealCoefficient k) s := by
    simpa only [funext (coefficient_eq k)] using
      AngularSeriesConvergence.away_summable hk s hs
  exact EulerProduct.eulerProduct_hasProd (term_one k s) (term_mul k s) hsum.norm (by simp [term])

theorem split_coefficient_eq (k : ℤ) (p : SplitPrimes) (j : ℕ) :
    idealCoefficient k ((p.1 : ℕ) ^ j) =
      AngularEulerLocal.symmetricSum (splitPhase k p) (splitPhase k p)⁻¹ (3 * j) := by
  rw [cube_coefficient, ← pow_mul, mul_comm j 3, split_coefficient]
  exact Fin.sum_univ_eq_sum_range
    (fun r => splitPhase k p ^ r * (splitPhase k p)⁻¹ ^ (3 * j - r)) (3 * j + 1)

theorem split_hasSum (k : ℤ) (p : SplitPrimes) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun j => term k s ((p.1 : ℕ) ^ j))
      ((1 + (splitPhase k p + (splitPhase k p)⁻¹) * (p.1 : ℂ) ^ (-s)) /
        ((1 - splitPhase k p ^ 3 * (p.1 : ℂ) ^ (-s)) *
          (1 - ((splitPhase k p)⁻¹) ^ 3 * (p.1 : ℂ) ^ (-s)))) := by
  have ht : splitPhase k p ≠ 0 := by
    intro h
    have hn := norm_splitPhase k p
    simp [h] at hn
  simpa only [term_prime_pow, split_coefficient_eq] using
    AngularEulerLocal.split_hasSum (norm_splitPhase k p)
      (by simp [norm_inv, norm_splitPhase]) (mul_inv_cancel₀ ht)
      ((Complex.norm_prime_cpow_le_one_half p.1 hs).trans_lt (by norm_num))

theorem inert_even {k : ℤ} (hk : Even k) (p : InertPrimes) (j : ℕ) :
    idealCoefficient k ((p.1 : ℕ) ^ (2 * j)) = 1 := by
  rw [cube_coefficient, ← pow_mul, show 2 * j * 3 = 2 * (3 * j) by ring]
  exact inert_even_coefficient hk p (3 * j)

theorem inert_odd (k : ℤ) (p : InertPrimes) (j : ℕ) :
    idealCoefficient k ((p.1 : ℕ) ^ (2 * j + 1)) = 0 := by
  rw [cube_coefficient, ← pow_mul, show (2 * j + 1) * 3 = 2 * (3 * j + 1) + 1 by ring]
  exact inert_odd_coefficient k p (3 * j + 1)

theorem inert_hasSum {k : ℤ} (hk : Even k) (p : InertPrimes) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun j => term k s ((p.1 : ℕ) ^ j)) (1 - ((p.1 : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  have hx : ‖((p.1 : ℂ) ^ (-s)) ^ 2‖ < 1 := by
    rw [norm_pow]
    have h := Complex.norm_prime_cpow_le_one_half p.1 hs
    have := norm_nonneg ((p.1 : ℂ) ^ (-s))
    nlinarith
  have he : HasSum (fun j => term k s ((p.1 : ℕ) ^ (2 * j)))
      (1 - ((p.1 : ℂ) ^ (-s)) ^ 2)⁻¹ := by
    convert hasSum_geometric_of_norm_lt_one hx using 1
    funext j
    rw [term_prime_pow, inert_even hk, one_mul, pow_mul]
  have ho : HasSum (fun j => term k s ((p.1 : ℕ) ^ (2 * j + 1))) 0 := by
    simp only [term_prime_pow, inert_odd, zero_mul]
    exact hasSum_zero
  simpa only [add_zero] using he.even_add_odd (f := fun j => term k s ((p.1 : ℕ) ^ j)) ho

theorem three_hasSum (k : ℤ) (s : ℂ) : HasSum (fun j => term k s (3 ^ j)) 1 := by
  have h : HasSum (fun j => term k s (3 ^ (j + 1))) 0 := by
    have he : (fun j => term k s (3 ^ (j + 1))) = fun _ => 0 := by
      funext j
      simp [term_eq, idealCoefficient, pow_succ]
    rw [he]
    exact hasSum_zero
  simpa only [pow_zero, term_one, add_zero] using h.zero_add (f := fun j => term k s (3 ^ j))

end Cubic.BoxAsymptotic.AngularEulerSeries
