import Cubic.BoxAsymptotic.HeckeEulerProduct
import Cubic.BoxAsymptotic.HeckePrimeFactors
import Cubic.PoissonSummation.HeightCountingEulerProduct

/-! The rational-prime factors of the genuine Hecke Euler product, with the
factor at three omitted as in the paper.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeRationalEulerFactors

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.PoissonSummation.QuadraticIdealSplitting
open Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.AngularMomentData
open Cubic.BoxAsymptotic.AngularCorrectionProduct Cubic.BoxAsymptotic.HeckePrimeFactors

def factor (k : ℤ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∏' P : (rationalPrime p).primesOver Integers,
    (1 - psi k P.val * (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹

theorem factor_hasProd (k : ℤ) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p => factor k p s) (heckeSeries k s) :=
  HeckeEulerProduct.grouped_euler_hasProd k s hs

theorem factor_as_finprod (k : ℤ) (p : Nat.Primes) (s : ℂ) :
    factor k p s = ∏ᶠ P ∈ (rationalPrime p).primesOver Integers,
      (1 - psi k P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹ := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [factor, tprod_eq_finprod (Set.toFinite _)]
  exact finprod_set_coe_eq_finprod_mem
    (f := fun P : Ideal Integers => (1 - psi k P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹)
    ((rationalPrime p).primesOver Integers)

theorem split_factor (k : ℤ) (p : SplitPrimes) (s : ℂ) :
    factor k p.1 s = (1 - splitPhase k p * (p.1 : ℂ) ^ (-s))⁻¹ *
      (1 - (splitPhase k p)⁻¹ * (p.1 : ℂ) ^ (-s))⁻¹ := by
  classical
  rw [factor_as_finprod, split_primes, finprod_mem_insert]
  · simp only [finprod_mem_singleton, norm_splitPrime, norm_splitOther, psi_splitOther]
    rfl
  · simpa only [Set.mem_singleton_iff] using (splitOther_ne p).symm
  · exact Set.finite_singleton _

theorem inert_factor {k : ℤ} (hk : Even k) (p : InertPrimes) (s : ℂ) :
    factor k p.1 s = (1 - ((p.1 : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  rw [factor_as_finprod, inert_primes, finprod_mem_singleton, psi_nat_inert hk, one_mul]
  rw [natIdeal, Cubic.BoxAsymptotic.IdealNormFibers.norm_span_nat,
    Cubic.PoissonSummation.HeightCountingEulerProduct.nat_pow_cpow]

theorem three_factor (k : ℤ) (s : ℂ) : factor k primeThree s = 1 := by
  have hz (P : (rationalPrime primeThree).primesOver Integers) : psi k P.val = 0 := by
    have hn : Ideal.absNorm P.val = 3 := by
      letI := P.property.1
      letI := P.property.2
      exact ramified_norm _
    simp [psi, hn]
  simp only [factor, hz, zero_mul, sub_zero, inv_one, tprod_one]

end Cubic.BoxAsymptotic.HeckeRationalEulerFactors
