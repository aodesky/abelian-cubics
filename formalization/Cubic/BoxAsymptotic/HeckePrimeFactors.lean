import Cubic.BoxAsymptotic.AngularCorrectionProduct
import Cubic.BoxAsymptotic.IdealNormFibers
import Cubic.BoxAsymptotic.HeckeModulus
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! The prime ideals and character values in the rational-prime Euler factors.
The two split values are reciprocal because their product is the character of
the rational principal ideal; no choice of a complex argument is used.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckePrimeFactors

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.PoissonSummation.QuadraticIdealSplitting
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.AngularIdeals
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.PrimaryGenerator
open Cubic.BoxAsymptotic.HeckeFiniteCharacter Cubic.BoxAsymptotic.HeckeGeneratorPhases
open Cubic.BoxAsymptotic.AngularCorrectionProduct

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

def natIdeal (n : ℕ) : Ideal Integers := Ideal.span {(n : Integers)}

theorem map_rationalPrime (p : Nat.Primes) :
    (rationalPrime p).map (algebraMap ℤ Integers) = natIdeal p := by
  simp [rationalPrime, natIdeal, Ideal.map_span, Set.image_singleton]

theorem natIdeal_eq_prod (p : Nat.Primes) (hp : (p : ℕ) ≠ 3) :
    natIdeal p = ∏ P ∈ (rationalPrime p).primesOver Integers, P := by
  classical
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hp0 : rationalPrime p ≠ 0 := by simpa using p.2.ne_zero
  rw [← map_rationalPrime, Ideal.map_algebraMap_eq_finset_prod_pow hp0]
  apply Finset.prod_congr rfl
  intro P hP
  have hm : P ∈ (rationalPrime p).primesOver Integers := by simpa using hP
  letI := hm.1
  letI := hm.2
  rw [unramified p hp P, pow_one]

theorem exists_split_other (p : SplitPrimes) :
    ∃ Q : Ideal Integers, Q ≠ splitPrime p ∧
      (rationalPrime p.1).primesOver Integers = {splitPrime p, Q} := by
  obtain ⟨P, Q, hPQ, he⟩ := Set.ncard_eq_two.mp (split_count p)
  have hm := splitPrime_mem p
  rw [he] at hm
  rcases Set.mem_insert_iff.mp hm with hP | hQ
  · exact ⟨Q, by simpa [hP] using hPQ.symm, by simpa [hP] using he⟩
  · have hQ' : splitPrime p = Q := Set.mem_singleton_iff.mp hQ
    exact ⟨P, by simpa [hQ'] using hPQ, by simpa [hQ', Set.pair_comm] using he⟩

def splitOther (p : SplitPrimes) : Ideal Integers := (exists_split_other p).choose

theorem splitOther_ne (p : SplitPrimes) : splitOther p ≠ splitPrime p :=
  (exists_split_other p).choose_spec.1

theorem split_primes (p : SplitPrimes) :
    (rationalPrime p.1).primesOver Integers = {splitPrime p, splitOther p} :=
  (exists_split_other p).choose_spec.2

theorem splitOther_mem (p : SplitPrimes) :
    splitOther p ∈ (rationalPrime p.1).primesOver Integers := by
  rw [split_primes]
  simp

theorem norm_splitOther (p : SplitPrimes) : Ideal.absNorm (splitOther p) = (p.1 : ℕ) := by
  letI := (splitOther_mem p).1
  letI := (splitOther_mem p).2
  exact split_norm p _

theorem split_mul (p : SplitPrimes) : splitPrime p * splitOther p = natIdeal p.1 := by
  classical
  have he : ((rationalPrime p.1).primesOver Integers).toFinset =
      {splitPrime p, splitOther p} := by
    ext I
    simp only [Set.mem_toFinset, split_primes, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  rw [natIdeal_eq_prod p.1 (by intro h; have := p.2; simp [h] at this), he]
  simp [(splitOther_ne p).symm]

theorem psi_nat_split (k : ℤ) (p : SplitPrimes) : psi k (natIdeal p.1) = 1 := by
  have h3 : ¬ 3 ∣ Ideal.absNorm (natIdeal p.1) := by
    rw [natIdeal, IdealNormFibers.norm_span_nat]
    intro h
    have hd := Nat.prime_three.dvd_of_dvd_pow h
    have hm := Nat.mod_eq_zero_of_dvd hd
    have := p.2
    omega
  have hprimary : IsPrimary (p.1 : Integers) := by
    change reduction (p.1 : Integers) = 1
    rw [map_natCast]
    have he : (p.1 : ZMod 3) = 1 := by rw [← ZMod.natCast_mod, p.2]; rfl
    apply TrivSqZeroExt.ext <;> simp [he]
  rw [natIdeal, principal_primary k hprimary h3, map_natCast]
  exact phase_ofReal_pos k (by exact_mod_cast p.1.2.pos)

theorem psi_splitOther (k : ℤ) (p : SplitPrimes) :
    psi k (splitOther p) = (splitPhase k p)⁻¹ := by
  have he : splitPhase k p * psi k (splitOther p) = 1 := by
    rw [splitPhase, ← psi_mul, split_mul, psi_nat_split]
  exact eq_inv_of_mul_eq_one_right he

theorem splitPrime_prime (p : SplitPrimes) : Prime (splitPrime p) :=
  Ideal.prime_of_mem_primesOver (by simpa using p.1.2.ne_zero) (splitPrime_mem p)

theorem splitOther_prime (p : SplitPrimes) : Prime (splitOther p) :=
  Ideal.prime_of_mem_primesOver (by simpa using p.1.2.ne_zero) (splitOther_mem p)

theorem inert_primes (p : InertPrimes) :
    (rationalPrime p.1).primesOver Integers = {natIdeal p.1} := by
  classical
  obtain ⟨P, he⟩ := Set.ncard_eq_one.mp (inert_count p)
  have hf : ((rationalPrime p.1).primesOver Integers).toFinset = {P} := by
    ext I
    simp only [Set.mem_toFinset, he, Set.mem_singleton_iff, Finset.mem_singleton]
  have hP : natIdeal p.1 = P := by
    rw [natIdeal_eq_prod p.1 (by intro h; have := p.2; simp [h] at this), hf]
    simp
  simpa only [hP] using he

theorem inert_prime (p : InertPrimes) : Prime (natIdeal p.1) := by
  have hm : natIdeal p.1 ∈ (rationalPrime p.1).primesOver Integers := by
    rw [inert_primes]
    exact Set.mem_singleton _
  exact Ideal.prime_of_mem_primesOver (by simpa using p.1.2.ne_zero) hm

theorem psi_nat_inert {k : ℤ} (hk : Even k) (p : InertPrimes) :
    psi k (natIdeal p.1) = 1 := by
  have h3 : ¬ 3 ∣ Ideal.absNorm (natIdeal p.1) := by
    rw [natIdeal, IdealNormFibers.norm_span_nat]
    intro h
    have hd := Nat.prime_three.dvd_of_dvd_pow h
    have hm := Nat.mod_eq_zero_of_dvd hd
    have := p.2
    omega
  have hprimary : IsPrimary (-(p.1 : Integers)) := by
    change reduction (-(p.1 : Integers)) = 1
    rw [map_neg, map_natCast]
    have he : (p.1 : ZMod 3) = -1 := by
      rw [← ZMod.natCast_mod, p.2]
      decide
    apply TrivSqZeroExt.ext <;> simp [he]
  have hspan : Ideal.span {-(p.1 : Integers)} = natIdeal p.1 := by
    simp [natIdeal]
  have hv := principal_primary k hprimary (by simpa only [hspan] using h3)
  rw [hspan, map_neg, map_natCast, phase_neg k (by exact_mod_cast p.1.2.ne_zero),
    hk.neg_one_zpow, one_mul] at hv
  rw [hv]
  exact phase_ofReal_pos k (by exact_mod_cast p.1.2.pos)

theorem psi_three_mul (k : ℤ) (I : Ideal Integers) : psi (3 * k) I = psi k I ^ 3 := by
  unfold psi
  split_ifs
  · simp
  · change character (3 * k) _ = character k _ ^ 3
    simp only [character, mul_comm (3 : ℤ) k, zpow_mul, zpow_ofNat]

end Cubic.BoxAsymptotic.HeckePrimeFactors
