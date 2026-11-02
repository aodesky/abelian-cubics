import Cubic.PoissonSummation.CyclotomicIntegerUnits
import Cubic.PoissonSummation.FiniteEulerProduct
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Actual prime ideals of the quadratic cyclotomic field

Arithmetic input to the genuine Dedekind-zeta comparison in `prop:leadingTerms`.
These are mathlib's ramification indices, residue degrees, absolute ideal
norms and sets of primes over rational primes in the actual ring of integers.
They are not inferred from a proposed Euler factor.
-/

noncomputable section

namespace Cubic.PoissonSummation.QuadraticIdealSplitting

open Ideal NumberField Cubic.QuadraticCorrespondence.CyclotomicField
open CyclotomicIntegerUnits FiniteEulerProduct

abbrev rationalPrime (p : Nat.Primes) : Ideal ℤ := Ideal.span {(p : ℤ)}

theorem not_dvd_three (p : Nat.Primes) (hp : (p : ℕ) ≠ 3) : ¬ (p : ℕ) ∣ 3 := by
  intro h
  exact hp ((Nat.prime_three.dvd_iff_eq p.2.ne_one).mp h).symm

theorem order_split (p : SplitPrimes) : orderOf (p.1 : ZMod 3) = 1 := by
  have he : (p.1 : ZMod 3) = 1 := by
    rw [← ZMod.natCast_mod, p.2]
    rfl
  rw [he, orderOf_one]

theorem order_inert (p : InertPrimes) : orderOf (p.1 : ZMod 3) = 2 := by
  have he : (p.1 : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, p.2]
    rfl
  rw [he]
  exact orderOf_eq_prime (by decide) (by decide)

theorem split_inertia (p : SplitPrimes) (P : Ideal Integers)
    [P.IsPrime] [P.LiesOver (rationalPrime p.1)] :
    (rationalPrime p.1).inertiaDeg P = 1 := by
  letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 3) (p.1 : ℕ) E P
    (not_dvd_three p.1 (by intro h; have := p.2; simp [h] at this))]
  exact order_split p

theorem inert_inertia (p : InertPrimes) (P : Ideal Integers)
    [P.IsPrime] [P.LiesOver (rationalPrime p.1)] :
    (rationalPrime p.1).inertiaDeg P = 2 := by
  letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 3) (p.1 : ℕ) E P
    (not_dvd_three p.1 (by intro h; have := p.2; simp [h] at this))]
  exact order_inert p

theorem unramified (p : Nat.Primes) (hp : (p : ℕ) ≠ 3) (P : Ideal Integers)
    [P.IsPrime] [P.LiesOver (rationalPrime p)] :
    Ideal.ramificationIdx (algebraMap ℤ Integers) (rationalPrime p) P = 1 := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd (m := 3) (p : ℕ) E P
    (not_dvd_three p hp)

theorem ramified_inertia (P : Ideal Integers)
    [P.IsPrime] [P.LiesOver (rationalPrime primeThree)] :
    (rationalPrime primeThree).inertiaDeg P = 1 := by
  haveI : P.LiesOver (Ideal.span {(3 : ℤ)}) := by
    simpa [rationalPrime, primeThree] using
      (inferInstance : P.LiesOver (rationalPrime primeThree))
  simpa [rationalPrime, primeThree] using
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime 3 E P

theorem ramified_index (P : Ideal Integers)
    [P.IsPrime] [P.LiesOver (rationalPrime primeThree)] :
    Ideal.ramificationIdx (algebraMap ℤ Integers) (rationalPrime primeThree) P = 2 := by
  haveI : P.LiesOver (Ideal.span {(3 : ℤ)}) := by
    simpa [rationalPrime, primeThree] using
      (inferInstance : P.LiesOver (rationalPrime primeThree))
  simpa [rationalPrime, primeThree] using
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime 3 E P

theorem split_norm (p : SplitPrimes) (P : Ideal Integers)
    [P.IsPrime] [P.LiesOver (rationalPrime p.1)] : Ideal.absNorm P = (p.1 : ℕ) := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg' P p.1.2, split_inertia p P, pow_one]

theorem inert_norm (p : InertPrimes) (P : Ideal Integers)
    [P.IsPrime] [P.LiesOver (rationalPrime p.1)] : Ideal.absNorm P = (p.1 : ℕ) ^ 2 := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg' P p.1.2, inert_inertia p P]

theorem ramified_norm (P : Ideal Integers)
    [P.IsPrime] [P.LiesOver (rationalPrime primeThree)] : Ideal.absNorm P = 3 := by
  haveI : P.LiesOver (Ideal.span {(3 : ℤ)}) := by
    simpa [rationalPrime, primeThree] using
      (inferInstance : P.LiesOver (rationalPrime primeThree))
  have h := ramified_inertia P
  simp only [rationalPrime, primeThree, Nat.cast_ofNat] at h
  rw [Ideal.absNorm_eq_pow_inertiaDeg' P Nat.prime_three]
  norm_num only [Nat.cast_ofNat]
  rw [h, pow_one]

theorem ramified_count : (Ideal.primesOver (rationalPrime primeThree) Integers).ncard = 1 :=
  IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 3 E

theorem degree_identity (p : Nat.Primes) :
    (Ideal.primesOver (rationalPrime p) Integers).ncard *
      ((rationalPrime p).ramificationIdxIn Integers * (rationalPrime p).inertiaDegIn Integers) = 2 := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {3} ℚ E
  have hp : rationalPrime p ≠ ⊥ := by simpa using p.2.ne_zero
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp Integers Gal(E/ℚ)
  rw [IsGaloisGroup.card_eq_finrank Gal(E/ℚ) ℚ E, finrank_eq_two] at h
  exact h

theorem split_count (p : SplitPrimes) :
    (Ideal.primesOver (rationalPrime p.1) Integers).ncard = 2 := by
  letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
  have hn := not_dvd_three p.1 (by intro h; have := p.2; simp [h] at this)
  have h := degree_identity p.1
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (m := 3) (p.1 : ℕ) E hn,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 3) (p.1 : ℕ) E hn,
    order_split p] at h
  simpa using h

theorem inert_count (p : InertPrimes) :
    (Ideal.primesOver (rationalPrime p.1) Integers).ncard = 1 := by
  letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
  have hn := not_dvd_three p.1 (by intro h; have := p.2; simp [h] at this)
  have h := degree_identity p.1
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (m := 3) (p.1 : ℕ) E hn,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 3) (p.1 : ℕ) E hn,
    order_inert p] at h
  omega

end Cubic.PoissonSummation.QuadraticIdealSplitting
