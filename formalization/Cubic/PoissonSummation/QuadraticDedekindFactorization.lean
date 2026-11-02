import Cubic.PoissonSummation.PrimeIdealIndex
import Cubic.PoissonSummation.QuadraticIdealSplitting
import Cubic.PoissonSummation.QuadraticDirichletCharacter

/-!
# Genuine Dedekind-zeta factorization for the quadratic field

The ideal-counting zeta series is identified with `ζ(s)L(s,χ)` on `Re(s)>1`.
The Euler factors come from actual prime ideals: two degree-one primes in
the split case, one degree-two prime in the inert case, and one degree-one
ramified prime at 3. Ramification does not multiply the norm exponent.
-/

noncomputable section

namespace Cubic.PoissonSummation.QuadraticDedekindFactorization

open Ideal NumberField QuadraticIdealSplitting FiniteEulerProduct
open Cubic.QuadraticCorrespondence.CyclotomicField CyclotomicIntegerUnits

def localFactor (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∏' Q : (rationalPrime p).primesOver Integers,
    (1 - (Ideal.absNorm Q.val : ℂ) ^ (-s))⁻¹

theorem localFactor_eq (p : Nat.Primes) (s : ℂ) (n : ℕ)
    (hn : ∀ Q : (rationalPrime p).primesOver Integers, Ideal.absNorm Q.val = n) :
    localFactor p s = ((1 - (n : ℂ) ^ (-s))⁻¹) ^
      (Ideal.primesOver (rationalPrime p) Integers).ncard := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  simp only [localFactor, hn, tprod_fintype, Finset.prod_const, Finset.card_univ,
    Set.ncard_eq_toFinset_card', Set.toFinset_card]

theorem split_factor (p : SplitPrimes) (s : ℂ) :
    localFactor p.val s = ((1 - (p.val : ℂ) ^ (-s))⁻¹) ^ 2 := by
  rw [localFactor_eq p.val s (p.val : ℕ) (fun Q => by
    letI : Q.val.IsPrime := Q.property.1
    letI : Q.val.LiesOver (rationalPrime p.val) := Q.property.2
    exact split_norm p Q.val), split_count p]

theorem inert_factor (p : InertPrimes) (s : ℂ) :
    localFactor p.val s = (1 - ((p.val : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  rw [localFactor_eq p.val s ((p.val : ℕ) ^ 2) (fun Q => by
    letI : Q.val.IsPrime := Q.property.1
    letI : Q.val.LiesOver (rationalPrime p.val) := Q.property.2
    exact inert_norm p Q.val), inert_count p, pow_one]
  congr 2
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

theorem ramified_factor (s : ℂ) :
    localFactor primeThree s = (1 - (3 : ℂ) ^ (-s))⁻¹ := by
  rw [localFactor_eq primeThree s 3 (fun Q => by
    letI : Q.val.IsPrime := Q.property.1
    letI : Q.val.LiesOver (rationalPrime primeThree) := Q.property.2
    exact ramified_norm Q.val), ramified_count, pow_one]
  rfl

theorem local_comparison (p : Nat.Primes) (s : ℂ) :
    localFactor p s = (1 - (p : ℂ) ^ (-s))⁻¹ *
      (1 - QuadraticDirichletCharacter.character (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ := by
  by_cases h3 : p = primeThree
  · subst p
    rw [ramified_factor]
    change (1 - (3 : ℂ) ^ (-s))⁻¹ = (1 - (3 : ℂ) ^ (-s))⁻¹ *
      (1 - QuadraticDirichletCharacter.character (3 : ℕ) * (3 : ℂ) ^ (-s))⁻¹
    rw [QuadraticDirichletCharacter.character_three]
    simp
  have h0 : (p : ℕ) % 3 ≠ 0 := by
    intro h
    have he : (p : ℕ) = 3 := (p.prop.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h)
    exact h3 (Subtype.ext he)
  by_cases h1 : (p : ℕ) % 3 = 1
  · rw [split_factor ⟨p, h1⟩ s, QuadraticDirichletCharacter.character_split ⟨p, h1⟩,
      one_mul, pow_two]
  · have h2 : (p : ℕ) % 3 = 2 := by omega
    rw [inert_factor ⟨p, h2⟩ s, QuadraticDirichletCharacter.character_inert ⟨p, h2⟩,
      ← mul_inv]
    congr 1
    ring

theorem factorization (s : ℂ) (hs : 1 < s.re) :
    NumberField.dedekindZeta E s =
      riemannZeta s * DirichletCharacter.LFunction QuadraticDirichletCharacter.character s := by
  have hD : HasProd (fun p => localFactor p s) (NumberField.dedekindZeta E s) :=
    PrimeIdealIndex.grouped_euler_hasProd E s hs
  have hL := (riemannZeta_eulerProduct_hasProd hs).mul
    (QuadraticDirichletCharacter.character.LSeries_eulerProduct_hasProd hs)
  rw [← DirichletCharacter.LFunction_eq_LSeries _ hs] at hL
  apply hD.unique
  simpa only [local_comparison] using hL

end Cubic.PoissonSummation.QuadraticDedekindFactorization
