import Cubic.BoxAsymptotic.HeckePrimeFactors

/-! Character sums on actual prime-power norm fibers.  Unique ideal
factorization gives the finite split sum and the parity condition at inert
primes. These computations precede the analytic summation of the local series.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckePrimePowerCoefficients

open UniqueFactorizationMonoid
open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.AngularIdeals
open Cubic.BoxAsymptotic.HeckeFiniteCharacter Cubic.BoxAsymptotic.HeckePrimeFactors
open Cubic.BoxAsymptotic.AngularCorrectionProduct Cubic.BoxAsymptotic.IdealNormFibers

theorem natIdeal_pow (p m : ℕ) : natIdeal (p ^ m) = natIdeal p ^ m := by
  simp only [natIdeal, Nat.cast_pow, Ideal.span_singleton_pow]

theorem dvd_natIdeal_pow {p m : ℕ} {I : Ideal Integers}
    (hI : Ideal.absNorm I = p ^ m) : I ∣ natIdeal p ^ m := by
  rw [← natIdeal_pow, ← hI]
  exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_absNorm_le I)

theorem split_decomposition (p : SplitPrimes) {m : ℕ} {I : Ideal Integers}
    (hI : Ideal.absNorm I = (p.1 : ℕ) ^ m) :
    ∃ r ≤ m, I = splitPrime p ^ r * splitOther p ^ (m - r) := by
  have hd := dvd_natIdeal_pow hI
  rw [← split_mul, mul_pow] at hd
  obtain ⟨J, K, hJ, hK, he⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨r, _, hr⟩ := (dvd_prime_pow (splitPrime_prime p) m).mp hJ
  obtain ⟨s, _, hs⟩ := (dvd_prime_pow (splitOther_prime p) m).mp hK
  have he' : I = splitPrime p ^ r * splitOther p ^ s :=
    he.trans (congrArg₂ (· * ·) (associated_iff_eq.mp hr) (associated_iff_eq.mp hs))
  have hn : r + s = m := by
    have hn' := hI
    rw [he', map_mul, map_pow, map_pow, norm_splitPrime, norm_splitOther, ← pow_add] at hn'
    exact pow_right_injective₀ p.1.2.pos p.1.2.ne_one hn'
  exact ⟨r, by omega, by simpa only [show m - r = s by omega] using he'⟩

def splitIdeal (p : SplitPrimes) (m : ℕ) (r : Fin (m + 1)) : Fiber ((p.1 : ℕ) ^ m) :=
  ⟨splitPrime p ^ r.val * splitOther p ^ (m - r.val), by
    rw [map_mul, map_pow, map_pow, norm_splitPrime, norm_splitOther, ← pow_add,
      Nat.add_sub_of_le (by omega : r.val ≤ m)]⟩

theorem splitIdeal_injective (p : SplitPrimes) (m : ℕ) : Function.Injective (splitIdeal p m) := by
  classical
  intro r s he
  have hcount (j : ℕ) (l : ℕ) :
      (normalizedFactors (splitPrime p ^ j * splitOther p ^ l)).count (splitPrime p) = j := by
    rw [normalizedFactors_mul (pow_ne_zero _ (splitPrime_prime p).ne_zero)
      (pow_ne_zero _ (splitOther_prime p).ne_zero), normalizedFactors_pow,
      normalizedFactors_pow, normalizedFactors_irreducible (splitPrime_prime p).irreducible,
      normalizedFactors_irreducible (splitOther_prime p).irreducible]
    simp [normalize_eq, (splitOther_ne p).symm]
  apply Fin.ext
  have h := congrArg (fun I : Ideal Integers => (normalizedFactors I).count (splitPrime p))
    (congrArg Subtype.val he)
  simpa only [splitIdeal, hcount] using h

theorem splitIdeal_surjective (p : SplitPrimes) (m : ℕ) :
    Function.Surjective (splitIdeal p m) := by
  intro I
  obtain ⟨r, hr, he⟩ := split_decomposition p I.property
  exact ⟨⟨r, by omega⟩, Subtype.ext he.symm⟩

def splitEquiv (p : SplitPrimes) (m : ℕ) : Fin (m + 1) ≃ Fiber ((p.1 : ℕ) ^ m) :=
  Equiv.ofBijective (splitIdeal p m) ⟨splitIdeal_injective p m, splitIdeal_surjective p m⟩

theorem split_coefficient (k : ℤ) (p : SplitPrimes) (m : ℕ) :
    HeckeSeriesConvergence.coefficient (psi k) ((p.1 : ℕ) ^ m) =
      ∑ r : Fin (m + 1), splitPhase k p ^ r.val * (splitPhase k p)⁻¹ ^ (m - r.val) := by
  have hf : HeckeSeriesConvergence.coefficient (psi k) ((p.1 : ℕ) ^ m) =
      ∑ᶠ I : Fiber ((p.1 : ℕ) ^ m), psi k I.val :=
    (finsum_subtype_eq_finsum_cond (f := psi k) (fun I => Ideal.absNorm I = (p.1 : ℕ) ^ m)).symm
  rw [hf, ← finsum_comp_equiv (splitEquiv p m), finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro r _
  change psiHom k (splitPrime p ^ r.val * splitOther p ^ (m - r.val)) = _
  simp only [map_mul, map_pow, psiHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    psi_splitOther, splitPhase]

theorem inert_decomposition (p : InertPrimes) {m : ℕ} {I : Ideal Integers}
    (hI : Ideal.absNorm I = (p.1 : ℕ) ^ m) :
    ∃ j : ℕ, 2 * j = m ∧ I = natIdeal p.1 ^ j := by
  obtain ⟨j, _, hj⟩ := (dvd_prime_pow (inert_prime p) m).mp (dvd_natIdeal_pow hI)
  have he := associated_iff_eq.mp hj
  refine ⟨j, ?_, he⟩
  rw [he, map_pow, natIdeal, norm_span_nat, ← pow_mul] at hI
  exact pow_right_injective₀ p.1.2.pos p.1.2.ne_one hI

theorem inert_even_fiber (p : InertPrimes) (j : ℕ) :
    {I : Ideal Integers | Ideal.absNorm I = (p.1 : ℕ) ^ (2 * j)} = {natIdeal p.1 ^ j} := by
  ext I
  constructor
  · intro hI
    obtain ⟨l, hl, he⟩ := inert_decomposition p hI
    have : l = j := by omega
    simpa only [Set.mem_singleton_iff, this] using he
  · rintro rfl
    simp only [Set.mem_setOf_eq, map_pow, natIdeal, norm_span_nat, pow_mul]

theorem inert_odd_fiber (p : InertPrimes) (j : ℕ) :
    {I : Ideal Integers | Ideal.absNorm I = (p.1 : ℕ) ^ (2 * j + 1)} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro I hI
  obtain ⟨l, hl, _⟩ := inert_decomposition p hI
  omega

theorem inert_even_coefficient {k : ℤ} (hk : Even k) (p : InertPrimes) (j : ℕ) :
    HeckeSeriesConvergence.coefficient (psi k) ((p.1 : ℕ) ^ (2 * j)) = 1 := by
  rw [HeckeSeriesConvergence.coefficient, inert_even_fiber, finsum_mem_singleton]
  change psiHom k (natIdeal p.1 ^ j) = 1
  rw [map_pow]
  change psi k (natIdeal p.1) ^ j = 1
  rw [psi_nat_inert hk, one_pow]

theorem inert_odd_coefficient (k : ℤ) (p : InertPrimes) (j : ℕ) :
    HeckeSeriesConvergence.coefficient (psi k) ((p.1 : ℕ) ^ (2 * j + 1)) = 0 := by
  rw [HeckeSeriesConvergence.coefficient, inert_odd_fiber]
  simp

end Cubic.BoxAsymptotic.HeckePrimePowerCoefficients
