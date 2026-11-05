import Cubic.BoxAsymptotic.HeckePrimeFactors
import CubicTargets.Counting.ExactFormula

/-!
# Ideals of prime-power norm in `𝓞_E`

Supporting arithmetic for the last step of `thm:exactFormula`, `d_n = a_E(n³)`.
The paper: "An ideal of norm `p^{3k}` with `p ≡ 1 (mod 3)` is `𝔭^i 𝔭̄^{3k−i}` for some
`0 ≤ i ≤ 3k`, which gives `3k+1` choices. An ideal of norm `q^{3k}` with `q ≡ 2 (mod 3)`
exists only if `3k` is even, that is, `k` is even, and is then unique."

* `aE_mul`: `a_E` is multiplicative on coprime arguments. Multiplication of ideals
  identifies the norm fibres at coprime `m, n` (`IdealNormFibers.mulEquiv`, which uses
  unique factorization of ideals and multiplicativity of `Ideal.absNorm`).
* `aE_split`: for `p ≡ 1 (mod 3)`, with `(p) = 𝔭𝔭̄`, the ideals of norm `p^m` are exactly
  `𝔭^i 𝔭̄^{m−i}`, `0 ≤ i ≤ m`, so there are `m+1` of them.
* `aE_inert_even`, `aE_inert_odd`: for `q ≡ 2 (mod 3)`, `(q)` is prime of norm `q²`, so
  an ideal of norm `q^m` exists only if `m` is even, and is then `(q)^{m/2}`.

These are stated for an arbitrary exponent `m`; the paper uses `m = 3k`.
-/

noncomputable section

namespace Cubic.Counting.PrimePowerIdealCount

open CubicTargets.Counting.ExactFormula (normIdeals aE)
open Cubic.PoissonSummation.CyclotomicIntegerUnits Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.BoxAsymptotic.AngularCorrectionProduct Cubic.BoxAsymptotic.HeckePrimeFactors
open Cubic.BoxAsymptotic.IdealNormFibers

/-! ### `a_E` is multiplicative -/

theorem aE_eq_card_fiber (m : ℕ) : aE m = Nat.card (Fiber m) := rfl

theorem aE_one : aE 1 = 1 := by
  have he : normIdeals 1 = {⊤} := by
    ext I
    simp [normIdeals, Ideal.absNorm_eq_one_iff]
  rw [aE, he, Nat.card_unique]

theorem aE_mul {m n : ℕ} (hmn : m.Coprime n) : aE (m * n) = aE m * aE n := by
  rw [aE_eq_card_fiber, aE_eq_card_fiber, aE_eq_card_fiber, ← Nat.card_prod,
    Nat.card_congr (mulEquiv hmn)]

/-! ### Divisors of prime powers -/

/-- An ideal of norm `N` divides `(N)`. -/
theorem dvd_span_norm (I : Ideal Integers) :
    I ∣ Ideal.span {((Ideal.absNorm I : ℕ) : Integers)} :=
  Ideal.dvd_iff_le.mpr (Ideal.span_singleton_absNorm_le I)

theorem natIdeal_pow (p m : ℕ) : natIdeal (p ^ m) = natIdeal p ^ m := by
  rw [natIdeal, natIdeal, Ideal.span_singleton_pow, Nat.cast_pow]

/-- A divisor of a power of a prime ideal is a power of it. -/
theorem eq_pow_of_dvd_pow {P J : Ideal Integers} (hP : Prime P) {m : ℕ} (h : J ∣ P ^ m) :
    ∃ i ≤ m, J = P ^ i := by
  obtain ⟨i, hi, ha⟩ := (dvd_prime_pow hP m).mp h
  exact ⟨i, hi, associated_iff_eq.mp ha⟩

/-! ### Split primes: `𝔭^i 𝔭̄^{m−i}` -/

section Split

variable (p : SplitPrimes)

theorem splitPrime_not_dvd_splitOther : ¬ splitPrime p ∣ splitOther p := by
  intro h
  have hle : splitOther p ≤ splitPrime p := Ideal.dvd_iff_le.mp h
  haveI : (splitOther p).IsPrime := (splitOther_mem p).1
  have hmax : (splitOther p).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (splitOther_prime p).ne_zero
  exact splitOther_ne p (hmax.eq_of_le (splitPrime_mem p).1.ne_top hle)

theorem splitOther_not_dvd_splitPrime : ¬ splitOther p ∣ splitPrime p := by
  intro h
  have hle : splitPrime p ≤ splitOther p := Ideal.dvd_iff_le.mp h
  haveI : (splitPrime p).IsPrime := (splitPrime_mem p).1
  have hmax : (splitPrime p).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (splitPrime_prime p).ne_zero
  exact splitOther_ne p (hmax.eq_of_le (splitOther_mem p).1.ne_top hle).symm

/-- `𝔭^i 𝔭̄^{m−i}`. -/
def splitIdeal (m : ℕ) (i : Fin (m + 1)) : Ideal Integers :=
  splitPrime p ^ (i : ℕ) * splitOther p ^ (m - i)

theorem norm_splitIdeal (m : ℕ) (i : Fin (m + 1)) :
    Ideal.absNorm (splitIdeal p m i) = (p.1 : ℕ) ^ m := by
  rw [splitIdeal, map_mul, map_pow, map_pow, norm_splitPrime, norm_splitOther, ← pow_add,
    Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.2)]

/-- `𝔭^i ∣ 𝔭^j 𝔭̄^k` forces `i ≤ j`. -/
theorem le_of_pow_dvd {i j k : ℕ}
    (h : splitPrime p ^ i ∣ splitPrime p ^ j * splitOther p ^ k) : i ≤ j := by
  have hrel : IsRelPrime (splitPrime p ^ i) (splitOther p ^ k) :=
    (((splitPrime_prime p).irreducible.isRelPrime_iff_not_dvd).mpr
      (splitPrime_not_dvd_splitOther p)).pow_left.pow_right
  exact (pow_dvd_pow_iff (splitPrime_prime p).ne_zero (splitPrime_prime p).not_unit).mp
    (hrel.dvd_of_dvd_mul_right h)

theorem splitIdeal_injective (m : ℕ) : Function.Injective (splitIdeal p m) := by
  intro i j he
  have hij : (i : ℕ) ≤ j := by
    apply le_of_pow_dvd p (k := m - j)
    have h := dvd_mul_right (splitPrime p ^ (i : ℕ)) (splitOther p ^ (m - i))
    rwa [← splitIdeal, he] at h
  have hji : (j : ℕ) ≤ i := by
    apply le_of_pow_dvd p (k := m - i)
    have h := dvd_mul_right (splitPrime p ^ (j : ℕ)) (splitOther p ^ (m - j))
    rwa [← splitIdeal, ← he] at h
  exact Fin.ext (le_antisymm hij hji)

/-- Every ideal of norm `p^m` is some `𝔭^i 𝔭̄^{m−i}`. -/
theorem exists_splitIdeal {m : ℕ} {I : Ideal Integers} (hI : Ideal.absNorm I = (p.1 : ℕ) ^ m) :
    ∃ i, splitIdeal p m i = I := by
  have hd : I ∣ splitPrime p ^ m * splitOther p ^ m := by
    have h := dvd_span_norm I
    rw [hI, ← natIdeal, natIdeal_pow, ← split_mul, mul_pow] at h
    exact h
  obtain ⟨J, K, hJ, hK, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨i, hi, rfl⟩ := eq_pow_of_dvd_pow (splitPrime_prime p) hJ
  obtain ⟨j, -, rfl⟩ := eq_pow_of_dvd_pow (splitOther_prime p) hK
  have hn : (p.1 : ℕ) ^ (i + j) = (p.1 : ℕ) ^ m := by
    rw [← hI, map_mul, map_pow, map_pow, norm_splitPrime, norm_splitOther, pow_add]
  have hij : i + j = m := Nat.pow_right_injective p.1.2.two_le hn
  refine ⟨⟨i, Nat.lt_succ_of_le hi⟩, ?_⟩
  simp only [splitIdeal]
  rw [show m - i = j by omega]

/-- `a_E(p^m) = m + 1` for `p ≡ 1 (mod 3)`. -/
theorem aE_split (m : ℕ) : aE ((p.1 : ℕ) ^ m) = m + 1 := by
  let f : Fin (m + 1) → normIdeals ((p.1 : ℕ) ^ m) :=
    fun i => ⟨splitIdeal p m i, norm_splitIdeal p m i⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j he => splitIdeal_injective p m (congrArg Subtype.val he), ?_⟩
    rintro ⟨I, hI⟩
    obtain ⟨i, hi⟩ := exists_splitIdeal p hI
    exact ⟨i, Subtype.ext hi⟩
  rw [aE, ← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]

end Split

/-! ### Inert primes: `(q)^{m/2}` -/

section Inert

variable (q : InertPrimes)

theorem norm_natIdeal : Ideal.absNorm (natIdeal (q.1 : ℕ)) = (q.1 : ℕ) ^ 2 :=
  norm_span_nat _

/-- An ideal of norm `q^m` is `(q)^i` with `2i = m`. -/
theorem eq_natIdeal_pow {m : ℕ} {I : Ideal Integers} (hI : Ideal.absNorm I = (q.1 : ℕ) ^ m) :
    ∃ i, 2 * i = m ∧ I = natIdeal (q.1 : ℕ) ^ i := by
  have hd : I ∣ natIdeal (q.1 : ℕ) ^ m := by
    have h := dvd_span_norm I
    rwa [hI, ← natIdeal, natIdeal_pow] at h
  obtain ⟨i, -, rfl⟩ := eq_pow_of_dvd_pow (inert_prime q) hd
  refine ⟨i, Nat.pow_right_injective q.1.2.two_le ?_, rfl⟩
  change (q.1 : ℕ) ^ (2 * i) = (q.1 : ℕ) ^ m
  rw [← hI, map_pow, norm_natIdeal, ← pow_mul]

/-- `a_E(q^{2k}) = 1` for `q ≡ 2 (mod 3)`. -/
theorem aE_inert_even (k : ℕ) : aE ((q.1 : ℕ) ^ (2 * k)) = 1 := by
  have he : normIdeals ((q.1 : ℕ) ^ (2 * k)) = {natIdeal (q.1 : ℕ) ^ k} := by
    ext I
    simp only [normIdeals, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hI
      obtain ⟨i, hi, rfl⟩ := eq_natIdeal_pow q hI
      rw [show i = k by omega]
    · rintro rfl
      rw [map_pow, norm_natIdeal, ← pow_mul]
  rw [aE, he, Nat.card_unique]

/-- `a_E(q^{2k+1}) = 0` for `q ≡ 2 (mod 3)`. -/
theorem aE_inert_odd (k : ℕ) : aE ((q.1 : ℕ) ^ (2 * k + 1)) = 0 := by
  have he : normIdeals ((q.1 : ℕ) ^ (2 * k + 1)) = ∅ := by
    ext I
    simp only [normIdeals, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hI
    obtain ⟨i, hi, -⟩ := eq_natIdeal_pow q hI
    omega
  rw [aE, he]; exact Nat.card_of_isEmpty

theorem aE_inert (m : ℕ) : aE ((q.1 : ℕ) ^ m) = if Even m then 1 else 0 := by
  split_ifs with hm
  · obtain ⟨k, rfl⟩ := hm
    simpa only [two_mul] using aE_inert_even q k
  · obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hm
    exact aE_inert_odd q k

end Inert

end Cubic.Counting.PrimePowerIdealCount
