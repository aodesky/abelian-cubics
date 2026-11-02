import Cubic.Counting.AsymptoticConstantsData
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The conductor weight `g` and its factorization `g = b * h`

Let `g(m) = 2^{ω(m)}` when `m` is squarefree with every prime factor `≡ 1 (mod 3)`, and
`g(m) = 0` otherwise. Its Dirichlet series is `∏_{p ≡ 1 (3)} (1 + 2p^{-s})`.

Let `χ` be the nontrivial character mod `3` and `b = χ * 1`, whose Dirichlet series is
`L(s,χ) ζ(s)`. We define the multiplicative function `h` by its prime-power values
* at `p ≡ 1 (3)`: `h(p²) = -3`, `h(p³) = 2`, the other `h(p^k)` (`k ≥ 1`) vanish,
  matching `(1 + 2x)(1 - x)² = 1 - 3x² + 2x³`;
* at `q ≡ 2 (3)`: `h(q²) = -1`, the other `h(q^k)` (`k ≥ 1`) vanish, matching
  `(1 - x)(1 + x) = 1 - x²`;
* at `3`: `h(3) = -1`, `h(3^k) = 0` for `k ≥ 2`, matching `1 - x`,

and prove `g = b * h` by comparing both multiplicative functions on prime powers.
-/

noncomputable section

namespace Cubic.BoxHeight.ConductorSum

open ArithmeticFunction Finset
open Cubic.Counting Cubic.PoissonSummation.FiniteEulerProduct

/-- `g(m) = 2^{ω(m)}` if `m` is squarefree and every prime factor of `m` is `≡ 1 (mod 3)`,
and `0` otherwise. (So `g 1 = 1`, `g 0 = 0` since 0 is not squarefree.) -/
def g (m : ℕ) : ℝ :=
  if Squarefree m ∧ ∀ p ∈ m.primeFactors, p % 3 = 1 then 2 ^ m.primeFactors.card else 0

/-- `A₀ = (2/3) · (π/(3√3)) · R(1)`, with
`R(1) = ∏_{q ≡ 2 (3)} (1 - q^{-2}) ∏_{p ≡ 1 (3)} (1 - 3p^{-2} + 2p^{-3})`. -/
def A₀ : ℝ := 2 / 3 * (Real.pi / (3 * Real.sqrt 3)) *
  (∏' q : InertPrimes, AsymptoticConstantsData.originalInertFactor q) *
  ∏' p : SplitPrimes, AsymptoticConstantsData.originalSplitFactor p

/-! ### The character `χ` mod 3 -/

/-- The nontrivial Dirichlet character mod `3`, as a real function on `ℕ`. -/
def chi (n : ℕ) : ℝ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

theorem mod_three_cases (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega

theorem chi_zero : chi 0 = 0 := by simp [chi]

theorem chi_one : chi 1 = 1 := by simp [chi]

theorem chi_mul (m n : ℕ) : chi (m * n) = chi m * chi n := by
  have h : (m * n) % 3 = (m % 3) * (n % 3) % 3 := Nat.mul_mod m n 3
  rcases mod_three_cases m with hm | hm | hm <;> rcases mod_three_cases n with hn | hn | hn <;>
    simp [chi, h, hm, hn]

theorem chi_pow (n i : ℕ) : chi (n ^ i) = chi n ^ i := by
  induction i with
  | zero => simp [chi_one]
  | succ i ih => rw [pow_succ, chi_mul, ih, pow_succ]

theorem abs_chi_le (n : ℕ) : |chi n| ≤ 1 := by
  unfold chi; split_ifs <;> norm_num

/-- `χ` as an arithmetic function. -/
def chiA : ArithmeticFunction ℝ := ⟨chi, chi_zero⟩

@[simp] theorem chiA_apply (n : ℕ) : chiA n = chi n := rfl

theorem isMultiplicative_chiA : chiA.IsMultiplicative :=
  ⟨chi_one, fun {m n} _ => chi_mul m n⟩

/-- `b = χ * 1`, with Dirichlet series `L(s,χ) ζ(s)`. -/
def b : ArithmeticFunction ℝ := chiA * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

theorem isMultiplicative_b : b.IsMultiplicative :=
  isMultiplicative_chiA.mul isMultiplicative_zeta.natCast

theorem b_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    b (p ^ k) = ∑ i ∈ range (k + 1), chi p ^ i := by
  rw [b, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  simp only [chiA_apply, chi_pow]

/-! ### The correction function `h` -/

/-- The prime-power values of `h`: `h(p^k) = hloc p k`. -/
def hloc (p k : ℕ) : ℝ :=
  if k = 0 then 1
  else if p % 3 = 0 then (if k = 1 then -1 else 0)
  else if p % 3 = 1 then (if k = 2 then -3 else if k = 3 then 2 else 0)
  else if k = 2 then -1 else 0

theorem hloc_zero (p : ℕ) : hloc p 0 = 1 := by simp [hloc]

theorem hloc_of_four_le (p : ℕ) {k : ℕ} (hk : 4 ≤ k) : hloc p k = 0 := by
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  have h2 : k ≠ 2 := by omega
  have h3 : k ≠ 3 := by omega
  simp [hloc, h0, h1, h2, h3]

/-- The underlying function of `h`. -/
def hfun (n : ℕ) : ℝ := if n = 0 then 0 else n.factorization.prod hloc

theorem hfun_one : hfun 1 = 1 := by simp [hfun]

theorem hfun_mul {m n : ℕ} (hmn : m.Coprime n) : hfun (m * n) = hfun m * hfun n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hfun]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hfun]
  have hd : Disjoint m.factorization.support n.factorization.support := by
    simpa only [Nat.support_factorization] using hmn.disjoint_primeFactors
  simp only [hfun, mul_ne_zero hm hn, hm, hn, if_false, Nat.factorization_mul hm hn,
    Finsupp.prod_add_index_of_disjoint hd]

/-- The correction function `h`, multiplicative with `h(p^k) = hloc p k`. -/
def h : ArithmeticFunction ℝ := ⟨hfun, by simp [hfun]⟩

@[simp] theorem h_apply (n : ℕ) : h n = hfun n := rfl

theorem isMultiplicative_h : h.IsMultiplicative :=
  ⟨hfun_one, fun {_ _} hmn => hfun_mul hmn⟩

theorem h_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : h (p ^ k) = hloc p k := by
  rw [h_apply, hfun, if_neg (pow_ne_zero k hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (hloc_zero p)]

/-! ### Multiplicativity of `g` -/

theorem g_zero : g 0 = 0 := by simp [g]

theorem g_one : g 1 = 1 := by simp [g]

theorem g_mul {m n : ℕ} (hmn : m.Coprime n) : g (m * n) = g m * g n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [g_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [g_zero]
  have hsq : Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
    rw [Nat.squarefree_mul_iff]
    exact ⟨fun h => h.2, fun h => ⟨hmn, h⟩⟩
  simp only [g, hmn.primeFactors_mul, card_union_of_disjoint hmn.disjoint_primeFactors,
    forall_mem_union, hsq, pow_add]
  by_cases h1 : Squarefree m ∧ ∀ p ∈ m.primeFactors, p % 3 = 1 <;>
    by_cases h2 : Squarefree n ∧ ∀ p ∈ n.primeFactors, p % 3 = 1
  · rw [if_pos ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩, if_pos h1, if_pos h2]
  · rw [if_neg (fun h => h2 ⟨h.1.2, h.2.2⟩), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 ⟨h.1.1, h.2.1⟩), if_neg h1, zero_mul]
  · rw [if_neg (fun h => h1 ⟨h.1.1, h.2.1⟩), if_neg h1, zero_mul]

/-- `g` as an arithmetic function. -/
def gA : ArithmeticFunction ℝ := ⟨g, g_zero⟩

@[simp] theorem gA_apply (n : ℕ) : gA n = g n := rfl

theorem isMultiplicative_gA : gA.IsMultiplicative :=
  ⟨g_one, fun {_ _} hmn => g_mul hmn⟩

theorem g_prime (p : ℕ) (hp : p.Prime) : g p = if p % 3 = 1 then 2 else 0 := by
  simp [g, hp.primeFactors, hp.squarefree]

theorem g_prime_pow_add_two (p : ℕ) (hp : p.Prime) (k : ℕ) : g (p ^ (k + 2)) = 0 := by
  have hns : ¬ Squarefree (p ^ (k + 2)) := by
    intro hs
    have := (Nat.squarefree_pow_iff hp.ne_one (by omega)).mp hs
    omega
  simp [g, hns]

/-! ### The factorization `g = b * h` -/

theorem mul_prime_pow (f₁ f₂ : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f₁ * f₂) (p ^ k) = ∑ i ∈ range (k + 1), f₁ (p ^ i) * f₂ (p ^ (k - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a c => f₁ a * f₂ c),
    Nat.sum_divisors_prime_pow hp]
  refine sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hp.pos]

/-- On `p^(m+3)`, only the terms with `h(p^j)`, `j ≤ 3`, survive. -/
theorem bh_prime_pow_add_three {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (b * h) (p ^ (m + 3)) = b (p ^ (m + 3)) + b (p ^ (m + 2)) * hloc p 1 +
      b (p ^ (m + 1)) * hloc p 2 + b (p ^ m) * hloc p 3 := by
  rw [mul_prime_pow b h hp, show m + 3 + 1 = m + 1 + 1 + 1 + 1 by ring, sum_range_succ,
    sum_range_succ, sum_range_succ, sum_range_succ]
  have hz : ∑ i ∈ range m, b (p ^ i) * h (p ^ (m + 3 - i)) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    rw [h_prime_pow hp, hloc_of_four_le p (by simp at hi; omega), mul_zero]
  rw [hz, zero_add]
  simp only [h_prime_pow hp, show m + 3 - (m + 1 + 1 + 1) = 0 by omega,
    show m + 3 - (m + 1 + 1) = 1 by omega, show m + 3 - (m + 1) = 2 by omega,
    show m + 3 - m = 3 by omega, hloc_zero]
  ring

theorem bh_prime_pow_zero {p : ℕ} (hp : p.Prime) : (b * h) (p ^ 0) = 1 := by
  rw [mul_prime_pow b h hp]
  simp only [zero_add, sum_range_one, pow_zero, Nat.sub_self, isMultiplicative_b.map_one,
    isMultiplicative_h.map_one, mul_one]

theorem bh_prime_pow_one {p : ℕ} (hp : p.Prime) :
    (b * h) (p ^ 1) = hloc p 1 + b (p ^ 1) := by
  rw [mul_prime_pow b h hp]
  simp only [sum_range_succ, sum_range_zero, Nat.sub_self, Nat.sub_zero, h_prime_pow hp,
    hloc_zero, pow_zero, isMultiplicative_b.map_one]
  ring

theorem bh_prime_pow_two {p : ℕ} (hp : p.Prime) :
    (b * h) (p ^ 2) = hloc p 2 + b (p ^ 1) * hloc p 1 + b (p ^ 2) := by
  rw [mul_prime_pow b h hp]
  simp only [sum_range_succ, sum_range_zero, h_prime_pow hp, hloc_zero, pow_zero,
    isMultiplicative_b.map_one, show 2 - 0 = 2 by rfl, show 2 - 1 = 1 by rfl,
    show 2 - 2 = 0 by rfl]
  ring

theorem g_eq_bh_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : gA (p ^ k) = (b * h) (p ^ k) := by
  have hb := b_prime_pow hp
  have hg1 : gA (p ^ 1) = if p % 3 = 1 then 2 else 0 := by rw [pow_one]; exact g_prime p hp
  have hg0 : gA (p ^ 0) = 1 := by simp [g_one]
  have hg2 : ∀ m, gA (p ^ (m + 2)) = 0 := g_prime_pow_add_two p hp
  rcases mod_three_cases p with h3 | h1 | h2
  · -- `p = 3`, `χ(p) = 0`
    have hc : chi p = 0 := by simp [chi, h3]
    have hb' : ∀ i : ℕ, b (p ^ i) = 1 := fun i => by
      rw [hb, hc, sum_range_succ']; simp
    match k with
    | 0 => rw [hg0, bh_prime_pow_zero hp]
    | 1 => rw [hg1, bh_prime_pow_one hp, hb']; simp [hloc, h3]
    | 2 => rw [hg2 0, bh_prime_pow_two hp, hb', hb']; simp [hloc, h3]
    | m + 3 =>
      rw [show m + 3 = m + 1 + 2 by ring, hg2, show m + 1 + 2 = m + 3 by ring,
        bh_prime_pow_add_three hp]
      simp [hb', hloc, h3]
  · -- `p ≡ 1`, `χ(p) = 1`, `b(p^i) = i + 1`
    have hc : chi p = 1 := by simp [chi, h1]
    have hb' : ∀ i : ℕ, b (p ^ i) = (i : ℝ) + 1 := fun i => by
      rw [hb, hc]; simp
    match k with
    | 0 => rw [hg0, bh_prime_pow_zero hp]
    | 1 => rw [hg1, bh_prime_pow_one hp, hb']; simp [hloc, h1]; norm_num
    | 2 => rw [hg2 0, bh_prime_pow_two hp, hb', hb']; simp [hloc, h1]; norm_num
    | m + 3 =>
      rw [show m + 3 = m + 1 + 2 by ring, hg2, show m + 1 + 2 = m + 3 by ring,
        bh_prime_pow_add_three hp]
      simp only [hb', hloc, h1]
      norm_num
      ring
  · -- `p ≡ 2`, `χ(p) = -1`, `b(p^(i+2)) = b(p^i)`
    have hc : chi p = -1 := by simp [chi, h2]
    have hb2 : ∀ i, b (p ^ (i + 2)) = b (p ^ i) := fun i => by
      rw [hb, hb, hc, show i + 2 + 1 = i + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
        pow_succ, pow_succ]
      ring
    have hb1 : b (p ^ 1) = 0 := by rw [hb, hc]; simp [sum_range_succ]
    match k with
    | 0 => rw [hg0, bh_prime_pow_zero hp]
    | 1 => rw [hg1, bh_prime_pow_one hp, hb1]; simp [hloc, h2]
    | 2 => rw [hg2 0, bh_prime_pow_two hp, hb1, hb2, pow_zero, isMultiplicative_b.map_one]
           simp [hloc, h2]
    | m + 3 =>
      rw [show m + 3 = m + 1 + 2 by ring, hg2, show m + 1 + 2 = m + 3 by ring,
        bh_prime_pow_add_three hp, show m + 3 = (m + 1) + 2 by ring, hb2 (m + 1)]
      simp [hloc, h2]

/-- The factorization `g = b * h` of arithmetic functions. -/
theorem gA_eq_mul : gA = b * h :=
  (IsMultiplicative.eq_iff_eq_on_prime_powers gA isMultiplicative_gA (b * h)
    (isMultiplicative_b.mul isMultiplicative_h)).mpr fun _ k hp => g_eq_bh_prime_pow hp k

end Cubic.BoxHeight.ConductorSum
