import Cubic.BoxHeight.ConductorSumData
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absolute convergence and the Euler product of `Σ h(d)/d`

The correction function `h` from `ConductorSumData` is supported on the numbers
`3^e · m` with `e ≤ 1` and `m` powerful, so `Σ |h(d)| d^{-σ}` converges for `σ > 1/2`.
We prove this at `σ = 3/4` for the nonnegative multiplicative function
`F(d) = |h(d)| d^{-3/4}`: the partial sums of `F` are bounded by its partial Euler products
`∏_{p < N} (1 + a_p) ≤ exp(Σ_p a_p)`, with `a_p = F(p) + F(p²) + F(p³) ≪ p^{-3/2}` away from `3`.
Since `log d ≤ 4 d^{1/4}`, both `Σ |h(d)|/d` and `Σ |h(d)| log d / d` converge.

The Euler product then evaluates `Σ h(d)/d` as the product of the local factors `2/3` at `3`,
`1 - q^{-2}` at `q ≡ 2 (3)` and `1 - 3p^{-2} + 2p^{-3}` at `p ≡ 1 (3)`.
-/

noncomputable section

namespace Cubic.BoxHeight.ConductorSum

open ArithmeticFunction Finset
open Cubic.Counting Cubic.PoissonSummation.FiniteEulerProduct

/-! ### A summability criterion for nonnegative multiplicative functions -/

/-- A nonnegative multiplicative function vanishing on `p^k`, `k ≥ 4`, is summable as soon as
`Σ_p (F(p) + F(p²) + F(p³))` converges. -/
theorem summable_of_multiplicative (F : ℕ → ℝ) (h1 : F 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n) (h0 : F 0 = 0)
    (hnn : ∀ n, 0 ≤ F n) (hsupp : ∀ p k, p.Prime → 4 ≤ k → F (p ^ k) = 0)
    (hs : Summable (fun p : ℕ => if p.Prime then F p + F (p ^ 2) + F (p ^ 3) else 0)) :
    Summable F := by
  set a : ℕ → ℝ := fun p => if p.Prime then F p + F (p ^ 2) + F (p ^ 3) else 0 with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => by
    simp only [ha]; split_ifs <;> [exact add_nonneg (add_nonneg (hnn _) (hnn _)) (hnn _);
      exact le_rfl]
  have hloc : ∀ {p : ℕ}, p.Prime → HasSum (fun n => F (p ^ n)) (1 + a p) := by
    intro p hp
    have h : HasSum (fun n => F (p ^ n)) (∑ n ∈ range 4, F (p ^ n)) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => hsupp p n hp (by simpa using hn))
    convert h using 1
    simp [ha, hp, sum_range_succ, h1]
    ring
  have hnorm : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖F (p ^ n)‖) := by
    intro p hp
    simpa only [Real.norm_of_nonneg (hnn _)] using (hloc hp).summable
  refine summable_of_sum_range_le hnn (c := Real.exp (∑' p, a p)) fun N => ?_
  obtain ⟨-, hE⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 hmul hnorm N
  have hI := (hasSum_subtype_iff_indicator (s := N.smoothNumbers)).mp hE
  have hle := sum_le_hasSum (range N) (fun i _ => Set.indicator_nonneg (fun j _ => hnn j) i) hI
  have hsum_eq : ∑ i ∈ range N, N.smoothNumbers.indicator F i = ∑ i ∈ range N, F i := by
    refine sum_congr rfl fun i hi => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [h0]
    · exact Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hi0 (by simpa using hi)) F
  rw [hsum_eq] at hle
  refine hle.trans ?_
  have hprod : ∏ p ∈ N.primesBelow, ∑' n : ℕ, F (p ^ n) ≤ ∏ p ∈ N.primesBelow, Real.exp (a p) := by
    refine prod_le_prod (fun p hp => tsum_nonneg fun n => hnn _) fun p hp => ?_
    rw [(hloc (Nat.prime_of_mem_primesBelow hp)).tsum_eq, add_comm]
    exact Real.add_one_le_exp _
  refine hprod.trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  exact hs.sum_le_tsum _ (fun p _ => ha0 p)

/-! ### The function `F(d) = |h(d)| d^{-3/4}` -/

/-- `|h(d)| d^{-3/4}`. -/
def hWeight (d : ℕ) : ℝ := |h d| / (d : ℝ) ^ (3 / 4 : ℝ)

theorem hWeight_nonneg (d : ℕ) : 0 ≤ hWeight d := by unfold hWeight; positivity

theorem abs_hloc_one (p : ℕ) : |hloc p 1| ≤ if p % 3 = 0 then 1 else 0 := by
  rcases mod_three_cases p with h | h | h <;> simp [hloc, h]

theorem abs_hloc_two (p : ℕ) : |hloc p 2| ≤ 3 := by
  rcases mod_three_cases p with h | h | h <;> norm_num [hloc, h]

theorem abs_hloc_three (p : ℕ) : |hloc p 3| ≤ 2 := by
  rcases mod_three_cases p with h | h | h <;> norm_num [hloc, h]

theorem natCast_pow_rpow (p k : ℕ) (r : ℝ) :
    (((p ^ k : ℕ) : ℝ)) ^ r = (p : ℝ) ^ ((k : ℝ) * r) := by
  rw [Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast, Nat.cast_pow]

theorem hWeight_summable : Summable hWeight := by
  have hmajor : Summable (fun p : ℕ =>
      (if p = 3 then (1 : ℝ) else 0) + 5 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    ((hasSum_ite_eq 3 (1 : ℝ)).summable).add
      ((Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 5)
  refine summable_of_multiplicative hWeight ?_ ?_ ?_ hWeight_nonneg ?_ ?_
  · simp [hWeight, isMultiplicative_h.map_one]
  · intro m n hmn
    simp only [hWeight, isMultiplicative_h.map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  · simp [hWeight]
  · intro p k hp hk
    simp [hWeight, h_prime_pow hp, hloc_of_four_le p hk]
  · refine hmajor.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    · split_ifs
      · exact add_nonneg (add_nonneg (hWeight_nonneg _) (hWeight_nonneg _)) (hWeight_nonneg _)
      · exact le_rfl
    by_cases hp : p.Prime
    swap
    · rw [if_neg hp]
      exact add_nonneg (by split_ifs <;> norm_num) (by positivity)
    rw [if_pos hp]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hpos : (0 : ℝ) < p := by linarith
    -- the three prime-power terms
    have e1 : hWeight p ≤ if p = 3 then 1 else 0 := by
      unfold hWeight
      rw [← pow_one p, h_prime_pow hp, pow_one]
      by_cases h3 : p = 3
      · subst h3
        rw [if_pos rfl, div_le_one (Real.rpow_pos_of_pos hpos _)]
        have : |hloc 3 1| = 1 := by norm_num [hloc]
        rw [this]
        exact Real.one_le_rpow hp1 (by norm_num)
      · have h0 : p % 3 ≠ 0 := by
          intro h0
          exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
            (Nat.dvd_of_mod_eq_zero h0)).symm
        rw [if_neg h3]
        have : hloc p 1 = 0 := by simp [hloc, h0]
        simp [this]
    have hpow32 : (0 : ℝ) < (p : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
    have e2 : hWeight (p ^ 2) ≤ 3 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      unfold hWeight
      rw [h_prime_pow hp, natCast_pow_rpow, show ((2 : ℕ) : ℝ) * (3 / 4) = 3 / 2 by norm_num,
        div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (abs_hloc_two p) (by positivity)
    have e3 : hWeight (p ^ 3) ≤ 2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      unfold hWeight
      rw [h_prime_pow hp, natCast_pow_rpow, show ((3 : ℕ) : ℝ) * (3 / 4) = 9 / 4 by norm_num,
        div_eq_mul_inv]
      refine mul_le_mul (abs_hloc_three p) ?_ (by positivity) (by norm_num)
      exact inv_anti₀ hpow32 (Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num))
    linarith

theorem rpow_three_quarters_le (d : ℕ) : (d : ℝ) ^ (3 / 4 : ℝ) ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    simpa using Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (3 / 4 : ℝ) ≤ 1)

/-- `Σ |h(d)|/d < ∞`. -/
theorem summable_abs_h_div : Summable (fun d : ℕ => |h d| / d) := by
  refine hWeight_summable.of_nonneg_of_le (fun d => by positivity) fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [hWeight]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.rpow_pos_of_pos hd' _)
    (rpow_three_quarters_le d)

/-- `Σ |h(d)| log d / d < ∞`. -/
theorem summable_abs_h_log : Summable (fun d : ℕ => |h d| * Real.log d / d) := by
  refine (hWeight_summable.mul_left 4).of_nonneg_of_le (fun d => ?_) fun d => ?_
  · have := Real.log_natCast_nonneg d
    positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [hWeight]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log d ≤ (d : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div hd'.le (by norm_num)
  have hsplit : (d : ℝ) = (d : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hd']; norm_num
  have h34 : (0 : ℝ) < (d : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hd' _
  have h14 : (0 : ℝ) < (d : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hd' _
  have hlog' : Real.log d ≤ 4 * (d : ℝ) ^ (1 / 4 : ℝ) := by linarith [hlog]
  have hq : (d : ℝ) ^ (1 / 4 : ℝ) / d = 1 / (d : ℝ) ^ (3 / 4 : ℝ) := by
    rw [div_eq_div_iff hd'.ne' h34.ne', one_mul, ← hsplit]
  calc |h d| * Real.log d / d ≤ |h d| * (4 * (d : ℝ) ^ (1 / 4 : ℝ)) / d := by
        gcongr
    _ = 4 * |h d| * ((d : ℝ) ^ (1 / 4 : ℝ) / d) := by ring
    _ = 4 * hWeight d := by rw [hq, hWeight]; ring

/-! ### The Euler product of `Σ h(d)/d` -/

/-- `h(d)/d`. -/
def hDiv (d : ℕ) : ℝ := h d / d

theorem hDiv_one : hDiv 1 = 1 := by simp [hDiv, isMultiplicative_h.map_one]

theorem hDiv_mul {m n : ℕ} (hmn : m.Coprime n) : hDiv (m * n) = hDiv m * hDiv n := by
  simp only [hDiv, isMultiplicative_h.map_mul_of_coprime hmn, Nat.cast_mul]
  rw [mul_div_mul_comm]

theorem summable_norm_hDiv : Summable (fun d => ‖hDiv d‖) := by
  simpa [hDiv, abs_div] using summable_abs_h_div

theorem hDiv_local (p : ℕ) (hp : p.Prime) :
    ∑' e : ℕ, hDiv (p ^ e) = 1 + hloc p 1 / p + hloc p 2 / p ^ 2 + hloc p 3 / p ^ 3 := by
  rw [tsum_eq_sum (s := range 4) (fun e he => by
    simp [hDiv, h_prime_pow hp, hloc_of_four_le p (by simpa using he)])]
  simp [hDiv, h_prime_pow hp, sum_range_succ, hloc_zero]

private abbrev PrimeCases := Unit ⊕ (InertPrimes ⊕ SplitPrimes)

private def primeOfCase : PrimeCases → Nat.Primes :=
  Sum.elim (fun _ => primeThree) (Sum.elim Subtype.val Subtype.val)

private theorem primeOfCase_injective : Function.Injective primeOfCase := by
  rintro (u | (q | p)) (v | (r | s)) h
  · cases u; cases v; rfl
  · have hr := r.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, primeThree, hr] at he
  · have hs := s.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, primeThree, hs] at he
  · have hq := q.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, primeThree, hq] at he
  · exact congrArg (fun a => Sum.inr (Sum.inl a)) (Subtype.ext h)
  · have hq := q.property
    have hs := s.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, hq, hs] at he
  · have hp := p.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, primeThree, hp] at he
  · have hp := p.property
    have hr := r.property
    have he := congrArg (fun n : Nat.Primes => (n : ℕ) % 3) h
    simp [primeOfCase, hp, hr] at he
  · exact congrArg (fun a => Sum.inr (Sum.inr a)) (Subtype.ext h)

private theorem primeOfCase_surjective : Function.Surjective primeOfCase := by
  intro p
  by_cases h3 : p = primeThree
  · exact ⟨Sum.inl (), h3.symm⟩
  have h0 : (p : ℕ) % 3 ≠ 0 := by
    intro h
    have he : (p : ℕ) = 3 := (p.prop.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h)
    exact h3 (Subtype.ext he)
  by_cases h2 : (p : ℕ) % 3 = 2
  · exact ⟨Sum.inr (Sum.inl ⟨p, h2⟩), rfl⟩
  · have h1 : (p : ℕ) % 3 = 1 := by omega
    exact ⟨Sum.inr (Sum.inr ⟨p, h1⟩), rfl⟩

private def primeCasesEquiv : PrimeCases ≃ Nat.Primes :=
  Equiv.ofBijective primeOfCase ⟨primeOfCase_injective, primeOfCase_surjective⟩

/-- A real product over all primes, assembled from the prime `3` and the two residue classes. -/
theorem hasProd_primes_mod_three_real {f : Nat.Primes → ℝ} {a c : ℝ}
    (hi : HasProd (fun p : InertPrimes => f p.1) a)
    (hs : HasProd (fun p : SplitPrimes => f p.1) c) :
    HasProd f (f primeThree * a * c) := by
  have h3 : HasProd (fun _ : Unit => f primeThree) (f primeThree) := by simp
  have hrest : HasProd (fun x : InertPrimes ⊕ SplitPrimes =>
      f (Sum.elim Subtype.val Subtype.val x)) (a * c) := HasProd.sum hi hs
  have hall : HasProd (fun x : PrimeCases => f (primeOfCase x))
      (f primeThree * (a * c)) := HasProd.sum h3 hrest
  simpa only [mul_assoc] using (primeCasesEquiv.hasProd_iff (f := f)).mp hall

theorem inert_deviation_summable :
    Summable (fun q : InertPrimes => ‖AsymptoticConstantsData.originalInertFactor q - 1‖) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hinj : Function.Injective (fun q : InertPrimes => ((q.1 : Nat.Primes) : ℕ)) :=
    fun a c hac => Subtype.ext (Subtype.ext hac)
  refine (hs.comp_injective hinj).congr fun q => ?_
  simp [AsymptoticConstantsData.originalInertFactor]

theorem split_deviation_summable :
    Summable (fun p : SplitPrimes => ‖AsymptoticConstantsData.originalSplitFactor p - 1‖) := by
  have hs : Summable (fun n : ℕ => 5 * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 5
  have hinj : Function.Injective (fun p : SplitPrimes => ((p.1 : Nat.Primes) : ℕ)) :=
    fun a c hac => Subtype.ext (Subtype.ext hac)
  refine (hs.comp_injective hinj).of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
  have hp1 : (1 : ℝ) ≤ ((p.1 : Nat.Primes) : ℕ) := by exact_mod_cast p.1.2.one_lt.le
  set x : ℝ := (((p.1 : Nat.Primes) : ℕ) : ℝ)
  simp only [Function.comp_apply, AsymptoticConstantsData.originalSplitFactor]
  change ‖1 - 3 / x ^ 2 + 2 / x ^ 3 - 1‖ ≤ 5 * (1 / x ^ 2)
  rw [Real.norm_eq_abs, abs_le]
  have hx2 : 0 < x ^ 2 := by positivity
  have h3 : 2 / x ^ 3 ≤ 2 / x ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) hx2
    nlinarith
  have h3' : 0 ≤ 2 / x ^ 3 := by positivity
  constructor
  · have : 3 / x ^ 2 = 3 * (1 / x ^ 2) := by ring
    have : 0 ≤ 1 / x ^ 2 := by positivity
    linarith
  · have : 2 / x ^ 2 = 2 * (1 / x ^ 2) := by ring
    have : 0 ≤ 1 / x ^ 2 := by positivity
    have : 0 ≤ 3 / x ^ 2 := by positivity
    linarith

/-- `Σ h(d)/d = (2/3) ∏_{q ≡ 2} (1 - q^{-2}) ∏_{p ≡ 1} (1 - 3p^{-2} + 2p^{-3})`. -/
theorem tsum_hDiv : ∑' d : ℕ, hDiv d = 2 / 3 *
    (∏' q : InertPrimes, AsymptoticConstantsData.originalInertFactor q) *
    ∏' p : SplitPrimes, AsymptoticConstantsData.originalSplitFactor p := by
  have hE := EulerProduct.eulerProduct_hasProd hDiv_one (fun {_ _} h => hDiv_mul h)
    summable_norm_hDiv (by simp [hDiv])
  have hmi : Multipliable (fun q : InertPrimes => AsymptoticConstantsData.originalInertFactor q) := by
    simpa using multipliable_one_add_of_summable inert_deviation_summable
  have hms : Multipliable (fun p : SplitPrimes => AsymptoticConstantsData.originalSplitFactor p) := by
    simpa using multipliable_one_add_of_summable split_deviation_summable
  have hi : HasProd (fun q : InertPrimes => ∑' e : ℕ, hDiv (((q.1 : Nat.Primes) : ℕ) ^ e))
      (∏' q : InertPrimes, AsymptoticConstantsData.originalInertFactor q) := by
    convert hmi.hasProd using 1
    funext q
    have hq := q.2
    rw [hDiv_local _ q.1.2, AsymptoticConstantsData.originalInertFactor]
    have h0 : ((q.1 : Nat.Primes) : ℕ) % 3 ≠ 0 := by omega
    have h1 : ((q.1 : Nat.Primes) : ℕ) % 3 ≠ 1 := by omega
    simp [hloc, h0, h1]
    ring
  have hs : HasProd (fun p : SplitPrimes => ∑' e : ℕ, hDiv (((p.1 : Nat.Primes) : ℕ) ^ e))
      (∏' p : SplitPrimes, AsymptoticConstantsData.originalSplitFactor p) := by
    convert hms.hasProd using 1
    funext p
    have hp := p.2
    rw [hDiv_local _ p.1.2, AsymptoticConstantsData.originalSplitFactor]
    have h0 : ((p.1 : Nat.Primes) : ℕ) % 3 ≠ 0 := by omega
    simp [hloc, hp]
    ring
  have hP := hasProd_primes_mod_three_real
    (f := fun p : Nat.Primes => ∑' e : ℕ, hDiv ((p : ℕ) ^ e)) hi hs
  have h3 : (∑' e : ℕ, hDiv (((primeThree : Nat.Primes) : ℕ) ^ e)) = 2 / 3 := by
    rw [show ((primeThree : Nat.Primes) : ℕ) = 3 from rfl, hDiv_local 3 Nat.prime_three]
    norm_num [hloc]
  rw [hE.unique hP]
  dsimp only
  rw [h3]

end Cubic.BoxHeight.ConductorSum
