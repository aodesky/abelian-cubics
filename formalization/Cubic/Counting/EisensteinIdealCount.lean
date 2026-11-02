import Cubic.PoissonSummation.QuadraticDedekindFactorization
import Cubic.PoissonSummation.DedekindZetaSeries
import Cubic.PoissonSummation.HeightCountingCoefficients
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Ideals of `ℤ[ζ]` of a given norm

Supporting arithmetic for `lemma:traceZeroCoefficients`. The number of ideals of `𝓞_E`,
`E = ℚ(ζ)`, of absolute norm `n ≥ 1` is `Σ_{d ∣ n} χ(d)`, where `χ` is the nontrivial
character mod `3`: the Dirichlet series of the ideal counts is `ζ_E(s) = ζ(s) L(s, χ)`
(`QuadraticDedekindFactorization.factorization`), and Dirichlet coefficients are determined
by the series. For `N = 3^e M` with `3 ∤ M`, the count at `N³` is the paper's
`d_M = Π_{p^k ∥ M, p ≡ 1} (3k+1) Π_{q^k ∥ M, q ≡ 2} 1_{2 ∣ k}`, which is `coefficient M`.
-/

noncomputable section

namespace Cubic.Counting.EisensteinIdealCount

open NumberField ArithmeticFunction Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.PoissonSummation Cubic.PoissonSummation.CyclotomicIntegerUnits

open scoped ArithmeticFunction.zeta
open QuadraticDirichletCharacter (character)

/-- The number of ideals of `𝓞_E` of absolute norm `n`. -/
def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal Integers // Ideal.absNorm I = n}

/-- `Σ_{d ∣ n} χ(d)`, as a Dirichlet convolution. -/
def divisorCharSum : ArithmeticFunction ℂ := ζ * toArithmeticFunction (character ·)

theorem divisorCharSum_apply (n : ℕ) : divisorCharSum n = ∑ d ∈ n.divisors, character d := by
  rw [divisorCharSum, coe_zeta_mul_apply]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp [toArithmeticFunction, Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)]

theorem divisorCharSum_multiplicative : divisorCharSum.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul character.isMultiplicative_toArithmeticFunction

theorem convolution_eq :
    LSeries.convolution (fun n => ((ζ n : ℕ) : ℂ)) (fun n => character n) =
      ⇑divisorCharSum := by
  have h : toArithmeticFunction (fun n => ((ζ n : ℕ) : ℂ)) = (ζ : ArithmeticFunction ℂ) := by
    ext m; simp [toArithmeticFunction, natCoe_apply]
  rw [LSeries.convolution, h]; rfl

theorem idealCount_eq (n : ℕ) (hn : n ≠ 0) : (idealCount n : ℂ) = divisorCharSum n := by
  have hf : LSeries.abscissaOfAbsConv (fun n => (idealCount n : ℂ)) < ⊤ := by
    have h := DedekindZetaSeries.coefficient_summable E 2 (by norm_num)
    simp only [DedekindZetaSeries.coefficient, Complex.ofReal_natCast] at h
    exact h.abscissaOfAbsConv_le.trans_lt (by simp)
  have hχ (s : ℂ) (hs : 1 < s.re) := character.LSeriesSummable_of_one_lt_re hs
  have hζ (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (fun n => ((ζ n : ℕ) : ℂ)) s :=
    LSeriesSummable_zeta_iff.mpr hs
  have hg : LSeries.abscissaOfAbsConv (fun n => divisorCharSum n) < ⊤ := by
    have h := (hζ 2 (by norm_num)).convolution (hχ 2 (by norm_num))
    rw [convolution_eq] at h
    exact h.abscissaOfAbsConv_le.trans_lt (by simp)
  have he : (fun x : ℝ => LSeries (fun n => (idealCount n : ℂ)) x) =ᶠ[Filter.atTop]
      fun x : ℝ => LSeries (fun n => divisorCharSum n) x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hs : 1 < (x : ℂ).re := by simpa using hx
    have hD := QuadraticDedekindFactorization.factorization (x : ℂ) hs
    rw [NumberField.dedekindZeta, DirichletCharacter.LFunction_eq_LSeries _ hs,
      ← LSeries_zeta_eq_riemannZeta hs] at hD
    rw [← LSeries_convolution' (hζ _ hs) (hχ _ hs), convolution_eq] at hD
    exact hD
  exact LSeries.eq_of_LSeries_eventually_eq hf hg he hn

/-! ### The value at `N³` -/

theorem character_prime_pow_sum (p m : ℕ) (hp : p.Prime) :
    divisorCharSum (p ^ m) = ∑ i ∈ Finset.range (m + 1), character p ^ i := by
  rw [divisorCharSum_apply, Nat.sum_divisors_prime_pow hp]
  simp [Nat.cast_pow, map_pow]

theorem sum_neg_one_pow (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), (-1 : ℂ) ^ i = 0 ∧
      ∑ i ∈ Finset.range (2 * m + 1), (-1 : ℂ) ^ i = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, ih.2, pow_succ,
        pow_mul]; simp
    · rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih.2, pow_succ, pow_succ, pow_mul]; simp
      rw [pow_succ, pow_mul]; simp

/-- `n ↦ Σ_{d ∣ n³} χ(d)` away from `3`. -/
def cubeCount : ArithmeticFunction ℂ where
  toFun n := if 3 ∣ n then 0 else divisorCharSum (n ^ 3)
  map_zero' := by simp

theorem cubeCount_multiplicative : cubeCount.IsMultiplicative := by
  refine ⟨by simp [cubeCount, divisorCharSum_multiplicative.map_one], fun {m n} hmn => ?_⟩
  simp only [cubeCount, ArithmeticFunction.coe_mk, Nat.prime_three.dvd_mul, mul_pow]
  by_cases hm : 3 ∣ m <;> by_cases hn : 3 ∣ n <;> simp only [hm, hn, or_true,
    or_false, if_true, if_false, zero_mul, mul_zero]
  exact divisorCharSum_multiplicative.map_mul_of_coprime (hmn.pow 3 3)

theorem cubeCount_eq_coefficient :
    cubeCount = (HeightCountingCoefficients.coefficient : ArithmeticFunction ℂ) := by
  refine (cubeCount_multiplicative.eq_iff_eq_on_prime_powers _ _
    HeightCountingCoefficients.multiplicative.intCast).mpr fun p k hp => ?_
  rw [ArithmeticFunction.intCoe_apply]
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [cubeCount, divisorCharSum_multiplicative.map_one,
      HeightCountingCoefficients.multiplicative.map_one]
  by_cases h3 : p = 3
  · subst h3
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [HeightCountingCoefficients.three_pow_succ]
    simp [cubeCount, pow_succ]
  have hp3 : ¬ 3 ∣ p ^ k := fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  simp only [cubeCount, ArithmeticFunction.coe_mk, hp3, if_false, ← pow_mul,
    character_prime_pow_sum p _ hp]
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have := Nat.mod_lt p (by norm_num : 3 > 0)
    have h0 : p % 3 ≠ 0 := fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h)).symm
    omega
  rcases hmod with h1 | h2
  · rw [QuadraticDirichletCharacter.character_of_mod, h1,
      HeightCountingCoefficients.split hp h1]
    simp; ring
  · have hc2 : character (@Nat.cast (ZMod 3) _ 2) = -1 := by
      rw [Nat.cast_ofNat]; exact QuadraticDirichletCharacter.character_two
    rw [QuadraticDirichletCharacter.character_of_mod, h2, hc2]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [HeightCountingCoefficients.inert_even hp h2,
        show 2 * j * 3 + 1 = 2 * (3 * j) + 1 by ring]
      exact_mod_cast (sum_neg_one_pow (3 * j)).2
    · rw [HeightCountingCoefficients.inert_odd hp h2,
        show (2 * j + 1) * 3 + 1 = 2 * (3 * j + 2) by ring]
      exact_mod_cast (sum_neg_one_pow (3 * j + 2)).1

theorem divisorCharSum_three_pow (k : ℕ) : divisorCharSum (3 ^ k) = 1 := by
  rw [character_prime_pow_sum 3 k Nat.prime_three, Finset.sum_range_succ']
  have h3 : character (3 : ZMod 3) = 0 := by
    rw [show (3 : ZMod 3) = 0 by decide]; simp
  simp [h3]

/-- The number of ideals of norm `N³`, `N = 3^e M`, `3 ∤ M`, is `coefficient M`. -/
theorem idealCount_cube (e M : ℕ) (hM : 0 < M) (h3 : ¬ 3 ∣ M) :
    (idealCount ((3 ^ e * M) ^ 3) : ℂ) = HeightCountingCoefficients.coefficient M := by
  have hcop : Nat.Coprime (3 ^ (e * 3)) (M ^ 3) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).pow _ _
  rw [idealCount_eq _ (by positivity), mul_pow, ← pow_mul,
    divisorCharSum_multiplicative.map_mul_of_coprime hcop, divisorCharSum_three_pow, one_mul]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f M) cubeCount_eq_coefficient
  simpa [cubeCount, h3, ArithmeticFunction.intCoe_apply] using h

end Cubic.Counting.EisensteinIdealCount
