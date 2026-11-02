import CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum
import Cubic.Counting.EisensteinIdealCount
import Cubic.PoissonSummation.HeightCountingEulerProduct
import Cubic.PoissonSummation.HeightZetaLaurent

/-! The actual ideal series at cube norms has the height-series Euler
factors, with its factor at three restored. This arithmetic comparison
uses no Poisson summation hypothesis. -/

noncomputable section

namespace Cubic.Introduction.CubeIdealEuler

open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.Counting.EisensteinIdealCount
open Cubic.PoissonSummation
open FiniteEulerProduct
open Filter
open scoped Topology

def allCoefficient : ArithmeticFunction ℂ where
  toFun n := divisorCharSum (n ^ 3)
  map_zero' := by simp

theorem coefficient_eq (n : ℕ) :
    CubeIdealSumData.coefficient E n = allCoefficient n := by
  by_cases hn : n = 0
  · simp [CubeIdealSumData.coefficient, allCoefficient, hn]
  · simp only [CubeIdealSumData.coefficient, hn, if_false]
    exact idealCount_eq (n ^ 3) (pow_ne_zero _ hn)

theorem multiplicative : allCoefficient.IsMultiplicative :=
  ⟨by simp [allCoefficient, divisorCharSum_multiplicative.map_one],
    fun {m n} hmn => by
      change divisorCharSum ((m * n) ^ 3) = _
      rw [mul_pow]
      exact divisorCharSum_multiplicative.map_mul_of_coprime (hmn.pow 3 3)⟩

theorem prime_power_away (p k : ℕ) (hp : p.Prime) (h3 : p ≠ 3) :
    allCoefficient (p ^ k) = HeightCountingCoefficients.coefficient (p ^ k) := by
  have h := idealCount_cube 0 (p ^ k) (pow_pos hp.pos _) (by
    intro h
    exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm)
  rw [← coefficient_eq]
  simpa [CubeIdealSumData.coefficient, hp.ne_zero, idealCount] using h

theorem three_power (k : ℕ) : allCoefficient (3 ^ k) = 1 := by
  change divisorCharSum ((3 ^ k) ^ 3) = 1
  rw [← pow_mul, divisorCharSum_three_pow]

def term (z : ℂ) (n : ℕ) : ℂ := LSeries.term allCoefficient z n

theorem term_eq (z : ℂ) (n : ℕ) :
    term z n = allCoefficient n * (n : ℂ) ^ (-z) :=
  LSeries.term_def₀ (by simp) z n

theorem term_one (z : ℂ) : term z 1 = 1 := by
  simp [term_eq, multiplicative.map_one]

theorem term_mul (z : ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    term z (m * n) = term z m * term z n := by
  simp only [term_eq, multiplicative.map_mul_of_coprime hmn,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

theorem away_term (p k : ℕ) (hp : p.Prime) (h3 : p ≠ 3) (z : ℂ) :
    term z (p ^ k) = HeightCountingEulerProduct.term z (p ^ k) := by
  rw [term_eq, HeightCountingEulerProduct.term_eq, prime_power_away p k hp h3]

theorem three_sum (z : ℂ) (hz : 1 < z.re) :
    HasSum (fun k => term z (3 ^ k)) (1 - (3 : ℂ) ^ (-z))⁻¹ := by
  convert hasSum_geometric_of_norm_lt_one
    ((Complex.norm_prime_cpow_le_one_half ⟨3, Nat.prime_three⟩ hz).trans_lt
      (by norm_num : (1 / 2 : ℝ) < 1)) using 1
  funext k
  rw [term_eq, three_power, one_mul, HeightCountingEulerProduct.nat_pow_cpow]

theorem euler_product
    (hKN : CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum.BlackBox)
    (z : ℂ) (hz : 1 < z.re) :
    LSeries (CubeIdealSumData.coefficient E) z =
      (1 - (3 : ℂ) ^ (-z))⁻¹ * HeightZetaContinuation.value z := by
  have hsum := (hKN E finrank_eq_two).absolute z hz
  rw [funext coefficient_eq] at hsum ⊢
  have hA : HasProd (fun p : Nat.Primes => ∑' k : ℕ, term z ((p : ℕ) ^ k))
      (LSeries allCoefficient z) :=
    EulerProduct.eulerProduct_hasProd (term_one z) (term_mul z)
      hsum.norm (by simp [term])
  have hi : HasProd (fun p : InertPrimes => ∑' k : ℕ, term z ((p.1 : ℕ) ^ k))
      (∏' p : InertPrimes, inertFactor p z) := by
    have he (p : InertPrimes) : (fun k => term z ((p.1 : ℕ) ^ k)) =
        fun k => HeightCountingEulerProduct.term z ((p.1 : ℕ) ^ k) := by
      funext k
      exact away_term _ _ p.1.2 (by intro h; have := p.2; simp [h] at this) z
    simpa only [he, (HeightCountingEulerProduct.inert_sum _ z hz).tsum_eq] using
      (convergent_inert z hz).hasProd
  have hs : HasProd (fun p : SplitPrimes => ∑' k : ℕ, term z ((p.1 : ℕ) ^ k))
      (∏' p : SplitPrimes, splitFactor p z) := by
    have he (p : SplitPrimes) : (fun k => term z ((p.1 : ℕ) ^ k)) =
        fun k => HeightCountingEulerProduct.term z ((p.1 : ℕ) ^ k) := by
      funext k
      exact away_term _ _ p.1.2 (by intro h; have := p.2; simp [h] at this) z
    simpa only [he, (HeightCountingEulerProduct.split_sum _ z hz).tsum_eq] using
      (convergent_split z hz).hasProd
  have hP := hasProd_primes_mod_three
    (f := fun p : Nat.Primes => ∑' k : ℕ, term z ((p : ℕ) ^ k)) hi hs
  have h := hA.unique hP
  rw [HeightZetaContinuationFormula.continuation_eq_eulerExpression z hz,
    HeightZetaEulerExtraction.eulerExpression_eq_unscaled_product z hz]
  simpa only [primeThree, (three_sum z hz).tsum_eq, mul_assoc] using h

/-- The holomorphic numerator of the restored ideal series at its double pole. -/
def regular (z : ℂ) : ℂ :=
  HeightZetaLaurent.numerator (2 * z) / 4 / (1 - (3 : ℂ) ^ (-z))

theorem regular_analytic : AnalyticAt ℂ regular 1 := by
  have hA : AnalyticAt ℂ (fun z : ℂ => HeightZetaLaurent.numerator (2 * z)) 1 :=
    (HeightZetaLaurent.numerator_analytic (2 * (1 : ℂ)) (by norm_num)).comp
      (f := fun z : ℂ => 2 * z) (by fun_prop)
  have hp : Differentiable ℂ (fun z : ℂ => (3 : ℂ) ^ (-z)) :=
    differentiable_id.neg.const_cpow (.inl (by norm_num))
  apply AnalyticAt.fun_div
  · exact hA.div_const
  · exact analyticAt_const.fun_sub (hp.analyticAt 1)
  · norm_num [Complex.cpow_neg]

theorem regular_agrees
    (hKN : CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum.BlackBox) :
    ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ),
      regular t = ((t : ℂ) - 1) ^ 2 * LSeries (CubeIdealSumData.coefficient E) t := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 1 < t at ht
  have ht' : 1 < (t : ℂ).re := ht
  have hne : 2 * (t : ℂ) ≠ 2 := by exact_mod_cast (by linarith : 2 * t ≠ 2)
  have htne : (t : ℂ) ≠ 1 := by exact_mod_cast ne_of_gt ht
  have h3 := Complex.one_sub_prime_cpow_ne_zero Nat.prime_three ht'
  have he := HeightZetaLaurent.value_eq_quotient (2 * (t : ℂ)) hne
  simp only [HeightZetaLaurent.value, mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)] at he
  rw [euler_product hKN _ ht', he, regular]
  field_simp [h3, sub_ne_zero.mpr hne, sub_ne_zero.mpr htne]
  <;> ring

theorem estimate
    (hKN : CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum.BlackBox) :
    (fun X : ℝ => CubeIdealSumData.summatory E X -
      (regular 1 * X * Real.log X + (deriv regular 1 - regular 1) * X))
      =O[atTop] CubeIdealSumData.error :=
  (hKN E finrank_eq_two).estimate regular regular_analytic (regular_agrees hKN)

end Cubic.Introduction.CubeIdealEuler
