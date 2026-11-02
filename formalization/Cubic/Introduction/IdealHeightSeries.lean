import Cubic.Introduction.IdealParametrization
import Cubic.PoissonSummation.HeightCountingSeries
import Cubic.PoissonSummation.HeightCountingEulerProduct
import Cubic.PoissonSummation.HeightZetaLaurent
import Cubic.Counting.EisensteinIdealCount

/-! Identifying the actual height fibers by the primary-ideal bijection.
This gives the coefficient formula without a Poisson hypothesis. -/

noncomputable section

namespace Cubic.Introduction.IdealHeightSeries

open Cubic.PoissonSummation
open CyclotomicIntegerUnits
open AdelicHeightZetaData IntegralHeightIndex HeightCountingData HeightCountingSeries
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.Counting.EisensteinIdealCount
open EisensteinPointData

def originalIdealEquiv : IntegralRationalPoints ≃ CubeIdeals :=
  IntegralPointComparison.integralPointsEquiv.symm.trans IdealParametrization.pointIdealEquiv

theorem norm_index (P : IntegralRationalPoints) :
    Ideal.absNorm (originalIdealEquiv P).1 = index P ^ 3 := by
  have h := IdealParametrization.ideal_norm_height
    (IntegralPointComparison.integralPointsEquiv.symm P)
  have hH : EisensteinPointData.pointHeight
      (IntegralPointComparison.integralPointsEquiv.symm P) = Real.sqrt (index P) := by
    exact congrArg Complex.re (IntegralHeightNormalization.pointHeight_eq_sqrt_index P)
  rw [hH, show Real.sqrt (index P) ^ 6 = (index P : ℝ) ^ 3 by
    rw [show 6 = 2 * 3 by decide, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]] at h
  exact_mod_cast h

def fiberIdealEquiv (n : ℕ) :
    IndexFiber n ≃ {J : CubeIdeals // Ideal.absNorm J.1 = n ^ 3} :=
  originalIdealEquiv.subtypeEquiv (fun P => by
    rw [norm_index]
    constructor
    · rintro rfl
      rfl
    · intro h
      have h' : (index P : ℤ) ^ 3 = (n : ℤ) ^ 3 := by exact_mod_cast h
      exact_mod_cast (show Odd 3 by decide).pow_injective h')

def forgetFiberEquiv (n : ℕ) (hn : ¬ 3 ∣ n) :
    {J : CubeIdeals // Ideal.absNorm J.1 = n ^ 3} ≃
      {I : Ideal Integers // Ideal.absNorm I = n ^ 3} where
  toFun J := ⟨J.1.1, J.2⟩
  invFun I := ⟨⟨I.1, by
    rw [I.2]
    exact fun h => hn (Nat.prime_three.dvd_of_dvd_pow h), ⟨n, I.2⟩⟩, I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_eq_idealCount (n : ℕ) (hn : ¬ 3 ∣ n) :
    count n = idealCount (n ^ 3) := by
  rw [count_eq_index_card]
  exact Nat.card_congr ((fiberIdealEquiv n).trans (forgetFiberEquiv n hn))

theorem counts_eq_coefficient (n : ℕ) :
    (count n : ℤ) = HeightCountingCoefficients.coefficient n := by
  by_cases h3 : 3 ∣ n
  · simp [count_eq_zero_of_three_dvd n h3,
      HeightCountingCoefficients.coefficient_apply, h3]
  · have hn : 0 < n := Nat.pos_of_ne_zero (fun h => h3 (by simp [h]))
    have he := idealCount_cube 0 n hn h3
    simp only [pow_zero, one_mul] at he
    rw [count_eq_idealCount n h3]
    exact_mod_cast he

theorem continuation_agrees (s : ℂ) (hs : 2 < s.re) :
    HeightZetaLaurent.value s = heightZeta s 0 := by
  have hhalf : 1 < (s / 2).re := by simp; linarith
  have he : (fun n => (count n : ℂ)) =
      fun n => (HeightCountingCoefficients.coefficient n : ℂ) := by
    funext n
    exact_mod_cast counts_eq_coefficient n
  have habs := HeightCountingSeries.absolute s hs
  rw [he] at habs
  rw [HeightCountingSeries.heightZeta_eq_LSeries s hs, he,
    HeightCountingEulerProduct.euler_product_of_summable _ hhalf habs]
  exact HeightZetaContinuationFormula.continuation_eq_eulerExpression _ hhalf

end Cubic.Introduction.IdealHeightSeries
