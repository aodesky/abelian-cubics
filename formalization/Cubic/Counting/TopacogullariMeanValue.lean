import CubicTargets.Counting.TopacogullariSecondMoment
import Cubic.Counting.HeightCoefficientContinuation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The earlier critical-line mean value from Topacogullari

The preceding manuscript used the dyadic estimate
`∫_U^{2U} |ζ_E(1/2+it)|² dt ≪_η U^{1+η}` from [Topacogullari 2021, Theorem 1.5].
The current lemma uses Chandrasekharan–Narasimhan instead; this stronger source
and its valid dyadic consequence are retained as extra mathematics.
Take the difference of Theorem 1.5 at `2U` and `U` (with `ε = 1/4`). The quadratic main
term is `≪ U (log U)² ≪_η U^{1+η}`, and both error terms are `≪ U` because
`2/3 + 1/4 ≤ 1` and `1/2 + 7/64 + 1/4 ≤ 1`.
-/

noncomputable section

namespace Cubic.Counting.TopacogullariMeanValue

open Cubic.Counting.HeightCoefficientData intervalIntegral

/-- A polynomial of degree two is bounded by `S (1 + |x|)²`. -/
theorem abs_eval_le {P : Polynomial ℝ} (hP : P.natDegree = 2) (x : ℝ) :
    |P.eval x| ≤ (|P.coeff 0| + |P.coeff 1| + |P.coeff 2|) * (1 + |x|) ^ 2 := by
  rw [Polynomial.eval_eq_sum_range, hP]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
  have hx : 0 ≤ |x| := abs_nonneg x
  have h1 : |x| ≤ (1 + |x|) ^ 2 := by nlinarith
  have h2 : |x| ^ 2 ≤ (1 + |x|) ^ 2 := pow_le_pow_left₀ hx (by linarith) 2
  have h0 : (1 : ℝ) ≤ (1 + |x|) ^ 2 := by nlinarith
  calc |P.coeff 0 + P.coeff 1 * x + P.coeff 2 * x ^ 2|
      ≤ |P.coeff 0| + |P.coeff 1| * |x| + |P.coeff 2| * |x| ^ 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_pow]
        linarith [abs_add_le (P.coeff 0) (P.coeff 1 * x), abs_mul (P.coeff 1) x]
    _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg (P.coeff 0)),
          mul_le_mul_of_nonneg_left h1 (abs_nonneg (P.coeff 1)),
          mul_le_mul_of_nonneg_left h2 (abs_nonneg (P.coeff 2))]

theorem continuous_critical :
    Continuous fun t : ℝ => ‖zetaE ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 := by
  refine (continuous_iff_continuousAt.mpr fun t => ?_).norm.pow 2
  refine (HeightCoefficientContinuation.zetaE_differentiableAt ?_).continuousAt.comp
    (by fun_prop : Continuous fun t : ℝ => (1 / 2 : ℂ) + t * Complex.I).continuousAt
  intro h
  have := congrArg Complex.re h
  norm_num at this

/-- The mean value quoted in the paper follows from Theorem 1.5. -/
theorem meanValue (h : CubicTargets.Counting.TopacogullariSecondMoment.BlackBox) : MeanValue := by
  obtain ⟨P, hP, hT⟩ := h
  obtain ⟨C, hC⟩ := hT (1 / 4) (by norm_num)
  intro η hη
  set S : ℝ := |P.coeff 0| + |P.coeff 1| + |P.coeff 2| with hS
  set A : ℝ := |C| * ((3 : ℝ) ^ (2 / 3 : ℝ) + (3 : ℝ) ^ (5 / 4 - 3 / 2 * (7 / 64) : ℝ)) with hA
  have hS0 : 0 ≤ S := by positivity
  have hA0 : 0 ≤ A := by positivity
  refine ⟨S * (1 + 2 / η) ^ 2 * 2 ^ η + 3 * A, fun U hU => ?_⟩
  have hU0 : 0 < U := by linarith
  set f : ℝ → ℝ := fun t => ‖zetaE ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 with hf
  set g : ℝ → ℝ := fun t => P.eval (Real.log t) with hg
  have hfi : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => continuous_critical.intervalIntegrable a b
  have hgc : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable g MeasureTheory.volume a b :=
    fun a b ha hab => (P.continuous.comp_continuousOn
      (Real.continuousOn_log.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1])).intervalIntegrable_of_Icc hab
  -- the error term of Theorem 1.5 is at most `A T` for `T ≥ 1`
  have herr : ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (1 : ℝ)..T, f t) - ∫ t in (1 : ℝ)..T, g t| ≤ A * T := by
    intro T hT1
    refine (hC T hT1).trans ?_
    have e1 : T ^ (2 / 3 + 1 / 4 : ℝ) ≤ T := by
      calc T ^ (2 / 3 + 1 / 4 : ℝ) ≤ T ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := Real.rpow_one T
    have e2 : T ^ (1 / 2 + 7 / 64 + 1 / 4 : ℝ) ≤ T := by
      calc T ^ (1 / 2 + 7 / 64 + 1 / 4 : ℝ) ≤ T ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := Real.rpow_one T
    have p1 : 0 ≤ (3 : ℝ) ^ (2 / 3 : ℝ) := by positivity
    have p2 : 0 ≤ (3 : ℝ) ^ (5 / 4 - 3 / 2 * (7 / 64) : ℝ) := by positivity
    calc C * ((3 : ℝ) ^ (2 / 3 : ℝ) * T ^ (2 / 3 + 1 / 4 : ℝ) +
          (3 : ℝ) ^ (5 / 4 - 3 / 2 * (7 / 64) : ℝ) * T ^ (1 / 2 + 7 / 64 + 1 / 4 : ℝ))
        ≤ |C| * ((3 : ℝ) ^ (2 / 3 : ℝ) * T + (3 : ℝ) ^ (5 / 4 - 3 / 2 * (7 / 64) : ℝ) * T) := by
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          rw [abs_of_nonneg (by positivity)]
          gcongr
      _ = A * T := by rw [hA]; ring
  -- `∫_U^{2U}` as a difference of `∫_1^T`
  have hdiff : ∀ h : ℝ → ℝ, (∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable h MeasureTheory.volume a b) →
      ∫ t in U..2 * U, h t = (∫ t in (1 : ℝ)..2 * U, h t) - ∫ t in (1 : ℝ)..U, h t := by
    intro h hh
    rw [intervalIntegral.integral_interval_sub_left (hh 1 (2 * U) le_rfl (by linarith))
      (hh 1 U le_rfl (by linarith))]
  have hF := hdiff f (fun a b _ _ => hfi a b)
  have hG := hdiff g (fun a b ha hab => hgc a b (by linarith) hab)
  -- the main term: `|∫_U^{2U} P(log t)| ≤ U · S (1 + log 2U)²`
  have hlog2U : 0 ≤ Real.log (2 * U) := Real.log_nonneg (by linarith)
  have hmainpt : ∀ t ∈ Set.Icc U (2 * U), |g t| ≤ S * (1 + Real.log (2 * U)) ^ 2 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
    refine (abs_eval_le hP _).trans (mul_le_mul_of_nonneg_left ?_ hS0)
    rw [abs_of_nonneg hl]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.log_le_log ht0 ht.2]) 2
  have hmain : |∫ t in U..2 * U, g t| ≤ U * (S * (1 + Real.log (2 * U)) ^ 2) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := U) (b := 2 * U)
      (f := g) (C := S * (1 + Real.log (2 * U)) ^ 2) (fun t ht => by
        rw [Set.uIoc_of_le (by linarith)] at ht
        exact hmainpt t ⟨ht.1.le, ht.2⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * U - U)] at this
    linarith
  -- `(1 + log 2U)² ≤ (1 + 2/η)² 2^η U^η`
  have hlogη : (1 + Real.log (2 * U)) ^ 2 ≤ (1 + 2 / η) ^ 2 * 2 ^ η * U ^ η := by
    have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 2 * U) (by linarith : 0 < η / 2)
    have h2 : (1 : ℝ) ≤ (2 * U) ^ (η / 2) := Real.one_le_rpow (by linarith) (by linarith)
    have h3 : 1 + Real.log (2 * U) ≤ (1 + 2 / η) * (2 * U) ^ (η / 2) := by
      have : (2 * U) ^ (η / 2) / (η / 2) = 2 / η * (2 * U) ^ (η / 2) := by field_simp
      rw [this] at h1
      nlinarith
    have hsq : ((2 * U) ^ (η / 2)) ^ 2 = 2 ^ η * U ^ η := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
        Real.mul_rpow (by norm_num) hU0.le]
      congr 2 <;> push_cast <;> ring
    calc (1 + Real.log (2 * U)) ^ 2 ≤ ((1 + 2 / η) * (2 * U) ^ (η / 2)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) h3 2
      _ = (1 + 2 / η) ^ 2 * 2 ^ η * U ^ η := by rw [mul_pow, hsq]; ring
  have hUη : U ≤ U ^ (1 + η) := by
    calc U = U ^ (1 : ℝ) := (Real.rpow_one U).symm
      _ ≤ U ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hUpow : U * U ^ η = U ^ (1 + η) := by
    rw [Real.rpow_add hU0, Real.rpow_one]
  have e2U := herr (2 * U) (by linarith)
  have eU := herr U (by linarith)
  have hf' : ∫ t in U..2 * U, f t ≤ |∫ t in U..2 * U, g t| + 3 * A * U := by
    rw [hF, hG] at *
    have := abs_le.mp e2U
    have := abs_le.mp eU
    rw [hG] at hmain
    have : (∫ t in (1 : ℝ)..2 * U, g t) - ∫ t in (1 : ℝ)..U, g t ≤
        |(∫ t in (1 : ℝ)..2 * U, g t) - ∫ t in (1 : ℝ)..U, g t| := le_abs_self _
    rw [hG]
    nlinarith
  calc ∫ t in U..2 * U, ‖zetaE ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2
      = ∫ t in U..2 * U, f t := rfl
    _ ≤ U * (S * ((1 + 2 / η) ^ 2 * 2 ^ η * U ^ η)) + 3 * A * U := by
        refine hf'.trans ?_
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogη hS0) hU0.le
        linarith
    _ = S * (1 + 2 / η) ^ 2 * 2 ^ η * (U * U ^ η) + 3 * A * U := by ring
    _ ≤ S * (1 + 2 / η) ^ 2 * 2 ^ η * U ^ (1 + η) + 3 * A * U ^ (1 + η) := by
        rw [hUpow]
        have : 0 ≤ 3 * A := by positivity
        nlinarith
    _ = (S * (1 + 2 / η) ^ 2 * 2 ^ η + 3 * A) * U ^ (1 + η) := by ring

end Cubic.Counting.TopacogullariMeanValue
