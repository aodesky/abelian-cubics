import Cubic.Counting.CountPolynomialNormalization
import Cubic.Counting.AsymptoticPolynomialCount
import CubicTargets.Counting.GeneralMonic

/-!
# Proof of `eqn:A1asymptotic`

The paper: "Theorem `thm:asymptoticPolynomialCount`, after the change of variables
`X = 1 + 3H²`, gives" `eqn:A1asymptotic`. By `lemma:rootVsToric` (as used in the proof of
that theorem, `AsymptoticPolynomialCount.bounded_eq`), for `X ≥ 1` the polynomials counted by
`A₁(X)` are those of root height at most `H = √((X-1)/3)`. With `H² = (X-1)/3`,
`C H² log H + (C log √3 + D - π/(3√3)) H² = (C/6)(X-1) log(X-1) + (D/3 - π/(9√3))(X-1)`,
which differs from `(C/6) X log X + (D/3 - π/(9√3)) X` by `O(log X)`, and
`H^{1+ε} ≤ X^{1/2+ε}`.
-/

noncomputable section

namespace Cubic.Counting.A1Asymptotic

open Cubic.Counting.GeneralMonicData Cubic.Counting.AsymptoticConstantsData
open Cubic.Counting.PolynomialCountData (boundedPolynomials polynomialCount)
open CubicTargets.Counting.WeightedPolynomialCount (countSet toricHeight)

/-- For `X ≥ 0`, `A₁(X)` counts the polynomials of toric height at most `√X`. -/
theorem traceOneSet_eq (X : ℝ) (hX : 0 ≤ X) : traceOneSet X = countSet (Real.sqrt X) := by
  ext f
  simp only [traceOneSet, countSet, toricHeight, Set.mem_setOf_eq]
  push_cast
  rw [Real.sqrt_le_sqrt_iff hX]

theorem traceOneSet_finite (X : ℝ) : (traceOneSet X).Finite := by
  have hsub : traceOneSet X ⊆ traceOneSet (max X 1) := fun f hf =>
    ⟨hf.1, hf.2.trans (le_max_left _ _)⟩
  refine Set.Finite.subset ?_ hsub
  rw [traceOneSet_eq _ (le_trans zero_le_one (le_max_right _ _))]
  exact (Cubic.Counting.WeightedCount.exact_count _
    (Real.one_le_sqrt.mpr (le_max_right _ _))).1

/-- For `X ≥ 1`, `A₁(X)` counts the polynomials of root height at most `√((X-1)/3)`. -/
theorem traceOneSet_eq_bounded {X : ℝ} (hX : 1 ≤ X) :
    traceOneSet X = boundedPolynomials (Real.sqrt ((X - 1) / 3)) := by
  rw [AsymptoticPolynomialCount.bounded_eq _ (Real.sqrt_nonneg _),
    Real.sq_sqrt (by linarith), traceOneSet_eq X (by linarith)]
  congr 2; ring

/-- `0 ≤ X log X - (X-1) log(X-1) - log X ≤ 1` for `X ≥ 2`. -/
theorem xlogx_diff {X : ℝ} (hX : 2 ≤ X) :
    0 ≤ X * Real.log X - (X - 1) * Real.log (X - 1) - Real.log X ∧
      X * Real.log X - (X - 1) * Real.log (X - 1) - Real.log X ≤ 1 := by
  have e : X * Real.log X - (X - 1) * Real.log (X - 1) - Real.log X =
      (X - 1) * (Real.log X - Real.log (X - 1)) := by ring
  rw [e]
  have hlog : Real.log (X - 1) ≤ Real.log X := Real.log_le_log (by linarith) (by linarith)
  refine ⟨mul_nonneg (by linarith) (by linarith), ?_⟩
  rw [← Real.log_div (by linarith) (by linarith)]
  have := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < X) (by linarith : (0 : ℝ) < X - 1))
  calc (X - 1) * Real.log (X / (X - 1)) ≤ (X - 1) * (X / (X - 1) - 1) :=
        mul_le_mul_of_nonneg_left this (by linarith)
    _ = 1 := by have hne : X - 1 ≠ 0 := by linarith
                field_simp; ring

theorem coefficient_estimate
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.GeneralMonic.A1Coefficients := by
  refine ⟨traceOneSet_finite, ?_⟩
  obtain ⟨Z, γ, C, D, -, hC, hA⟩ :=
    AsymptoticPolynomialCount.«thm:asymptoticPolynomialCount» hPoisson hCN
  have hCc : C = Cconst := hC.original_leading
  have hDc : D = Dconst := by
    have h := hC.original_secondary
    rw [div_eq_iff hC.positive.ne'] at h
    rw [h, Dconst, hCc, Cconst, mul_comm]
  intro ε hε
  obtain ⟨c, hc⟩ := (hA.estimate ε hε).bound
  obtain ⟨H₀, hH₀⟩ := Filter.eventually_atTop.mp hc
  set s := 1 / 2 + ε
  set Q := D / 3 - Real.pi / (9 * Real.sqrt 3) with hQdef
  refine ⟨|c| + C / 6 * (1 / s) + C / 6 + |Q|, max 2 (1 + 3 * H₀ ^ 2), fun X hX => ?_⟩
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hX0 : 0 < X := by linarith
  set H := Real.sqrt ((X - 1) / 3) with hHdef
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  have hH2 : H ^ 2 = (X - 1) / 3 := Real.sq_sqrt (by linarith)
  have hHH₀ : H₀ ≤ H := by
    rcases le_or_gt H₀ 0 with h | h
    · linarith
    · rw [hHdef, Real.le_sqrt' h]
      have := le_trans (le_max_right _ _) hX
      linarith
  have h := hH₀ H hHH₀
  have hHpow : 0 ≤ H ^ (1 + ε) := Real.rpow_nonneg hH0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hHpow] at h
  have hA : (A₁ X : ℝ) = polynomialCount H := by
    rw [A₁, traceOneSet_eq_bounded (by linarith)]; rfl
  -- the main terms
  have hlogH : Real.log H = (Real.log (X - 1) - Real.log 3) / 2 := by
    rw [hHdef, Real.log_sqrt (div_nonneg (by linarith) (by norm_num)), Real.log_div (by linarith) (by norm_num)]
  have hlog3 : Real.log (Real.sqrt 3) = Real.log 3 / 2 := Real.log_sqrt (by norm_num)
  have hmain : C * H ^ 2 * Real.log H +
      (C * Real.log (Real.sqrt 3) + D - Real.pi / (3 * Real.sqrt 3)) * H ^ 2 =
      C / 6 * ((X - 1) * Real.log (X - 1)) + Q * (X - 1) := by
    rw [hlogH, hlog3, hH2]
    have h3 : Real.sqrt 3 ≠ 0 := by positivity
    simp only [Q]; field_simp; ring
  rw [hmain, ← hA] at h
  -- the powers of `X`
  have hX1 : 1 ≤ X := by linarith
  have hs1 : 1 ≤ X ^ s := Real.one_le_rpow hX1 (by positivity)
  have hHX : H ^ (1 + ε) ≤ X ^ s := by
    have hHs : H ≤ X ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, hHdef]
      exact Real.sqrt_le_sqrt (by linarith)
    calc H ^ (1 + ε) ≤ (X ^ (1 / 2 : ℝ)) ^ (1 + ε) :=
          Real.rpow_le_rpow hH0 hHs (by linarith)
      _ = X ^ ((1 + ε) / 2) := by rw [← Real.rpow_mul hX0.le]; ring_nf
      _ ≤ X ^ s := Real.rpow_le_rpow_of_exponent_le hX1 (by simp only [s]; linarith)
  have hlogX : Real.log X ≤ X ^ s / s := Real.log_le_rpow_div hX0.le (by positivity)
  obtain ⟨d0, d1⟩ := xlogx_diff hX2
  have hC0 : 0 < C := hC.positive
  have hc1 : c * H ^ (1 + ε) ≤ |c| * X ^ s :=
    (mul_le_mul_of_nonneg_right (le_abs_self c) hHpow).trans
      (mul_le_mul_of_nonneg_left hHX (abs_nonneg c))
  have hQ : |Q| ≤ |Q| * X ^ s := le_mul_of_one_le_right (abs_nonneg Q) hs1
  have hlog' : C / 6 * (Real.log X + 1) ≤ C / 6 * (1 / s) * X ^ s + C / 6 * X ^ s := by
    have : Real.log X + 1 ≤ X ^ s / s + X ^ s := by linarith
    calc C / 6 * (Real.log X + 1) ≤ C / 6 * (X ^ s / s + X ^ s) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  simp only
  rw [← hCc, ← hDc, ← hQdef]
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have p0 : 0 ≤ C / 6 * (X * Real.log X - (X - 1) * Real.log (X - 1) - Real.log X) :=
    mul_nonneg (by positivity) d0
  have p1 : C / 6 * (X * Real.log X - (X - 1) * Real.log (X - 1) - Real.log X) ≤ C / 6 * 1 :=
    mul_le_mul_of_nonneg_left d1 (by positivity)
  have p2 : 0 ≤ C / 6 * Real.log X := mul_nonneg (by positivity) hlog0
  have hQ1 := neg_abs_le Q
  have hQ2 := le_abs_self Q
  rw [abs_le] at h ⊢
  constructor <;> nlinarith

/-- The labelled formula in the current manuscript. -/
theorem «eqn:A1asymptotic»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.GeneralMonic.A1Claim := by
  obtain ⟨hf, he⟩ := coefficient_estimate hPoisson hCN
  refine ⟨hf, ?_⟩
  intro ε hε
  obtain ⟨K, X₀, hK⟩ := he ε hε
  refine ⟨K, X₀, fun X hX => ?_⟩
  simpa only [CountPolynomialNormalization.trace_one_main X] using hK X hX

end Cubic.Counting.A1Asymptotic
