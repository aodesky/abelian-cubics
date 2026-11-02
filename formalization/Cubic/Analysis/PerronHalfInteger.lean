import Cubic.Analysis.PerronTruncated
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Truncated Perron formula at half-integers

This is the specialization used in the proof of `eqn:dSummatoryForGeneralTrace`.
Let `d n ≥ 0` with `d n ≪_η n^η` for every `η > 0`, and suppose that
`∑ d n n^{-c} ≤ B (log X)^2` at `c = 1 + 1 / log X` for all `X ≥ 3`. For a half-integer
`X ≥ 3` and `T ≥ X`, the error in the truncated Perron formula on the line `Re s = c` is
`O_η(X^η (log X)^2)`.

In the direct proof, the terms with `X / 2 ≤ n ≤ 2X` are controlled by `|X - n| ≥ 1/2`
together with `d n ≪_η n^η`, via `|log (X / n)| ≥ |X - n| / (2X)`; the sum of `1 / |X - n|`
over these `n` is bounded by a harmonic number. The other terms have `|log (X / n)| ≥ 1/2`
and are bounded using `X^c = e X` and the bound on `∑ d n n^{-c}`.
-/

noncomputable section

namespace Cubic.Analysis.Perron

open Complex Set Filter LSeries

/-- `|log (p / q)| ≥ |p - q| / max p q` for `p, q > 0`. -/
lemma abs_sub_div_max_le_abs_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    |p - q| / max p q ≤ |Real.log (p / q)| := by
  rcases le_total p q with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith), neg_sub]
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hq hp)
    rw [inv_div] at hl
    have hlog : Real.log (p / q) = -Real.log (q / p) := by rw [← Real.log_inv, inv_div]
    rw [hlog, abs_neg, abs_of_nonneg (Real.log_nonneg ((one_le_div hp).2 h))]
    calc (q - p) / q = 1 - p / q := by field_simp
      _ ≤ _ := hl
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hq)
    rw [inv_div] at hl
    rw [abs_of_nonneg (Real.log_nonneg ((one_le_div hq).2 h))]
    calc (p - q) / p = 1 - q / p := by field_simp
      _ ≤ _ := hl

/-- `∑_{0 ≤ n ≤ 2m+1} 1 / |m + 1/2 - n| ≤ 4 (1 + log (m + 1))`. -/
lemma sum_inv_abs_halfInteger_sub_le (m : ℕ) :
    ∑ n ∈ Finset.range (2 * m + 2), 1 / |((m : ℝ) + 1 / 2) - n| ≤
      4 * (1 + Real.log (m + 1)) := by
  set g : ℕ → ℝ := fun n => 1 / |((m : ℝ) + 1 / 2) - n| with hg
  have hsplit : 2 * m + 2 = (m + 1) + (m + 1) := by ring
  rw [hsplit, Finset.sum_range_add, ← Finset.sum_range_reflect g (m + 1)]
  have h1 : ∀ j ∈ Finset.range (m + 1), g (m + 1 - 1 - j) ≤ 2 / ((j : ℝ) + 1) := by
    intro j hj
    have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    simp only [g]
    rw [show m + 1 - 1 - j = m - j by omega, Nat.cast_sub hj',
      show (m : ℝ) + 1 / 2 - (m - j) = j + 1 / 2 by ring, abs_of_pos (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have h2 : ∀ j ∈ Finset.range (m + 1), g (m + 1 + j) ≤ 2 / ((j : ℝ) + 1) := by
    intro j _
    simp only [g]
    push_cast
    rw [show (m : ℝ) + 1 / 2 - (m + 1 + j) = -(j + 1 / 2) by ring, abs_neg,
      abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hH : ∑ j ∈ Finset.range (m + 1), 2 / ((j : ℝ) + 1) = 2 * (harmonic (m + 1) : ℝ) := by
    simp [harmonic, Finset.mul_sum, div_eq_mul_inv]
  have hlog := harmonic_le_one_add_log (m + 1)
  push_cast at hlog
  calc ∑ j ∈ Finset.range (m + 1), g (m + 1 - 1 - j) + ∑ j ∈ Finset.range (m + 1), g (m + 1 + j)
      ≤ ∑ j ∈ Finset.range (m + 1), 2 / ((j : ℝ) + 1) +
          ∑ j ∈ Finset.range (m + 1), 2 / ((j : ℝ) + 1) :=
        add_le_add (Finset.sum_le_sum h1) (Finset.sum_le_sum h2)
    _ ≤ 4 * (1 + Real.log (m + 1)) := by rw [hH]; linarith

/-- The pointwise bound on the terms of the Perron error for a half-integer `X`. -/
lemma perron_error_term_le {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) {K η : ℝ} (hη : 0 < η)
    (hK : ∀ n : ℕ, 1 ≤ n → d n ≤ K * (n : ℝ) ^ η) (hK0 : 0 ≤ K) {m : ℕ} {X c T : ℝ}
    (hXm : X = m + 1 / 2) (hX0 : 0 < X) (hc0 : 0 < c) (hc2 : c ≤ 2)
    (hXc : X ^ c = Real.exp 1 * X) (hXT : X ≤ T) (n : ℕ) :
    ‖(d n : ℂ)‖ * (X / n) ^ c * min 4 (1 / (Real.pi * T * |Real.log (X / n)|)) ≤
      2 * Real.exp 1 / Real.pi * (d n / (n : ℝ) ^ c) +
        (if n ∈ Finset.range (2 * m + 2) then
          8 / Real.pi * K * (2 * X) ^ η * (1 / |X - n|) else 0) := by
  have hT0 : 0 < T := hX0.trans_le hXT
  have hpi := Real.pi_pos
  have hA0 : 0 ≤ 2 * Real.exp 1 / Real.pi * (d n / (n : ℝ) ^ c) := by
    have := hd n; positivity
  have hB0 : 0 ≤ (if n ∈ Finset.range (2 * m + 2) then
      8 / Real.pi * K * (2 * X) ^ η * (1 / |X - n|) else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.cast_zero, div_zero, Real.zero_rpow hc0.ne', mul_zero, zero_mul]
    linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hXn : (n : ℝ) ≠ X := by
    intro h
    rw [hXm] at h
    have h2 : ((2 * n : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective h2
    omega
  have hdn : ‖(d n : ℂ)‖ = d n := by rw [Complex.norm_real, Real.norm_of_nonneg (hd n)]
  rw [hdn]
  set ℓ := |Real.log (X / n)| with hℓ
  have hlog := abs_sub_div_max_le_abs_log hX0 hn'
  have hXn0 : 0 < |X - n| := abs_pos.2 (sub_ne_zero.2 hXn.symm)
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (div_pos hXn0 (lt_max_of_lt_left hX0)) hlog
  have hy0 : 0 ≤ d n * (X / n) ^ c := mul_nonneg (hd n) (Real.rpow_nonneg (by positivity) c)
  have hmin : d n * (X / n) ^ c * min 4 (1 / (Real.pi * T * ℓ)) ≤
      d n * (X / n) ^ c * (1 / (Real.pi * T * ℓ)) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hy0
  refine hmin.trans ?_
  -- Terms with `|log (X / n)| ≥ 1/2`.
  have hAcase : 1 / 2 ≤ ℓ →
      d n * (X / n) ^ c * (1 / (Real.pi * T * ℓ)) ≤
        2 * Real.exp 1 / Real.pi * (d n / (n : ℝ) ^ c) := by
    intro hℓ2
    have h1 : 1 / (Real.pi * T * ℓ) ≤ 2 / (Real.pi * T) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hpi hT0]
    have hXT1 : X / T ≤ 1 := (div_le_one hT0).2 hXT
    have hdnc : 0 ≤ d n / (n : ℝ) ^ c := by have := hd n; positivity
    calc d n * (X / n) ^ c * (1 / (Real.pi * T * ℓ))
        ≤ d n * (X / n) ^ c * (2 / (Real.pi * T)) := mul_le_mul_of_nonneg_left h1 hy0
      _ = 2 * Real.exp 1 / Real.pi * (d n / (n : ℝ) ^ c) * (X / T) := by
        rw [Real.div_rpow hX0.le hn'.le, hXc]
        field_simp
      _ ≤ 2 * Real.exp 1 / Real.pi * (d n / (n : ℝ) ^ c) * 1 := by gcongr
      _ = _ := mul_one _
  by_cases h2X : (n : ℝ) ≤ 2 * X
  · by_cases hX2 : X ≤ 2 * n
    · -- Terms with `X / 2 ≤ n ≤ 2X`.
      have hmem : n ∈ Finset.range (2 * m + 2) := by
        rw [Finset.mem_range]
        have : (n : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
        have := Nat.cast_le.1 this
        omega
      rw [if_pos hmem]
      have hmax : max X n ≤ 2 * X := max_le (by linarith) h2X
      have hℓX : |X - n| / (2 * X) ≤ ℓ :=
        (div_le_div_of_nonneg_left (abs_nonneg _) (lt_max_of_lt_left hX0) hmax).trans hlog
      have h1 : 1 / (Real.pi * T * ℓ) ≤ 2 * X / (Real.pi * T * |X - n|) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        rw [div_le_iff₀ (by positivity)] at hℓX
        nlinarith [mul_pos hpi hT0]
      have hpow : (X / n) ^ c ≤ 4 := by
        have hXn2 : X / n ≤ 2 := by rw [div_le_iff₀ hn']; linarith
        calc (X / n) ^ c ≤ 2 ^ c := Real.rpow_le_rpow (by positivity) hXn2 hc0.le
          _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc2
          _ = 4 := by norm_num
      have hdK : d n ≤ K * (2 * X) ^ η :=
        (hK n (Nat.one_le_iff_ne_zero.2 hn)).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn'.le h2X hη.le) hK0)
      have hXT1 : X / T ≤ 1 := (div_le_one hT0).2 hXT
      have hKX : 0 ≤ K * (2 * X) ^ η := by positivity
      calc d n * (X / n) ^ c * (1 / (Real.pi * T * ℓ))
          ≤ (K * (2 * X) ^ η) * 4 * (2 * X / (Real.pi * T * |X - n|)) := by
            apply mul_le_mul (mul_le_mul hdK hpow (by positivity) hKX) h1 (by positivity)
              (by positivity)
        _ = 8 / Real.pi * K * (2 * X) ^ η * (1 / |X - n|) * (X / T) := by
            field_simp
            ring
        _ ≤ 8 / Real.pi * K * (2 * X) ^ η * (1 / |X - n|) * 1 := by gcongr
        _ ≤ _ := by linarith
    · -- Terms with `n < X / 2`.
      push_neg at hX2
      have hmax : max X n = X := max_eq_left (by linarith)
      have hℓ2 : 1 / 2 ≤ ℓ := by
        refine le_trans ?_ hlog
        rw [hmax, abs_of_pos (by linarith), le_div_iff₀ hX0]
        linarith
      linarith [hAcase hℓ2]
  · -- Terms with `n > 2X`.
    push_neg at h2X
    have hmax : max X n = n := max_eq_right (by linarith)
    have hℓ2 : 1 / 2 ≤ ℓ := by
      refine le_trans ?_ hlog
      rw [hmax, abs_of_neg (by linarith), le_div_iff₀ hn']
      linarith
    linarith [hAcase hℓ2]

/-- **Truncated Perron formula at half-integers** (the specialization in the proof of
`eqn:dSummatoryForGeneralTrace`). Let `d n ≥ 0` satisfy `d n ≪_η n^η` for every `η > 0`, and
suppose `∑ d n n^{-c} ≤ B (log X)^2` at `c = 1 + 1 / log X` for all `X ≥ 3`. Then for every
`η > 0` there is `K'` such that for every half-integer `X = m + 1/2 ≥ 3` and every `T ≥ X`,
`|∑_{1 ≤ n ≤ X} d n - (1 / 2πi) ∫_{c - iT}^{c + iT} (∑ d n n^{-s}) X^s / s ds|
  ≤ K' X^η (log X)^2`. -/
theorem norm_sum_sub_perronIntegral_halfInteger_le (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hdiv : ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → d n ≤ K * (n : ℝ) ^ η)
    (B : ℝ) (hB : ∀ X : ℝ, 3 ≤ X →
      ∑' n : ℕ, d n / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ B * Real.log X ^ 2) :
    ∀ η : ℝ, 0 < η → ∃ K' : ℝ, ∀ (m : ℕ) (X : ℝ), X = m + 1 / 2 → 3 ≤ X → ∀ T : ℝ, X ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (d n : ℂ) -
          perronIntegral (fun n => (d n : ℂ)) (1 + 1 / Real.log X) T X‖ ≤
        K' * X ^ η * Real.log X ^ 2 := by
  intro η hη
  obtain ⟨K, hK⟩ := hdiv η hη
  refine ⟨2 * Real.exp 1 / Real.pi * B + 96 / Real.pi * K * 2 ^ η, ?_⟩
  intro m X hXm hX3 T hXT
  have hX0 : 0 < X := by linarith
  have hpi := Real.pi_pos
  have hK0 : 0 ≤ K := by
    have := hK 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
    linarith [hd 1]
  set L := Real.log X with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  set c := 1 + 1 / L with hc_def
  have hc0 : 0 < c := by positivity
  have hc2 : c ≤ 2 := by
    have : 1 / L ≤ 1 := (div_le_one (by linarith)).2 hL1
    linarith
  have hT1 : 1 ≤ T := by linarith
  have hXc : X ^ c = Real.exp 1 * X := by
    rw [hc_def, Real.rpow_add hX0, Real.rpow_one, Real.rpow_def_of_pos hX0, ← hL,
      mul_one_div_cancel (by linarith : L ≠ 0)]
    ring
  have hXn : ∀ n : ℕ, (n : ℝ) ≠ X := by
    intro n h
    rw [hXm] at h
    have h2 : ((2 * n : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective h2
    omega
  -- Absolute convergence at `c`, from `d n ≪ n^{η₀}` with `η₀ = 1 / (2L)`.
  have hsum : Summable fun n : ℕ => d n / (n : ℝ) ^ c := by
    obtain ⟨K₀, hK₀⟩ := hdiv (1 / (2 * L)) (by positivity)
    have hexp : 1 / (2 * L) - c < -1 := by
      rw [hc_def]
      have : 0 < 1 / L := by positivity
      have : 1 / (2 * L) = 1 / L / 2 := by field_simp
      linarith
    refine Summable.of_nonneg_of_le (fun n => by have := hd n; positivity) (fun n => ?_)
      ((Real.summable_nat_rpow.2 hexp).mul_left K₀)
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.cast_zero]
      rw [Real.zero_rpow hc0.ne', Real.zero_rpow (by linarith : 1 / (2 * L) - c ≠ 0)]
      simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Real.rpow_sub hn', div_le_iff₀ (Real.rpow_pos_of_pos hn' c)]
      calc d n ≤ K₀ * (n : ℝ) ^ (1 / (2 * L)) := hK₀ n (Nat.one_le_iff_ne_zero.2 hn)
        _ = K₀ * ((n : ℝ) ^ (1 / (2 * L)) / (n : ℝ) ^ c) * (n : ℝ) ^ c := by
          field_simp
  have ha : LSeriesSummable (fun n => (d n : ℂ)) c := by
    refine Summable.of_norm (hsum.congr fun n => ?_)
    rw [norm_term_eq, Complex.ofReal_re]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow hc0.ne']
    · rw [if_neg hn, Complex.norm_real, Real.norm_of_nonneg (hd n)]
  have hmain := norm_sum_sub_perronIntegral_le (fun n => (d n : ℂ)) hc0 hc2 hT1 hX0 hXn ha
  refine hmain.trans ?_
  -- Split each term of the error bound.
  set A : ℕ → ℝ := fun n => 2 * Real.exp 1 / Real.pi * (d n / (n : ℝ) ^ c) with hA_def
  set Bf : ℕ → ℝ := fun n => if n ∈ Finset.range (2 * m + 2) then
    8 / Real.pi * K * (2 * X) ^ η * (1 / |X - n|) else 0 with hBf_def
  have hpt := fun n => perron_error_term_le hd hη hK hK0 hXm hX0 hc0 hc2 hXc hXT n
  have hAs : Summable A := hsum.mul_left _
  have hBfz : ∀ n ∉ Finset.range (2 * m + 2), Bf n = 0 := fun n hn => if_neg hn
  have hBs : Summable Bf := (hasSum_sum_of_ne_finset_zero hBfz).summable
  have hEs := Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (div_nonneg hX0.le (Nat.cast_nonneg n)) _))
      (le_min (by norm_num) (by positivity))) hpt (hAs.add hBs)
  have hS := sum_inv_abs_halfInteger_sub_le m
  rw [← hXm] at hS
  have hlogm : 1 + Real.log (m + 1) ≤ 3 * L := by
    have hm1 : ((m : ℝ) + 1) ≤ 2 * X := by rw [hXm]; linarith
    have := Real.log_le_log (by positivity) hm1
    rw [Real.log_mul (by norm_num) hX0.ne', ← hL] at this
    have := Real.log_two_lt_d9
    linarith
  have hBsum : ∑' n, Bf n ≤ 96 / Real.pi * K * 2 ^ η * X ^ η * L := by
    rw [tsum_eq_sum hBfz, Finset.sum_congr rfl fun n hn => if_pos hn, ← Finset.mul_sum,
      Real.mul_rpow (by norm_num) hX0.le]
    have hc : 0 ≤ 8 / Real.pi * K * (2 ^ η * X ^ η) := by positivity
    calc 8 / Real.pi * K * (2 ^ η * X ^ η) *
          ∑ i ∈ Finset.range (2 * m + 2), 1 / |X - i|
        ≤ 8 / Real.pi * K * (2 ^ η * X ^ η) * (4 * (3 * L)) :=
          mul_le_mul_of_nonneg_left (hS.trans (by linarith)) hc
      _ = 96 / Real.pi * K * 2 ^ η * X ^ η * L := by ring
  have hAsum : ∑' n, A n ≤ 2 * Real.exp 1 / Real.pi * (B * L ^ 2) := by
    rw [hA_def, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hB X hX3) (by positivity)
  have hBL : 0 ≤ B * L ^ 2 :=
    (tsum_nonneg fun n => by have := hd n; positivity).trans (hB X hX3)
  have hXη : 1 ≤ X ^ η := Real.one_le_rpow (by linarith) hη.le
  have hL2 : L ≤ L ^ 2 := by nlinarith
  calc ∑' n : ℕ, ‖(d n : ℂ)‖ * (X / n) ^ c * min 4 (1 / (Real.pi * T * |Real.log (X / n)|))
      ≤ ∑' n, (A n + Bf n) := hEs.tsum_le_tsum hpt (hAs.add hBs)
    _ = ∑' n, A n + ∑' n, Bf n := hAs.tsum_add hBs
    _ ≤ 2 * Real.exp 1 / Real.pi * (B * L ^ 2) + 96 / Real.pi * K * 2 ^ η * X ^ η * L :=
        add_le_add hAsum hBsum
    _ ≤ 2 * Real.exp 1 / Real.pi * (B * L ^ 2 * X ^ η) +
          96 / Real.pi * K * 2 ^ η * X ^ η * L ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hBL hXη)
          (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1 / Real.pi)
        have h2 := mul_le_mul_of_nonneg_left hL2
          (by positivity : (0 : ℝ) ≤ 96 / Real.pi * K * 2 ^ η * X ^ η)
        linarith
    _ = (2 * Real.exp 1 / Real.pi * B + 96 / Real.pi * K * 2 ^ η) * X ^ η * L ^ 2 := by ring

end Cubic.Analysis.Perron
