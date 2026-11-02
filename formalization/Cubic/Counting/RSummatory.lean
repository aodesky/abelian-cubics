import Cubic.Counting.TraceZeroCoefficients
import Cubic.Counting.DSummatory

/-!
# The summatory function of `r(N)`

Supporting estimate for `prop:traceZeroAsymptotic`. By `lemma:traceZeroCoefficients`, for
`N = 3^a M` with `3 ∤ M`, `r(N) = d_N` if `a = 0` and `r(N) = 3d_M + 1_{N = 3u²}` if `a ≥ 1`;
since `d_n = 0` for `3 ∣ n`, this is `r(N) = d_N + 3 Σ_{e ≥ 1, 3^e ∣ N} d_{N/3^e} + 1_{N = 3u²}`.
Summing,
`Σ_{N ≤ X} r(N) = Σ_{n ≤ X} d_n + 3 Σ_{e ≥ 1} Σ_{n ≤ X/3^e} d_n + O(X^{1/2})`.
-/

noncomputable section

namespace Cubic.Counting.RSummatory

open Cubic.Counting.GeneralMonicData Cubic.PoissonSummation

theorem d_eq_zero (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    {n : ℕ} (hn : 3 ∣ n) : d n = 0 := by
  have h := HeightCountingIdentification.counts_eq_coefficient hPoisson n
  rw [HeightCountingCoefficients.coefficient_apply, if_pos hn] at h
  exact_mod_cast h

open scoped Classical in
/-- `1_{N = 3u² for some u > 0}`. -/
def ind (N : ℕ) : ℕ := if ∃ u : ℤ, 0 < u ∧ (N : ℤ) = 3 * u ^ 2 then 1 else 0

/-- The per-`N` identity, with the powers `3^e`, `1 ≤ e ≤ m`, for any `m ≥ N`. -/
theorem r_eq (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    {N m : ℕ} (hN : 1 ≤ N) (hm : N ≤ m) :
    r N = d N + 3 * ∑ e ∈ Finset.Icc 1 m, (if 3 ^ e ∣ N then d (N / 3 ^ e) else 0) + ind N := by
  obtain ⟨a, M, hM3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : N ≠ 0) 3 (by norm_num)
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have h := (Cubic.Counting.TraceZeroCoefficients.«lemma:traceZeroCoefficients» hPoisson
    a M hM hM3).2
  have hcop : ∀ e, Nat.Coprime (3 ^ e) M := fun e =>
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3)
  have hle : ∀ e, 3 ^ e ∣ 3 ^ a * M → e ≤ a := fun e he =>
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp ((hcop e).dvd_of_dvd_mul_right he)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hsum : ∑ e ∈ Finset.Icc 1 m, (if 3 ^ e ∣ 3 ^ 0 * M then d (3 ^ 0 * M / 3 ^ e) else 0)
        = 0 := Finset.sum_eq_zero fun e he => by
      rw [if_neg]; intro h'; have := hle e h'; simp at he; omega
    have hind : ind (3 ^ 0 * M) = 0 := by
      rw [ind, if_neg]
      rintro ⟨u, -, hu⟩
      apply hM3
      have : (3 : ℤ) ∣ (M : ℤ) := ⟨u ^ 2, by simpa using hu⟩
      exact_mod_cast this
    rw [if_pos rfl] at h
    rw [hsum, hind]
    simp only [pow_zero, one_mul, mul_zero, add_zero] at h ⊢
    exact_mod_cast h
  · have hsum : ∑ e ∈ Finset.Icc 1 m, (if 3 ^ e ∣ 3 ^ a * M then d (3 ^ a * M / 3 ^ e) else 0)
        = d M := by
      have hma : a ≤ m := by
        have : a < 3 ^ a := Nat.lt_pow_self (by norm_num)
        have : 3 ^ a ≤ 3 ^ a * M := Nat.le_mul_of_pos_right _ hM
        omega
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_Icc.mpr ⟨ha, hma⟩)]
      · rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (by positivity)]
      · intro e he hea
        split_ifs with hd
        · have hlt : e < a := lt_of_le_of_ne (hle e hd) hea
          apply d_eq_zero hPoisson
          rw [show 3 ^ a * M = 3 ^ e * (3 ^ (a - e) * M) by
            rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le],
            Nat.mul_div_cancel_left _ (by positivity)]
          exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
        · rfl
    have hd0 : d (3 ^ a * M) = 0 :=
      d_eq_zero hPoisson (Dvd.dvd.mul_right (dvd_pow_self 3 ha.ne') _)
    rw [if_neg ha.ne'] at h
    rw [hsum, hd0, ind]
    split_ifs with hu
    · rw [if_pos hu] at h
      have h' : r ((3 ^ a * M : ℕ) : ℤ) = 3 * d M + 1 := by exact_mod_cast h
      rw [h']; ring
    · rw [if_neg hu] at h
      have h' : r ((3 ^ a * M : ℕ) : ℤ) = 3 * d M := by exact_mod_cast h
      rw [h']; ring

/-- `Σ_{n ≤ Y} d_n`. -/
def D (Y : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (d n : ℝ)

theorem sum_int_eq_sum_nat {X : ℝ} (hX : 0 ≤ X) (f : ℤ → ℝ) :
    ∑ N ∈ Finset.Icc (1 : ℤ) ⌊X⌋, f N = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n := by
  have hfl : (⌊X⌋₊ : ℤ) = ⌊X⌋ := Int.natCast_floor_eq_floor hX
  refine Finset.sum_nbij' (fun N : ℤ => N.toNat) (fun n : ℕ => (n : ℤ)) ?_ ?_ ?_ ?_ ?_ <;>
    intro x hx <;> simp only [Finset.mem_Icc] at hx ⊢
  · omega
  · omega
  · omega
  · simp
  · rw [Int.toNat_of_nonneg (by omega)]

/-- Reindexing `N = 3^e n`. -/
theorem sum_dvd_eq {X : ℝ} (hX : 0 ≤ X) (e : ℕ) :
    ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (if 3 ^ e ∣ N then (d (N / 3 ^ e) : ℝ) else 0) = D (X / 3 ^ e) := by
  rw [← Finset.sum_filter, D]
  have h3 : (0 : ℝ) < 3 ^ e := by positivity
  refine Finset.sum_nbij' (fun N => N / 3 ^ e) (fun n => 3 ^ e * n) ?_ ?_ ?_ ?_ ?_
  · intro N hN
    simp only [Finset.mem_filter, Finset.mem_Icc] at hN ⊢
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hN
    rw [Nat.mul_div_cancel_left _ (by positivity)]
    refine ⟨by rcases k with _ | k; simp at h1; omega, Nat.le_floor ?_⟩
    rw [le_div_iff₀ h3]
    have := (Nat.le_floor_iff hX).mp h2
    push_cast at this; linarith
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega)), Nat.le_floor ?_⟩,
      dvd_mul_right _ _⟩
    have := (Nat.le_floor_iff (by positivity)).mp hn.2
    rw [le_div_iff₀ h3] at this
    push_cast; linarith
  · intro N hN
    simp only [Finset.mem_filter] at hN
    exact Nat.mul_div_cancel' hN.2
  · intro n _
    exact Nat.mul_div_cancel_left _ (by positivity)
  · intro N _; rfl

/-- `Σ_{N ≤ X} r(N) = D(X) + 3 Σ_{e ≥ 1} D(X/3^e) + #{N ≤ X : N = 3u²}`. -/
theorem sum_r (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    {X : ℝ} (hX : 0 ≤ X) :
    ∑ N ∈ Finset.Icc (1 : ℤ) ⌊X⌋, (r N : ℝ) =
      D X + 3 * ∑ e ∈ Finset.Icc 1 ⌊X⌋₊, D (X / 3 ^ e) +
        ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (ind N : ℝ) := by
  rw [sum_int_eq_sum_nat hX]
  have hper : ∀ N ∈ Finset.Icc 1 ⌊X⌋₊, (r N : ℝ) = d N +
      3 * ∑ e ∈ Finset.Icc 1 ⌊X⌋₊, (if 3 ^ e ∣ N then (d (N / 3 ^ e) : ℝ) else 0) + ind N := by
    intro N hN
    rw [Finset.mem_Icc] at hN
    rw [show ((N : ℤ)) = ((N : ℕ) : ℤ) from rfl, r_eq hPoisson hN.1 hN.2]
    push_cast
    congr 2
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_comm]
  congr 2
  exact congrArg (3 * ·) (Finset.sum_congr rfl fun e _ => sum_dvd_eq hX e)

/-! ### Estimates -/

theorem geom_one (L : ℕ) : ∑ e ∈ Finset.Icc 1 L, (1 / 3 : ℝ) ^ e = (1 - (1 / 3) ^ L) / 2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]; ring

theorem geom_two (L : ℕ) :
    ∑ e ∈ Finset.Icc 1 L, (e : ℝ) * (1 / 3 : ℝ) ^ e = 3 / 4 - (2 * L + 3) / 4 * (1 / 3) ^ L := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]; push_cast; ring

theorem D_eq_zero {Y : ℝ} (hY : Y < 1) : D Y = 0 := by
  rw [D, Nat.floor_eq_zero.mpr hY]; simp

theorem D_nonneg (Y : ℝ) : 0 ≤ D Y := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem D_mono {Y Z : ℝ} (h : Y ≤ Z) : D Y ≤ D Z :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor h)) fun _ _ _ => Nat.cast_nonneg _

/-- Only `e ≤ log₃ X` contribute. -/
theorem sum_D_eq {X : ℝ} (hX : 1 ≤ X) :
    ∑ e ∈ Finset.Icc 1 ⌊X⌋₊, D (X / 3 ^ e) =
      ∑ e ∈ Finset.Icc 1 (Nat.log 3 ⌊X⌋₊), D (X / 3 ^ e) := by
  have hL : Nat.log 3 ⌊X⌋₊ ≤ ⌊X⌋₊ := (Nat.log_lt_self 3 (by
    have := Nat.one_le_floor_iff X |>.mpr hX; omega)).le
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hL) fun e he he' => ?_
  apply D_eq_zero
  simp only [Finset.mem_Icc, not_and, not_le] at he he'
  have hlt : ⌊X⌋₊ < 3 ^ e := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) ⌊X⌋₊
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (he' he.1))
  rw [div_lt_one (by positivity)]
  have := Nat.lt_floor_add_one X
  have h' : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ ((3 ^ e : ℕ) : ℝ) := by exact_mod_cast hlt
  push_cast at h'; linarith

/-- The indicator sum is at most `√X`. -/
theorem sum_ind_le {X : ℝ} (hX : 0 ≤ X) : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (ind N : ℝ) ≤ √X := by
  classical
  have hsub : (Finset.Icc 1 ⌊X⌋₊).filter (fun N => ind N = 1) ⊆
      (Finset.Icc 1 ⌊√X⌋₊).image (fun u => 3 * u ^ 2) := by
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_Icc, ind] at hN
    split_ifs at hN with hu
    · obtain ⟨u, hu0, hNu⟩ := hu
      simp only [Finset.mem_image, Finset.mem_Icc]
      refine ⟨u.toNat, ⟨by omega, Nat.le_floor ?_⟩, ?_⟩
      · rw [Real.le_sqrt (by positivity) hX]
        have h1 : ((u.toNat : ℕ) : ℝ) = (u : ℝ) := by
          have := Int.toNat_of_nonneg hu0.le; exact_mod_cast this
        have h2 : ((N : ℕ) : ℝ) ≤ X := (Nat.le_floor_iff hX).mp hN.1.2
        have h3 : ((N : ℤ) : ℝ) = 3 * (u : ℝ) ^ 2 := by exact_mod_cast hNu
        push_cast at h3
        rw [h1]; nlinarith [sq_nonneg (u : ℝ)]
      · have : ((3 * u.toNat ^ 2 : ℕ) : ℤ) = (N : ℤ) := by
          push_cast; rw [Int.toNat_of_nonneg hu0.le]; exact hNu.symm
        exact_mod_cast this
    · exact absurd hN.2 (by norm_num)
  have hsum : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (ind N : ℝ) =
      ((Finset.Icc 1 ⌊X⌋₊).filter (fun N => ind N = 1)).card := by
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl fun N _ => ?_
    unfold ind; split_ifs <;> simp_all
  rw [hsum]
  calc (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => ind N = 1)).card : ℝ)
      ≤ ((Finset.Icc 1 ⌊√X⌋₊).image (fun u => 3 * u ^ 2)).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 ⌊√X⌋₊).card := by exact_mod_cast Finset.card_image_le
    _ = ⌊√X⌋₊ := by simp
    _ ≤ √X := Nat.floor_le (Real.sqrt_nonneg _)

/-- The expansion of `D` holds for all `Y ≥ 1`, after enlarging the constant. -/
theorem D_uniform {a b : ℝ} (hD : CubicTargets.Counting.GeneralMonic.HasExpansion D a b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 1 ≤ Y → |D Y - (a * Y * Real.log Y + b * Y)| ≤ K * Y ^ (1 / 2 + ε) := by
  obtain ⟨K, X₀, hK⟩ := hD ε hε
  set X₁ := max X₀ 1
  have hX₁ : 1 ≤ X₁ := le_max_right _ _
  refine ⟨max K 0 + (D X₁ + |a| * (X₁ * Real.log X₁) + |b| * X₁), by
    have := D_nonneg X₁
    have := Real.log_nonneg hX₁
    positivity, fun Y hY => ?_⟩
  have hs : 1 ≤ Y ^ (1 / 2 + ε) := Real.one_le_rpow hY (by linarith)
  have hB0 : 0 ≤ D X₁ + |a| * (X₁ * Real.log X₁) + |b| * X₁ := by
    have := D_nonneg X₁
    have := Real.log_nonneg hX₁
    positivity
  rcases le_or_gt X₁ Y with h | h
  · have := hK Y (le_trans (le_max_left _ _) h)
    have h1 : K * Y ^ (1 / 2 + ε) ≤ max K 0 * Y ^ (1 / 2 + ε) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    nlinarith
  · have hlog : Real.log Y ≤ Real.log X₁ := Real.log_le_log (by linarith) h.le
    have hlog0 := Real.log_nonneg hY
    have hmain : |a * Y * Real.log Y + b * Y| ≤ |a| * (X₁ * Real.log X₁) + |b| * X₁ := by
      calc _ ≤ |a * Y * Real.log Y| + |b * Y| := abs_add_le _ _
        _ = |a| * (Y * Real.log Y) + |b| * Y := by
          rw [mul_assoc, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Y),
            abs_of_nonneg hlog0]
        _ ≤ _ := by gcongr
    have hDY : |D Y| ≤ D X₁ := by
      rw [abs_of_nonneg (D_nonneg Y)]; exact D_mono h.le
    have := abs_sub _ _ |>.trans (add_le_add hDY hmain)
    have h0 : 0 ≤ max K 0 * Y ^ (1 / 2 + ε) := by positivity
    nlinarith

/-- The difference between the truncated and the complete geometric sums. -/
theorem tail_bound (a b lX l3 t L : ℝ) (hlX : 0 ≤ lX) (hl3 : 0 < l3) (ht : 0 ≤ t) (ht3 : t ≤ 3)
    (hL : 0 ≤ L) (hLl : L * l3 ≤ lX) :
    |-(a * lX * t / 2) + a * (L * l3) * t / 2 + 3 / 4 * a * l3 * t - b * t / 2| ≤
      3 * |a| * lX + 9 / 4 * |a| * l3 + 3 / 2 * |b| := by
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have e1 : |a * lX * t / 2| = |a| * (lX * t) / 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hlX, abs_of_nonneg ht]; norm_num; ring
  have e2 : |a * (L * l3) * t / 2| = |a| * ((L * l3) * t) / 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hL hl3.le), abs_of_nonneg ht]
    norm_num; ring
  have e3 : |3 / 4 * a * l3 * t| = 3 / 4 * |a| * (l3 * t) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hl3.le, abs_of_nonneg ht]; norm_num; ring
  have e4 : |b * t / 2| = |b| * t / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg ht]; norm_num
  have m1 : lX * t ≤ lX * 3 := mul_le_mul_of_nonneg_left ht3 hlX
  have m2 : (L * l3) * t ≤ lX * 3 :=
    (mul_le_mul_of_nonneg_left ht3 (mul_nonneg hL hl3.le)).trans (by linarith)
  have m3 : l3 * t ≤ l3 * 3 := mul_le_mul_of_nonneg_left ht3 hl3.le
  have n1 := mul_le_mul_of_nonneg_left m1 ha
  have n2 := mul_le_mul_of_nonneg_left m2 ha
  have n3 := mul_le_mul_of_nonneg_left m3 ha
  have n4 := mul_le_mul_of_nonneg_left ht3 hb
  have t1 := abs_add_le (-(a * lX * t / 2) + a * (L * l3) * t / 2 + 3 / 4 * a * l3 * t) (-(b * t / 2))
  have t2 := abs_add_le (-(a * lX * t / 2) + a * (L * l3) * t / 2) (3 / 4 * a * l3 * t)
  have t3 := abs_add_le (-(a * lX * t / 2)) (a * (L * l3) * t / 2)
  rw [abs_neg] at t1 t3
  rw [sub_eq_add_neg]
  linarith

/-- `Σ_{N ≤ X} r(N) = (5C/6) X log X + (5D/3 - (3C/4) log 3) X + O_ε(X^{1/2+ε})`. -/
theorem sum_r_expansion
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.GeneralMonic.HasExpansion
      (fun X => ∑ N ∈ Finset.Icc (1 : ℤ) ⌊X⌋, (r N : ℝ))
      (5 * Cconst / 6) (5 * Dconst / 3 - 3 * Cconst / 4 * Real.log 3) := by
  have hD : CubicTargets.Counting.GeneralMonic.HasExpansion D (Cconst / 3) (2 * Dconst / 3) :=
    Cubic.Counting.DSummatory.coefficient_estimate hPoisson hCN
  set a := Cconst / 3
  set b := 2 * Dconst / 3
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := D_uniform hD (half_pos hε)
  have hl3 : 1 < Real.log 3 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hl3pos : 0 < Real.log 3 := by linarith
  refine ⟨K + 3 * (3 * |a| * (2 / ε) + 9 / 4 * |a| * Real.log 3 + 3 / 2 * |b| +
    K / Real.log 3 * (2 / ε)) + 1, 1, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  -- powers of `X`
  set P := X ^ (1 / 2 + ε)
  set Q := X ^ (1 / 2 + ε / 2)
  set R := X ^ (ε / 2)
  have hPQR : P = Q * R := by
    show X ^ (1 / 2 + ε) = X ^ (1 / 2 + ε / 2) * X ^ (ε / 2)
    rw [← Real.rpow_add hX0]; ring_nf
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hX (by linarith)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX (by linarith)
  have hQP : Q ≤ P := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hRP : R ≤ P := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hsqrtP : √X ≤ P := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hlogX : Real.log X ≤ 2 / ε * R := by
    have := Real.log_le_rpow_div hX0.le (half_pos hε)
    rw [div_div_eq_mul_div] at this; linarith [show X ^ (ε / 2) * 2 / ε = 2 / ε * R by ring]
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX
  -- `L = log₃ X`
  set L := Nat.log 3 ⌊X⌋₊
  have hfl : 1 ≤ ⌊X⌋₊ := Nat.one_le_floor_iff X |>.mpr hX
  have hL1 : (3 : ℝ) ^ L ≤ X := by
    have := Nat.pow_log_le_self 3 (by omega : ⌊X⌋₊ ≠ 0)
    have h' : ((3 ^ L : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast this
    push_cast at h'; exact h'.trans (Nat.floor_le hX0.le)
  have hL2 : X < (3 : ℝ) ^ (L + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) ⌊X⌋₊
    have h' : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ ((3 ^ (L + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'; linarith [Nat.lt_floor_add_one X]
  have hLlog : (L : ℝ) * Real.log 3 ≤ Real.log X := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hL1
  set t := X * (1 / 3) ^ L
  have ht1 : 1 ≤ t := by
    have : t = X / 3 ^ L := by simp [t, div_eq_mul_inv]
    rw [this, le_div_iff₀ (by positivity)]; linarith
  have ht3 : t ≤ 3 := by
    have : t = X / 3 ^ L := by simp [t, div_eq_mul_inv]
    rw [this, div_le_iff₀ (by positivity)]; rw [pow_succ] at hL2; linarith
  -- the sum over `e`
  have hsplit : ∑ e ∈ Finset.Icc 1 L, D (X / 3 ^ e) =
      ∑ e ∈ Finset.Icc 1 L, (a * (X * (1 / 3) ^ e) * (Real.log X - e * Real.log 3) +
        b * (X * (1 / 3) ^ e)) +
      ∑ e ∈ Finset.Icc 1 L, (D (X / 3 ^ e) - (a * (X / 3 ^ e) * Real.log (X / 3 ^ e) +
        b * (X / 3 ^ e))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Real.log_div hX0.ne' (by positivity), Real.log_pow,
      show X / 3 ^ e = X * (1 / 3) ^ e by rw [one_div, inv_pow, div_eq_mul_inv]]
    ring
  have hmain : ∑ e ∈ Finset.Icc 1 L, (a * (X * (1 / 3) ^ e) * (Real.log X - e * Real.log 3) +
      b * (X * (1 / 3) ^ e)) =
      (a * X * Real.log X + b * X) * ((1 - (1 / 3) ^ L) / 2) -
        a * X * Real.log 3 * (3 / 4 - (2 * L + 3) / 4 * (1 / 3) ^ L) := by
    rw [← geom_one, ← geom_two, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have herr : |∑ e ∈ Finset.Icc 1 L, (D (X / 3 ^ e) - (a * (X / 3 ^ e) * Real.log (X / 3 ^ e) +
      b * (X / 3 ^ e)))| ≤ L * (K * Q) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ e ∈ Finset.Icc 1 L, |D (X / 3 ^ e) - (a * (X / 3 ^ e) * Real.log (X / 3 ^ e) +
        b * (X / 3 ^ e))| ≤ K * Q := by
      intro e he
      rw [Finset.mem_Icc] at he
      have h3e : (3 : ℝ) ^ e ≤ X :=
        le_trans (pow_le_pow_right₀ (by norm_num) he.2) hL1
      have hY1 : 1 ≤ X / 3 ^ e := by rw [le_div_iff₀ (by positivity)]; linarith
      refine (hK _ hY1).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      exact Real.rpow_le_rpow (by linarith) (div_le_self hX0.le (one_le_pow₀ (by norm_num)))
        (by linarith)
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    simp
  have hLKQ : L * (K * Q) ≤ K / Real.log 3 * (2 / ε) * P := by
    have hL' : (L : ℝ) ≤ 2 / ε * R / Real.log 3 := by
      rw [le_div_iff₀ hl3pos]; linarith
    calc (L : ℝ) * (K * Q) ≤ 2 / ε * R / Real.log 3 * (K * Q) :=
          mul_le_mul_of_nonneg_right hL' (by positivity)
      _ = K / Real.log 3 * (2 / ε) * P := by rw [hPQR]; field_simp
  -- assemble
  have hDX := hK X hX
  have hQ' : K * Q ≤ K * P := mul_le_mul_of_nonneg_left hQP hK0
  have hind := sum_ind_le hX0.le
  have hind0 : 0 ≤ ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (ind N : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  simp only
  rw [sum_r hPoisson hX0.le, sum_D_eq hX, hsplit, hmain]
  have hpow : (1 / 3 : ℝ) ^ L * X = t := by ring
  set E := ∑ e ∈ Finset.Icc 1 L, (D (X / 3 ^ e) - (a * (X / 3 ^ e) * Real.log (X / 3 ^ e) +
      b * (X / 3 ^ e)))
  have hE := abs_le.mp (herr.trans hLKQ)
  have hDX' := abs_le.mp (hDX.trans hQ')
  have hlogP : Real.log X ≤ 2 / ε * P := hlogX.trans (by gcongr)
  have hLl : (L : ℝ) ≤ Real.log X / Real.log 3 := by rw [le_div_iff₀ hl3pos]; exact hLlog
  -- the difference of main terms is `O(log X)`
  have heq : (a * X * Real.log X + b * X) * ((1 - (1 / 3) ^ L) / 2) -
      a * X * Real.log 3 * (3 / 4 - (2 * L + 3) / 4 * (1 / 3) ^ L) -
      (a * X * Real.log X / 2 - 3 / 4 * a * X * Real.log 3 + b * X / 2) =
      -(a * Real.log X * t / 2) + a * (L * Real.log 3) * t / 2 + 3 / 4 * a * Real.log 3 * t -
        b * t / 2 := by rw [← hpow]; ring
  have hd := tail_bound a b (Real.log X) (Real.log 3) t L hlog0 hl3pos (by linarith) ht3
    (Nat.cast_nonneg _) hLlog
  rw [← heq] at hd
  have hd' := abs_le.mp hd
  have hP1 : 1 ≤ P := hQ1.trans hQP
  have p1 : 3 * |a| * Real.log X ≤ 3 * |a| * (2 / ε) * P := by
    have := mul_le_mul_of_nonneg_left hlogP (by positivity : 0 ≤ 3 * |a|)
    linarith [show 3 * |a| * (2 / ε * P) = 3 * |a| * (2 / ε) * P by ring]
  have p2 : 9 / 4 * |a| * Real.log 3 ≤ 9 / 4 * |a| * Real.log 3 * P := by
    have := mul_le_mul_of_nonneg_left hP1 (by positivity : 0 ≤ 9 / 4 * |a| * Real.log 3)
    linarith
  have p3 : 3 / 2 * |b| ≤ 3 / 2 * |b| * P := by
    have := mul_le_mul_of_nonneg_left hP1 (by positivity : 0 ≤ 3 / 2 * |b|)
    linarith
  have hmainEq : 5 * Cconst / 6 * X * Real.log X +
      (5 * Dconst / 3 - 3 * Cconst / 4 * Real.log 3) * X =
      (a * X * Real.log X + b * X) +
        3 * (a * X * Real.log X / 2 - 3 / 4 * a * X * Real.log 3 + b * X / 2) := by
    simp only [a, b]; ring
  rw [hmainEq, abs_le]
  constructor <;> linarith

end Cubic.Counting.RSummatory
