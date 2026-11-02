import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Contour estimates in `eqn:dSummatoryForGeneralTrace`

Generic estimates for a function `Z` on `Re s > 1/2`, conjugation-symmetric, with a
mean bound `∫_U^{2U} |Z(σ+it)| dt ≤ K U^{1+η}` on the lines `β ≤ σ ≤ 2`:

* "there is a `T ∈ [X, 2X]` for which the upper horizontal integral is `O(X^η)`; the
  lower one has the same bound since the Dirichlet coefficients are real"
  (`exists_height`), by averaging over `T ∈ [X, 2X]`;
* "on the vertical line `Re(s) = β`, dyadic summation … gives
  `∫_{β-iT}^{β+iT} |Z(s) X^s/s| |ds| ≪ X^{β+η}`" (`left_bound`).
-/

noncomputable section

namespace Cubic.Counting.HeightCoefficientContour

open MeasureTheory Set Complex intervalIntegral

/-- A continuous function lies below its average somewhere. -/
theorem exists_le_of_integral_le {f : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hint : ∫ t in a..b, f t ≤ M * (b - a)) :
    ∃ T ∈ Icc a b, f T ≤ M := by
  by_contra h
  push_neg at h
  have hpos : 0 < ∫ t in a..b, (f t - M) := by
    apply intervalIntegral_pos_of_pos_on
    · exact (hf.sub continuousOn_const).intervalIntegrable_of_Icc hab.le
    · intro x hx
      linarith [h x (Ioo_subset_Icc_self hx)]
    · exact hab
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable_of_Icc hab.le) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hpos
  linarith

/-- One dyadic block: `∫_U^{2U} g/t ≤ K U^η`. -/
theorem block_bound {g : ℝ → ℝ} {K η U : ℝ} (hU : 2 ≤ U) (hg0 : ∀ t, 2 ≤ t → 0 ≤ g t)
    (hgc : ContinuousOn g (Ici 2)) (hmean : ∫ t in U..2 * U, g t ≤ K * U ^ (1 + η)) :
    ∫ t in U..2 * U, g t / t ≤ K * U ^ η := by
  have hU0 : 0 < U := by linarith
  have hsub : Icc U (2 * U) ⊆ Ici 2 := fun t ht => le_trans hU ht.1
  have hcont : ContinuousOn (fun t => g t / t) (Icc U (2 * U)) :=
    (hgc.mono hsub).div continuousOn_id (fun t ht => (by linarith [ht.1] : (0 : ℝ) < t).ne')
  have hle : ∫ t in U..2 * U, g t / t ≤ ∫ t in U..2 * U, g t / U := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (hcont.intervalIntegrable_of_Icc (by linarith))
      (((hgc.mono hsub).div_const U).intervalIntegrable_of_Icc (by linarith))
    intro t ht
    exact div_le_div_of_nonneg_left (hg0 t (hsub ht)) hU0 ht.1
  rw [intervalIntegral.integral_div] at hle
  calc ∫ t in U..2 * U, g t / t ≤ (∫ t in U..2 * U, g t) / U := hle
    _ ≤ K * U ^ (1 + η) / U := div_le_div_of_nonneg_right hmean hU0.le
    _ = K * U ^ η := by
      rw [Real.rpow_add hU0, Real.rpow_one]
      field_simp

/-- Dyadic summation: `∫_2^T g/t ≪ T^η`. -/
theorem dyadic_bound {g : ℝ → ℝ} {K η : ℝ} (hη : 0 < η) (hg0 : ∀ t, 2 ≤ t → 0 ≤ g t)
    (hgc : ContinuousOn g (Ici 2))
    (hmean : ∀ U, 2 ≤ U → ∫ t in U..2 * U, g t ≤ K * U ^ (1 + η)) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∫ t in (2 : ℝ)..T, g t / t ≤ C * T ^ η := by
  set r : ℝ := (2 : ℝ) ^ η with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hη
  have hK : 0 ≤ K := by
    have h2 := hmean 2 le_rfl
    have h0 : 0 ≤ ∫ t in (2 : ℝ)..2 * 2, g t :=
      intervalIntegral.integral_nonneg (by norm_num) (fun t ht => hg0 t ht.1)
    have hp : 0 < (2 : ℝ) ^ (1 + η) := by positivity
    nlinarith
  have hcont : ∀ a b : ℝ, 2 ≤ a → a ≤ b → IntervalIntegrable (fun t => g t / t) volume a b :=
    fun a b ha hab => ((hgc.mono (fun t ht => le_trans ha ht.1)).div continuousOn_id
      (fun t ht => (by linarith [ht.1] : (0 : ℝ) < t).ne')).intervalIntegrable_of_Icc hab
  -- `∫_2^{2^{n+1}} g/t ≤ K r^{n+1}/(r-1)`.
  have hgeom : ∀ n : ℕ, ∫ t in (2 : ℝ)..2 ^ (n + 1), g t / t ≤ K * r ^ (n + 1) / (r - 1) := by
    intro n
    induction n with
    | zero =>
      simp only [zero_add, pow_one, intervalIntegral.integral_same]
      have : 0 < r - 1 := by linarith
      positivity
    | succ n ih =>
      have h2n : (2 : ℝ) ≤ 2 ^ (n + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hcont 2 (2 ^ (n + 1)) le_rfl h2n)
        (hcont (2 ^ (n + 1)) (2 ^ (n + 1 + 1)) h2n (pow_le_pow_right₀ (by norm_num) (by omega)))
      rw [← hsplit]
      have hb := block_bound (K := K) (η := η) h2n hg0 hgc (hmean _ h2n)
      rw [show (2 : ℝ) * 2 ^ (n + 1) = 2 ^ (n + 1 + 1) by ring] at hb
      have hpow : ((2 : ℝ) ^ (n + 1)) ^ η = r ^ (n + 1) := by
        rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      rw [hpow] at hb
      have hr0 : 0 < r - 1 := by linarith
      have : K * r ^ (n + 1) / (r - 1) + K * r ^ (n + 1) = K * r ^ (n + 1 + 1) / (r - 1) := by
        field_simp
        ring
      linarith
  refine ⟨K * r / (r - 1), fun T hT => ?_⟩
  have hm : ⌊T⌋₊ ≠ 0 := by
    have := Nat.le_floor (show ((2 : ℕ) : ℝ) ≤ T by exact_mod_cast hT)
    omega
  set n := Nat.log 2 ⌊T⌋₊ with hn
  have hlow : (2 : ℝ) ^ n ≤ T := by
    calc (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hm
      _ ≤ T := Nat.floor_le (by linarith)
  have hhigh : T ≤ (2 : ℝ) ^ (n + 1) := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊T⌋₊
    have h2 : ⌊T⌋₊ + 1 ≤ 2 ^ (n + 1) := h1
    have h3 := Nat.lt_floor_add_one T
    have h4 : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h4
    linarith
  have hmono : ∫ t in (2 : ℝ)..T, g t / t ≤ ∫ t in (2 : ℝ)..2 ^ (n + 1), g t / t := by
    apply intervalIntegral.integral_mono_interval le_rfl hT hhigh
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact div_nonneg (hg0 t ht.1.le) (by linarith [ht.1])
    · exact hcont 2 _ le_rfl (by linarith)
  have hrn : r ^ n ≤ T ^ η := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact Real.rpow_le_rpow (by positivity) hlow hη.le
  have hr0 : 0 < r - 1 := by linarith
  calc ∫ t in (2 : ℝ)..T, g t / t ≤ K * r ^ (n + 1) / (r - 1) := hmono.trans (hgeom n)
    _ = K * r / (r - 1) * r ^ n := by rw [pow_succ]; field_simp
    _ ≤ K * r / (r - 1) * T ^ η := by
      apply mul_le_mul_of_nonneg_left hrn
      have : 0 < r := by linarith
      positivity

section Contour

variable {Z : ℂ → ℂ}

/-- The region `Re s > 1/2`, `s ≠ 1`. -/
def region : Set ℂ := {s : ℂ | (1 / 2 : ℝ) < s.re} \ {1}

theorem region_open : IsOpen region :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton

theorem mem_region {s : ℂ} (hre : (1 / 2 : ℝ) < s.re) (him : s.im ≠ 0) : s ∈ region :=
  ⟨hre, fun h => him (by rw [Set.mem_singleton_iff.mp h]; simp)⟩

theorem norm_cpow_div_le (X : ℝ) (hX : 0 < X) (s : ℂ) (w : ℂ) (T : ℝ) (hT : 0 < T)
    (hs : T ≤ |s.im|) :
    ‖w * (X : ℂ) ^ s / s‖ ≤ X ^ s.re * ‖w‖ / T := by
  have hsn : T ≤ ‖s‖ := hs.trans (Complex.abs_im_le_norm s)
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hT hsn
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, mul_comm ‖w‖]
  exact div_le_div_of_nonneg_left (by positivity) hT hsn

/-- Conjugation symmetry preserves the norm on the reflected point. -/
theorem norm_conj_point (hconj : ∀ s ∈ region, Z ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Z s))
    (x T : ℝ) (h : ((x : ℂ) + T * I) ∈ region) :
    ‖Z ((x : ℂ) + (-T : ℝ) * I)‖ = ‖Z ((x : ℂ) + T * I)‖ := by
  have hc : (starRingEnd ℂ) ((x : ℂ) + T * I) = (x : ℂ) + (-T : ℝ) * I := by
    apply Complex.ext <;> simp
  rw [← hc, hconj _ h, Complex.norm_conj]

/-- Dyadic summation on the line `Re s = β` (`β < 1`). -/
theorem left_bound {β K η : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hη : 0 < η)
    (hZc : ContinuousOn Z region)
    (hconj : ∀ s ∈ region, Z ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Z s))
    (hmean : ∀ U, 2 ≤ U → ∫ t in U..2 * U, ‖Z (β + t * I)‖ ≤ K * U ^ (1 + η)) :
    ∃ C : ℝ, ∀ X T : ℝ, 0 < X → 2 ≤ T →
      ∫ t in (-T)..T, ‖Z (β + t * I) * (X : ℂ) ^ ((β : ℂ) + t * I) / ((β : ℂ) + t * I)‖ ≤
        C * X ^ β * T ^ η := by
  have hline : ∀ t : ℝ, ((β : ℂ) + t * I) ∈ region := fun t =>
    ⟨by simp; linarith, fun h => by
      have := congrArg Complex.re (Set.mem_singleton_iff.mp h); simp at this; linarith⟩
  have hZline : Continuous fun t : ℝ => Z ((β : ℂ) + t * I) :=
    hZc.comp_continuous (by fun_prop) hline
  have hne : ∀ t : ℝ, ((β : ℂ) + t * I) ≠ 0 := fun t h => by
    have := congrArg Complex.re h; simp at this; linarith
  -- `h t = ‖Z(β+it)‖ / ‖β+it‖`
  set h : ℝ → ℝ := fun t => ‖Z ((β : ℂ) + t * I)‖ / ‖(β : ℂ) + t * I‖ with hh
  have hhc : Continuous h := hZline.norm.div (by fun_prop) (fun t => norm_ne_zero_iff.mpr (hne t))
  have heven : ∀ t, h (-t) = h t := by
    intro t
    simp only [hh]
    have h1 := norm_conj_point hconj β t (hline t)
    have h2 : ‖(β : ℂ) + ((-t : ℝ) : ℂ) * I‖ = ‖(β : ℂ) + t * I‖ := by
      rw [← Complex.norm_conj]; congr 1; apply Complex.ext <;> simp
    push_cast at h1 h2 ⊢
    rw [h1, h2]
  obtain ⟨C₁, hC₁⟩ := dyadic_bound (g := fun t => ‖Z ((β : ℂ) + t * I)‖) hη
    (fun t _ => norm_nonneg _) hZline.norm.continuousOn hmean
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).bddAbove_image hhc.continuousOn
  have hM0 : 0 ≤ M := le_trans (div_nonneg (norm_nonneg _) (norm_nonneg _)) (hM ⟨0, by norm_num, rfl⟩)
  refine ⟨2 * C₁ + 4 * M, fun X T hX hT => ?_⟩
  have hTη : 1 ≤ T ^ η := Real.one_le_rpow (by linarith) hη.le
  have hint : ∀ a b, IntervalIntegrable h volume a b := fun a b => hhc.intervalIntegrable a b
  have hnorm : ∀ t : ℝ, ‖Z (β + t * I) * (X : ℂ) ^ ((β : ℂ) + t * I) / ((β : ℂ) + t * I)‖ =
      X ^ β * h t := by
    intro t
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp [hh]; ring
  simp_rw [hnorm]
  rw [intervalIntegral.integral_const_mul]
  -- split `[-T, T] = [-T, -2] ∪ [-2, 2] ∪ [2, T]`
  have hsplit : ∫ t in (-T)..T, h t =
      (∫ t in (-T)..(-2), h t) + (∫ t in (-2 : ℝ)..2, h t) + ∫ t in (2 : ℝ)..T, h t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hneg : ∫ t in (-T)..(-2), h t = ∫ t in (2 : ℝ)..T, h t := by
    rw [← intervalIntegral.integral_comp_neg]
    simp_rw [heven]
  have hright : ∫ t in (2 : ℝ)..T, h t ≤ C₁ * T ^ η := by
    refine le_trans ?_ (hC₁ T hT)
    apply intervalIntegral.integral_mono_on hT (hint _ _)
    · exact (hZline.norm.continuousOn.div continuousOn_id
        (fun t ht => (by linarith [ht.1] : (0 : ℝ) < t).ne')).intervalIntegrable_of_Icc hT
    · intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      apply div_le_div_of_nonneg_left (norm_nonneg _) ht0
      calc t = |((β : ℂ) + t * I).im| := by simp [abs_of_pos ht0]
        _ ≤ ‖(β : ℂ) + t * I‖ := Complex.abs_im_le_norm _
  have hmid : ∫ t in (-2 : ℝ)..2, h t ≤ 4 * M := by
    have := intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2) (hint _ _)
      (intervalIntegrable_const (c := M)) (fun t ht => hM ⟨t, ht, rfl⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  rw [hsplit, hneg]
  have hXβ : 0 < X ^ β := Real.rpow_pos_of_pos hX β
  have : (∫ t in (2 : ℝ)..T, h t) + (∫ t in (-2 : ℝ)..2, h t) + ∫ t in (2 : ℝ)..T, h t ≤
      (2 * C₁ + 4 * M) * T ^ η := by nlinarith
  calc X ^ β * ((∫ t in (2 : ℝ)..T, h t) + (∫ t in (-2 : ℝ)..2, h t) + ∫ t in (2 : ℝ)..T, h t)
      ≤ X ^ β * ((2 * C₁ + 4 * M) * T ^ η) := mul_le_mul_of_nonneg_left this hXβ.le
    _ = (2 * C₁ + 4 * M) * X ^ β * T ^ η := by ring


/-- Clamp into `[a, b]`. -/
def clamp (a b x : ℝ) : ℝ := max a (min x b)

theorem continuous_clamp (a b : ℝ) : Continuous (clamp a b) := by
  unfold clamp; fun_prop

theorem clamp_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) : clamp a b x = x := by
  unfold clamp; rw [min_eq_left hx.2, max_eq_right hx.1]

theorem clamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clamp a b x ∈ Icc a b := by
  unfold clamp
  exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

/-- Averaging over `T ∈ [X, 2X]` bounds both horizontal integrals at some height. -/
theorem exists_height {β K η : ℝ} (hβ : 1 / 2 < β)
    (hZc : ContinuousOn Z region)
    (hconj : ∀ s ∈ region, Z ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Z s))
    (hmean : ∀ σ : ℝ, β ≤ σ → σ ≤ 2 → ∀ U, 2 ≤ U →
      ∫ t in U..2 * U, ‖Z (σ + t * I)‖ ≤ K * U ^ (1 + η))
    (X c : ℝ) (hX : 2 ≤ X) (hc : β < c) (hc2 : c ≤ 2) :
    ∃ T ∈ Icc X (2 * X),
      (∫ x in β..c, ‖Z (x + T * I) * (X : ℂ) ^ ((x : ℂ) + T * I) / ((x : ℂ) + T * I)‖ ≤
        K * (c - β) * X ^ (c - 1 + η)) ∧
      ∫ x in β..c, ‖Z (x + (-T : ℝ) * I) * (X : ℂ) ^ ((x : ℂ) + (-T : ℝ) * I) /
          ((x : ℂ) + (-T : ℝ) * I)‖ ≤ K * (c - β) * X ^ (c - 1 + η) := by
  have hX0 : 0 < X := by linarith
  have hK : 0 ≤ K := by
    have h2 := hmean β le_rfl (by linarith) 2 le_rfl
    have h0 : 0 ≤ ∫ t in (2 : ℝ)..2 * 2, ‖Z (β + t * I)‖ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)
    have hp : 0 < (2 : ℝ) ^ (1 + η) := by positivity
    nlinarith
  have hmemR : ∀ x T : ℝ, β ≤ x → 2 ≤ T → ((x : ℂ) + T * I) ∈ region := fun x T hx hT =>
    mem_region (by simp; linarith) (by simp; linarith)
  -- The clamped integrand `F T x = X^x ‖Z(x+iT)‖ / T`.
  set F : ℝ → ℝ → ℝ := fun T x =>
    X ^ clamp β c x * ‖Z ((clamp β c x : ℂ) + (clamp X (2 * X) T : ℝ) * I)‖ / clamp X (2 * X) T
    with hF
  have hclT : ∀ T, X ≤ clamp X (2 * X) T := fun T => (clamp_mem (by linarith) T).1
  have hFc : Continuous (Function.uncurry F) := by
    have hZ : Continuous fun p : ℝ × ℝ =>
        Z ((clamp β c p.2 : ℂ) + (clamp X (2 * X) p.1 : ℝ) * I) :=
      hZc.comp_continuous (by
        have := continuous_clamp β c; have := continuous_clamp X (2 * X); fun_prop)
        (fun p => hmemR _ _ (clamp_mem hc.le _).1 (by linarith [hclT p.1]))
    have hden : ∀ p : ℝ × ℝ, clamp X (2 * X) p.1 ≠ 0 := fun p => by linarith [hclT p.1]
    refine Continuous.div ?_ ((continuous_clamp X (2 * X)).comp continuous_fst) hden
    exact (Real.continuous_const_rpow hX0.ne').comp ((continuous_clamp β c).comp continuous_snd)
      |>.mul hZ.norm
  have hFeq : ∀ T ∈ Icc X (2 * X), ∀ x ∈ Icc β c,
      F T x = X ^ x * ‖Z ((x : ℂ) + T * I)‖ / T := by
    intro T hT x hx
    simp only [hF, clamp_of_mem hT, clamp_of_mem hx]
  set Φ : ℝ → ℝ := fun T => ∫ x in β..c, F T x with hΦ
  have hΦc : Continuous Φ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFc β c
  -- Average of `Φ` over `[X, 2X]`.
  have hswap : ∫ T in X..2 * X, Φ T = ∫ x in β..c, ∫ T in X..2 * X, F T x := by
    simp only [hΦ]
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le hc.le]
    simp_rw [intervalIntegral.integral_of_le hc.le, intervalIntegral.integral_of_le
      (show X ≤ 2 * X by linarith)]
    apply MeasureTheory.integral_integral_swap
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hinner : ∀ x ∈ Icc β c, ∫ T in X..2 * X, F T x ≤ X ^ c * (K * X ^ η) := by
    intro x hx
    have hcongr : ∫ T in X..2 * X, F T x = X ^ x * ∫ T in X..2 * X, ‖Z ((x : ℂ) + T * I)‖ / T := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro T hT
      rw [uIcc_of_le (by linarith)] at hT
      simp only [hFeq T hT x hx]
      ring
    rw [hcongr]
    have hgc : ContinuousOn (fun T : ℝ => ‖Z ((x : ℂ) + T * I)‖) (Ici 2) :=
      (hZc.comp (by fun_prop : Continuous fun T : ℝ => (x : ℂ) + T * I).continuousOn
        (fun T hT => hmemR x T hx.1 hT)).norm
    have hb := block_bound (g := fun T => ‖Z ((x : ℂ) + T * I)‖) (K := K) (η := η) hX
      (fun _ _ => norm_nonneg _) hgc (hmean x hx.1 (hx.2.trans hc2) X hX)
    have hxc : X ^ x ≤ X ^ c := Real.rpow_le_rpow_of_exponent_le (by linarith) hx.2
    exact mul_le_mul hxc hb (intervalIntegral.integral_nonneg (by linarith)
      (fun T hT => div_nonneg (norm_nonneg _) (by linarith [hT.1]))) (by positivity)
  have hinnerc : Continuous fun x => ∫ T in X..2 * X, F T x :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x T => F T x) (hFc.comp continuous_swap) X (2 * X)
  have havg : ∫ T in X..2 * X, Φ T ≤ K * (c - β) * X ^ (c - 1 + η) * (2 * X - X) := by
    rw [hswap]
    calc ∫ x in β..c, ∫ T in X..2 * X, F T x ≤ ∫ _x in β..c, X ^ c * (K * X ^ η) :=
          intervalIntegral.integral_mono_on hc.le (hinnerc.intervalIntegrable _ _)
            intervalIntegrable_const hinner
      _ = K * (c - β) * X ^ (c - 1 + η) * (2 * X - X) := by
          rw [intervalIntegral.integral_const, smul_eq_mul,
            show c - 1 + η = c + η - 1 by ring, Real.rpow_sub_one hX0.ne', Real.rpow_add hX0]
          field_simp
          ring
  obtain ⟨T, hT, hΦT⟩ := exists_le_of_integral_le (by linarith) hΦc.continuousOn havg
  have hT2 : 2 ≤ T := le_trans hX hT.1
  have hT0 : 0 < T := by linarith
  have hΦeq : Φ T = ∫ x in β..c, X ^ x * ‖Z ((x : ℂ) + T * I)‖ / T := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hc.le] at hx
    exact hFeq T hT x hx
  have hcpow : Continuous fun w : ℂ => (X : ℂ) ^ w :=
    continuous_const.cpow continuous_id (fun _ => Or.inl (by simpa using hX0))
  -- the two horizontal integrands are continuous on `[β, c]`
  have hcont : ∀ T' : ℝ, 2 ≤ |T'| → ContinuousOn (fun x : ℝ =>
      ‖Z ((x : ℂ) + T' * I) * (X : ℂ) ^ ((x : ℂ) + T' * I) / ((x : ℂ) + T' * I)‖) (Icc β c) := by
    intro T' hT'
    have hne : ∀ x : ℝ, ((x : ℂ) + T' * I) ≠ 0 := fun x h => by
      have := congrArg Complex.im h; simp at this; rw [this] at hT'; norm_num at hT'
    have hmem : ∀ x ∈ Icc β c, ((x : ℂ) + T' * I) ∈ region := fun x hx =>
      mem_region (by simp; linarith [hx.1]) (by
        simp; intro h; rw [h] at hT'; norm_num at hT')
    refine ContinuousOn.norm (ContinuousOn.div (ContinuousOn.mul
      (hZc.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + T' * I).continuousOn hmem)
      (hcpow.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + T' * I)).continuousOn)
      (by fun_prop) (fun x _ => hne x))
  have hbound : ∀ T' : ℝ, |T'| = T →
      ∫ x in β..c, ‖Z ((x : ℂ) + T' * I) * (X : ℂ) ^ ((x : ℂ) + T' * I) / ((x : ℂ) + T' * I)‖ ≤
        Φ T := by
    intro T' hT'
    rw [hΦeq]
    apply intervalIntegral.integral_mono_on hc.le
      ((hcont T' (by rw [hT']; exact hT2)).intervalIntegrable_of_Icc hc.le)
      ((Real.continuous_const_rpow hX0.ne').continuousOn.mul
        (hZc.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + T * I).continuousOn
          (fun x hx => hmemR x T hx.1 hT2)).norm |>.div_const T |>.intervalIntegrable_of_Icc hc.le)
    intro x hx
    have h1 := norm_cpow_div_le X hX0 ((x : ℂ) + T' * I) (Z ((x : ℂ) + T' * I)) T hT0
      (by simp [hT'])
    have hre : ((x : ℂ) + T' * I).re = x := by simp
    rw [hre] at h1
    have hZn : ‖Z ((x : ℂ) + T' * I)‖ = ‖Z ((x : ℂ) + T * I)‖ := by
      rcases abs_eq (by linarith : (0 : ℝ) ≤ T) |>.mp hT' with h | h
      · rw [h]
      · rw [h]; exact norm_conj_point hconj x T (hmemR x T hx.1 hT2)
    rw [hZn] at h1
    exact h1
  refine ⟨T, hT, (hbound T (abs_of_pos hT0)).trans hΦT, ?_⟩
  exact (hbound (-T) (by rw [abs_neg, abs_of_pos hT0])).trans hΦT

end Contour

end Cubic.Counting.HeightCoefficientContour
