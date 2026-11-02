import Cubic.BoxAsymptotic.BulkSum

/-!
# The bulk weight is `1` on the core and at most `1` everywhere

`w_bulk = Σ_{θ₀ ∈ {0, π}} Σ_{good (i, j)} φ(n/2^i) φ(τ_{θ₀} 2^j)`. For fixed `(n, τ)` the full
double sum over all `(i, j)` factors as `(Σ_i φ(n/2^i))(Σ_j φ(τ 2^j))`, each factor a
telescoping difference of values of `χ` in `[0, 1]`, and equal to `1` over a long enough
range. Only one centre contributes, since `τ₀ + τ_π = π`. On the *core*

  `n ≥ 4`, `0 < τ ≤ ε/8`, `46000 H ≤ ε² τ² n √n`, `n τ ≤ H/32`, `32 n ≤ H²`

(with `τ` the distance to the nearer centre) every piece with a nonzero term is good, so
`w_bulk = 1`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.Core

open Real
open CubicTargets.BoxAsymptotic (wrap)
open Cubic.BoxAsymptotic.SmoothPartition
open Cubic.BoxAsymptotic.Pieces (τof pw)
open Cubic.BoxAsymptotic.BulkW (Good)
open Cubic.BoxAsymptotic.GoodSet (G mem_G mem_G_of_good)
open Cubic.BoxAsymptotic.GoodSums (X Θ)
open Cubic.BoxAsymptotic.BulkSum (wb)
open scoped Classical

theorem wrap_add_int (x : ℝ) (k : ℤ) : wrap (x + 2 * π * k) = wrap x := by
  simp only [wrap]
  rw [show 2 * π * (k : ℝ) = k • (2 * π) by rw [zsmul_eq_mul]; ring]
  exact toIocMod_add_zsmul _ _ _ _

/-- `τ₀ + τ_π = π`. -/
theorem tau_sum (t : ℝ) : τof 0 t + τof π t = π := by
  simp only [τof, sub_zero]
  set w := wrap t
  have hw : -π < w ∧ w ≤ π := by
    have := toIocMod_mem_Ioc two_pi_pos (-π) t
    exact ⟨this.1, by have h2 : w ≤ -π + 2 * π := this.2; linarith⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t = w + 2 * π * k :=
    ⟨toIocDiv two_pi_pos (-π) t, by simp only [w, wrap, toIocMod, zsmul_eq_mul]; ring⟩
  have hwπ : wrap (t - π) = wrap (w - π) := by
    rw [hk, show w + 2 * π * k - π = w - π + 2 * π * k by ring, wrap_add_int]
  rw [hwπ]
  rcases le_or_gt w 0 with h | h
  · have : wrap (w - π) = w + π := by
      rw [show w - π = w + π + 2 * π * (-1 : ℤ) by push_cast; ring, wrap_add_int]
      exact Cubic.BoxAsymptotic.PartitionIntegrals.wrap_eq_self
        ⟨by linarith [hw.1], by linarith⟩
    rw [this, abs_of_nonpos h, abs_of_pos (by linarith [hw.1])]; ring
  · have : wrap (w - π) = w - π :=
      Cubic.BoxAsymptotic.PartitionIntegrals.wrap_eq_self ⟨by linarith, by linarith [hw.2]⟩
    rw [this, abs_of_pos h, abs_of_nonpos (by linarith [hw.2])]; ring

theorem pw_eq (p : ℕ × ℕ) (θ₀ n t : ℝ) :
    pw (X p) (Θ p) θ₀ n t = φ (n / 2 ^ p.1) * φ (τof θ₀ t * 2 ^ p.2) := by
  simp only [pw, X, Θ]
  congr 2
  rw [one_div_pow, div_div_eq_mul_div, div_one]

/-- The full double sum over a box factors. -/
theorem box_sum (u τ : ℝ) (M M' : ℕ) :
    ∑ p ∈ Finset.Icc 0 M ×ˢ Finset.Icc 0 M', φ (u / 2 ^ p.1) * φ (τ * 2 ^ p.2) =
      (χ (u / 2 ^ M) - χ (2 * u / 2 ^ 0)) * (χ (τ * 2 ^ 0) - χ (τ * 2 ^ (M' + 1))) := by
  rw [Finset.sum_product, ← sum_φ_norm u (Nat.zero_le M), ← sum_φ_angle τ (Nat.zero_le M'),
    Finset.sum_mul_sum]

theorem χ_diff_mem (a b : ℝ) (hab : a ≤ b) : 0 ≤ χ a - χ b ∧ χ a - χ b ≤ 1 :=
  ⟨by linarith [χ_anti hab], by linarith [χ_le_one a, χ_nonneg b]⟩

/-- A sum of piece weights over any finite set is at most `1`. -/
theorem sum_le_one {u τ : ℝ} (hu : 0 < u) (hτ : 0 < τ) (S : Finset (ℕ × ℕ)) :
    ∑ p ∈ S, φ (u / 2 ^ p.1) * φ (τ * 2 ^ p.2) ≤ 1 := by
  set M := ⌈2 * u⌉₊
  set M' := ⌈2 / τ⌉₊
  have hsupp : ∀ p ∈ S, φ (u / 2 ^ p.1) * φ (τ * 2 ^ p.2) ≠ 0 →
      p ∈ Finset.Icc 0 M ×ˢ Finset.Icc 0 M' := by
    intro p _ hp
    have h1 : φ (u / 2 ^ p.1) ≠ 0 := fun h => hp (by rw [h, zero_mul])
    have h2 : φ (τ * 2 ^ p.2) ≠ 0 := fun h => hp (by rw [h, mul_zero])
    have a := φ_support h1
    have b := φ_support h2
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨Nat.zero_le _, ?_⟩, Nat.zero_le _, ?_⟩
    · have : (2 : ℝ) ^ p.1 ≤ 2 * u := by
        have := a.1; rw [le_div_iff₀ (by positivity)] at this; linarith
      have : (p.1 : ℝ) ≤ 2 * u := (by exact_mod_cast (Nat.lt_two_pow_self).le :
        ((p.1 : ℕ) : ℝ) ≤ 2 ^ p.1).trans this
      exact_mod_cast this.trans (Nat.le_ceil _)
    · have : (2 : ℝ) ^ p.2 ≤ 2 / τ := by
        rw [le_div_iff₀ hτ]; linarith [b.2]
      have : (p.2 : ℝ) ≤ 2 / τ := (by exact_mod_cast (Nat.lt_two_pow_self).le :
        ((p.2 : ℕ) : ℝ) ≤ 2 ^ p.2).trans this
      exact_mod_cast this.trans (Nat.le_ceil _)
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ φ (u / 2 ^ p.1) * φ (τ * 2 ^ p.2) := fun p =>
    mul_nonneg (φ_nonneg _) (φ_nonneg _)
  calc ∑ p ∈ S, φ (u / 2 ^ p.1) * φ (τ * 2 ^ p.2)
      = ∑ p ∈ S.filter (fun p => φ (u / 2 ^ p.1) * φ (τ * 2 ^ p.2) ≠ 0),
          φ (u / 2 ^ p.1) * φ (τ * 2 ^ p.2) := by
        rw [Finset.sum_filter_ne_zero]
    _ ≤ ∑ p ∈ Finset.Icc 0 M ×ˢ Finset.Icc 0 M', φ (u / 2 ^ p.1) * φ (τ * 2 ^ p.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp => hsupp p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
          (fun p _ _ => hnn p)
    _ ≤ 1 := by
        rw [box_sum]
        obtain ⟨a0, a1⟩ := χ_diff_mem (u / 2 ^ M) (2 * u / 2 ^ 0) (by
          rw [pow_zero, div_one]
          have : u / 2 ^ M ≤ u := div_le_self hu.le (one_le_pow₀ (by norm_num))
          linarith)
        obtain ⟨b0, b1⟩ := χ_diff_mem (τ * 2 ^ 0) (τ * 2 ^ (M' + 1)) (by
          rw [pow_zero, mul_one]
          exact le_mul_of_one_le_right hτ.le (one_le_pow₀ (by norm_num)))
        calc (χ (u / 2 ^ M) - χ (2 * u / 2 ^ 0)) * (χ (τ * 2 ^ 0) - χ (τ * 2 ^ (M' + 1)))
            ≤ 1 * 1 := mul_le_mul a1 b1 b0 (by norm_num)
          _ = 1 := by norm_num


theorem wb_eq (H ε θ₀ n t : ℝ) :
    wb H ε θ₀ n t = ∑ p ∈ G H ε, φ (n / 2 ^ p.1) * φ (τof θ₀ t * 2 ^ p.2) := by
  simp only [wb, pw_eq]

theorem wb_nonneg (H ε θ₀ n t : ℝ) : 0 ≤ wb H ε θ₀ n t := by
  rw [wb_eq]; exact Finset.sum_nonneg fun p _ => mul_nonneg (φ_nonneg _) (φ_nonneg _)

/-- If some good piece sees `τ`, then `τ ≤ 1/2`. -/
theorem small_of_wb {H ε θ₀ n t : ℝ} (h : wb H ε θ₀ n t ≠ 0) : τof θ₀ t ≤ 1 / 2 := by
  rw [wb_eq] at h
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h2 : φ (τof θ₀ t * 2 ^ p.2) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  have b := φ_support h2
  have hj := (mem_G hp).hj
  have : (4 : ℝ) ≤ 2 ^ p.2 := by
    have : (2 : ℝ) ^ 2 ≤ 2 ^ p.2 := pow_le_pow_right₀ (by norm_num) hj
    norm_num at this; exact this
  have ht : 0 ≤ τof θ₀ t := abs_nonneg _
  nlinarith [b.2]

theorem wb_zero_of_zero {H ε θ₀ n t : ℝ} (h : τof θ₀ t = 0) : wb H ε θ₀ n t = 0 := by
  rw [wb_eq]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [h, zero_mul, φ_eq_zero_of_le (u := 0) (by norm_num), mul_zero]

/-- `0 ≤ w_bulk ≤ 1`. -/
theorem wb_total_le {H ε n t : ℝ} (hn : 0 < n) :
    0 ≤ wb H ε 0 n t + wb H ε π n t ∧ wb H ε 0 n t + wb H ε π n t ≤ 1 := by
  refine ⟨add_nonneg (wb_nonneg _ _ _ _ _) (wb_nonneg _ _ _ _ _), ?_⟩
  have hs := tau_sum t
  have hle : ∀ θ₀, wb H ε θ₀ n t ≤ 1 := fun θ₀ => by
    rcases eq_or_lt_of_le (abs_nonneg (wrap (t - θ₀))) with h0 | h0
    · rw [wb_zero_of_zero (show τof θ₀ t = 0 from h0.symm)]; norm_num
    · rw [wb_eq]; exact sum_le_one hn h0 _
  by_cases h0 : wb H ε 0 n t = 0
  · rw [h0, zero_add]; exact hle π
  · have h1 := small_of_wb h0
    have : wb H ε π n t = 0 := by
      by_contra hπ
      have := small_of_wb hπ
      linarith [Real.pi_gt_three]
    rw [this, add_zero]; exact hle 0

/-- The core. -/
structure InCore (H ε n τ : ℝ) : Prop where
  hn : 4 ≤ n
  hτ : 0 < τ
  h1 : τ ≤ ε / 8
  h2 : 46000 * H ≤ ε ^ 2 * τ ^ 2 * (n * Real.sqrt n)
  h3 : n * τ ≤ H / 32
  h4 : 32 * n ≤ H ^ 2

/-- On the core every piece with a nonzero term is good. -/
theorem good_of_core {H ε n τ : ℝ} (hc : InCore H ε n τ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (hH : 0 < H) {i j : ℕ}
    (hi : φ (n / 2 ^ i) ≠ 0) (hj : φ (τ * 2 ^ j) ≠ 0) : Good H ε i j := by
  have a := φ_support hi
  have b := φ_support hj
  have hX : (0 : ℝ) < 2 ^ i := by positivity
  have hT : (0 : ℝ) < 2 ^ j := by positivity
  have hn0 : 0 < n := by linarith [hc.hn]
  have hτ := hc.hτ
  -- `n/2 ≤ 2^i ≤ 2n` and `τ/2 ≤ 2^{-j} ≤ 2τ`
  have hX1 : n / 2 ≤ 2 ^ i := by have := a.2; rw [div_le_iff₀ hX] at this; linarith
  have hX2 : (2 : ℝ) ^ i ≤ 2 * n := by have := a.1; rw [le_div_iff₀ hX] at this; linarith
  have eΘ : ((1 : ℝ) / 2) ^ j = 1 / 2 ^ j := by rw [one_div_pow]
  have hΘ1 : τ / 2 ≤ (1 / 2 : ℝ) ^ j := by
    rw [eΘ, le_div_iff₀ hT]; linarith [b.2]
  have hΘ2 : (1 / 2 : ℝ) ^ j ≤ 2 * τ := by
    rw [eΘ, div_le_iff₀ hT]; linarith [b.1]
  have hΘ0 : (0 : ℝ) < (1 / 2) ^ j := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `i ≥ 1`
    by_contra h; push_neg at h
    have : i = 0 := by omega
    subst this; norm_num at hX2 hX1; linarith [hc.hn]
  · -- `j ≥ 2`
    by_contra h; push_neg at h
    have : (1 / 2 : ℝ) ≤ (1 / 2) ^ j := by
      calc (1 / 2 : ℝ) = (1 / 2) ^ 1 := by norm_num
        _ ≤ (1 / 2) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [hc.h1]
  · linarith [hc.h1]
  · -- `2000 H ≤ ε² Θ² X √X`
    have hsq : Real.sqrt n / Real.sqrt 2 ≤ Real.sqrt (2 ^ i) := by
      rw [← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt hX1
    have hs2 : Real.sqrt 2 ≤ 1.415 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hs2' : 0 < Real.sqrt 2 := by positivity
    have hΘsq : τ ^ 2 / 4 ≤ ((1 / 2 : ℝ) ^ j) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hΘ1 2
      rw [div_pow] at this; norm_num at this ⊢; linarith
    have hXX : n * Real.sqrt n / (2 * Real.sqrt 2) ≤ 2 ^ i * Real.sqrt (2 ^ i) := by
      have := mul_le_mul hX1 hsq (by positivity) (by positivity)
      calc n * Real.sqrt n / (2 * Real.sqrt 2) = n / 2 * (Real.sqrt n / Real.sqrt 2) := by
            field_simp
        _ ≤ _ := this
    have key : ε ^ 2 * (τ ^ 2 / 4) * (n * Real.sqrt n / (2 * Real.sqrt 2)) ≤
        ε ^ 2 * ((1 / 2 : ℝ) ^ j) ^ 2 * (2 ^ i * Real.sqrt (2 ^ i)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hΘsq (by positivity)) hXX (by positivity)
        (by positivity)
    have e : ε ^ 2 * (τ ^ 2 / 4) * (n * Real.sqrt n / (2 * Real.sqrt 2)) =
        ε ^ 2 * τ ^ 2 * (n * Real.sqrt n) / (8 * Real.sqrt 2) := by field_simp; ring
    rw [e] at key
    have h2 := hc.h2
    have : 2000 * H ≤ ε ^ 2 * τ ^ 2 * (n * Real.sqrt n) / (8 * Real.sqrt 2) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  · -- `X Θ ≤ H/8`
    have := mul_le_mul hX2 hΘ2 hΘ0.le (by linarith)
    have := hc.h3
    nlinarith
  · linarith [hc.h4]


/-- The centre sum is `1` on the core. -/
theorem wb_eq_one {H ε n t θ₀ : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (hc : InCore H ε n (τof θ₀ t)) : wb H ε θ₀ n t = 1 := by
  set τ := τof θ₀ t
  have hn := hc.hn
  have hτ := hc.hτ
  have hH0 : 0 < H := by linarith
  rw [wb_eq]
  set f : ℕ × ℕ → ℝ := fun p => φ (n / 2 ^ p.1) * φ (τ * 2 ^ p.2)
  set M := ⌈2 * n⌉₊
  set M' := ⌈2 / τ⌉₊
  set P := Finset.Icc 0 M ×ˢ Finset.Icc 0 M'
  have hP : ∑ p ∈ P, f p = 1 := by
    simp only [f, P]
    rw [box_sum]
    have hM : (2 * n : ℝ) ≤ 2 ^ M := (Nat.le_ceil _).trans
      (by exact_mod_cast (Nat.lt_two_pow_self).le)
    have hM' : 2 / τ ≤ (2 : ℝ) ^ M' := (Nat.le_ceil _).trans
      (by exact_mod_cast (Nat.lt_two_pow_self).le)
    rw [χ_eq_one (by rw [div_le_one (by positivity)]; linarith),
      χ_eq_zero (by rw [pow_zero, div_one]; linarith),
      χ_eq_one (by rw [pow_zero, mul_one]; linarith [hc.h1]),
      χ_eq_zero (by
        rw [pow_succ, ← mul_assoc]
        have : 2 ≤ τ * 2 ^ M' := by rw [div_le_iff₀ hτ] at hM'; linarith
        linarith)]
    norm_num
  have hsupp : ∀ p : ℕ × ℕ, f p ≠ 0 → p ∈ P := by
    intro p hp
    have h1 : φ (n / 2 ^ p.1) ≠ 0 := fun h => hp (by simp only [f, h, zero_mul])
    have h2 : φ (τ * 2 ^ p.2) ≠ 0 := fun h => hp (by simp only [f, h, mul_zero])
    have a := φ_support h1
    have b := φ_support h2
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨Nat.zero_le _, ?_⟩, Nat.zero_le _, ?_⟩
    · have : (2 : ℝ) ^ p.1 ≤ 2 * n := by
        have := a.1; rw [le_div_iff₀ (by positivity)] at this; linarith
      have : (p.1 : ℝ) ≤ 2 * n := (by exact_mod_cast (Nat.lt_two_pow_self).le :
        ((p.1 : ℕ) : ℝ) ≤ 2 ^ p.1).trans this
      exact_mod_cast this.trans (Nat.le_ceil _)
    · have : (2 : ℝ) ^ p.2 ≤ 2 / τ := by
        rw [le_div_iff₀ hτ]; linarith [b.2]
      have : (p.2 : ℝ) ≤ 2 / τ := (by exact_mod_cast (Nat.lt_two_pow_self).le :
        ((p.2 : ℕ) : ℝ) ≤ 2 ^ p.2).trans this
      exact_mod_cast this.trans (Nat.le_ceil _)
  have hG : ∀ p : ℕ × ℕ, f p ≠ 0 → p ∈ G H ε := by
    intro p hp
    have h1 : φ (n / 2 ^ p.1) ≠ 0 := fun h => hp (by simp only [f, h, zero_mul])
    have h2 : φ (τ * 2 ^ p.2) ≠ 0 := fun h => hp (by simp only [f, h, mul_zero])
    exact mem_G_of_good hH hε0 hε1 (good_of_core hc hε0 hε1 hH0 h1 h2)
  rw [← hP, ← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (s := P)]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨-, hp⟩; exact ⟨hsupp p hp, hp⟩
  · rintro ⟨-, hp⟩; exact ⟨hG p hp, hp⟩

/-- **`w_bulk = 1` on the core.** -/
theorem wb_total_eq_one {H ε n t θ₀ : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (hθ₀ : θ₀ = 0 ∨ θ₀ = π) (hc : InCore H ε n (τof θ₀ t)) :
    wb H ε 0 n t + wb H ε π n t = 1 := by
  have hs := tau_sum t
  have hsmall : τof θ₀ t ≤ 1 / 80 := by linarith [hc.h1]
  rcases hθ₀ with rfl | rfl
  · rw [wb_eq_one hH hε0 hε1 hc]
    have : wb H ε π n t = 0 := by
      by_contra h; have := small_of_wb h; linarith [Real.pi_gt_three]
    rw [this, add_zero]
  · rw [wb_eq_one hH hε0 hε1 hc]
    have : wb H ε 0 n t = 0 := by
      by_contra h; have := small_of_wb h; linarith [Real.pi_gt_three]
    rw [this, zero_add]

end Cubic.BoxAsymptotic.Core
