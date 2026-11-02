import Cubic.BoxAsymptotic.Pieces
import Cubic.BoxAsymptotic.TraceAsymptotic

/-!
# `W` on the support of a good piece (`eq:width`, `eq:bulk`)

A piece `(i, j)`, `X = 2^i`, `Θ = 2^{-j}`, is *good* if

  `2 ≤ j`, `Θ ≤ ε/4`, `2000 H ≤ ε² Θ² X √X`, `X Θ ≤ H/8`, `16 X ≤ H²`

This is a coupled choice of logarithmic buffers for the same truncation as
`eq:bulk`, rather than its literal range. `GoodCount.J_bound` controls the
change of angular logarithmic length by `O(log(1/ε))`; `Discard` and `BulkSum`
prove the discarded-count and smoothing-error bounds for this choice.
On its support `X/2 ≤ n ≤ 2X`,
`Θ/2 ≤ τ ≤ 2Θ` (with `τ` the distance of `θ` to `θ₀ ∈ {0, π}`) the hypotheses of
`TraceAsymptotic.W_bulk` hold with `c = 1 - cos τ`, and comparing `√(2c)` with `τ` gives

  `|W_H(n, θ) - 18√3 H/(nτ)| ≤ 14 ε · 18√3 H/(nτ)`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.BulkW

open Real MeasureTheory
open CubicTargets.BoxAsymptotic (wrap)
open Cubic.BoxAsymptotic.TraceWidth (E W Q)
open Cubic.BoxAsymptotic.TraceAsymptotic (Bulk W_bulk m sV)
open Cubic.BoxAsymptotic.Pieces (τof)

/-- A good piece. -/
structure Good (H ε : ℝ) (i j : ℕ) : Prop where
  hi : 1 ≤ i
  hj : 2 ≤ j
  g1 : (1 / 2 : ℝ) ^ j ≤ ε / 4
  g2 : 2000 * H ≤ ε ^ 2 * ((1 / 2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ i * Real.sqrt (2 ^ i))
  g3 : (2 : ℝ) ^ i * (1 / 2) ^ j ≤ H / 8
  g4 : 16 * (2 : ℝ) ^ i ≤ H ^ 2

/-- `W` is unchanged by `θ ↦ θ - π`. -/
theorem W_sub_pi (H n θ : ℝ) : W H n (θ - Real.pi) = W H n θ := by
  have hE : E H n (θ - Real.pi) = (fun s : ℝ => -s) ⁻¹' E H n θ := by
    ext s
    simp only [E, Q, Set.mem_preimage, Set.mem_setOf_eq, abs_neg, neg_sq, Real.cos_sub_pi]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, h2, ?_⟩ <;>
      [rw [← abs_neg]; rw [← abs_neg]] <;> convert h3 using 2 <;> ring
  rw [W, W, hE]
  have := Real.volume_preimage_mul_left (a := -1) (by norm_num) (E H n θ)
  simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, ENNReal.ofReal_one, one_mul] at this
  rw [this]

theorem cos_wrap (x : ℝ) : Real.cos (wrap x) = Real.cos x := by
  simp only [wrap]
  rw [toIocMod, zsmul_eq_mul, show x - (toIocDiv two_pi_pos (-π) x : ℝ) * (2 * π) =
    x - ((toIocDiv two_pi_pos (-π) x : ℤ) : ℝ) * (2 * π) from rfl, Real.cos_sub_int_mul_two_pi]

theorem abs_wrap_le (x : ℝ) : |wrap x| ≤ π := by
  have h := toIocMod_mem_Ioc two_pi_pos (-π) x
  simp only [wrap]
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

/-- `cos θ = cos τ` for `θ₀ ∈ {0, π}` after the symmetry. -/
theorem cos_τ (θ : ℝ) : Real.cos (θ - 0) = Real.cos (τof 0 θ) ∧
    Real.cos (θ - Real.pi) = Real.cos (τof Real.pi θ) := by
  simp only [τof]
  constructor
  · rw [Real.cos_abs, cos_wrap]
  · rw [Real.cos_abs, cos_wrap]


theorem pi_sq_lt : Real.pi ^ 2 < 9.87 := by
  have := Real.pi_lt_d4; have := Real.pi_pos; nlinarith

/-- The bulk hypotheses on the support of a good piece. -/
theorem bulk_of_good {H ε n τ : ℝ} {i j : ℕ} (hg : Good H ε i j) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 10) (hH : 1 ≤ H) (hn1 : (2 : ℝ) ^ i / 2 ≤ n) (hn2 : n ≤ 2 * 2 ^ i)
    (hτ1 : (1 / 2 : ℝ) ^ j / 2 ≤ τ) (hτ2 : τ ≤ 2 * (1 / 2) ^ j) :
    Bulk H (Real.sqrt n) (1 - Real.cos τ) ε := by
  set X : ℝ := 2 ^ i
  set Θ : ℝ := (1 / 2) ^ j
  have hX : 0 < X := by positivity
  have hΘ : 0 < Θ := by positivity
  have hn : 0 < n := by linarith
  have hτ : 0 < τ := by linarith
  have hτε : τ ≤ ε / 2 := by linarith [hg.g1]
  have hτπ : |τ| ≤ Real.pi := by rw [abs_of_pos hτ]; linarith [Real.pi_gt_three]
  set c := 1 - Real.cos τ
  have hcup : c ≤ τ ^ 2 / 2 := by simp only [c]; linarith [Real.one_sub_sq_div_two_le_cos (x := τ)]
  have hclow : 2 * τ ^ 2 / Real.pi ^ 2 ≤ c := Cubic.BoxAsymptotic.Bands.one_sub_cos_ge hτπ
  have hpi := pi_sq_lt
  have hpi0 : 0 < Real.pi ^ 2 := by positivity
  have hc : 0 < c := lt_of_lt_of_le (by positivity) hclow
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  refine ⟨Real.sqrt_pos.mpr hn, hε0, hε1, hc, ?_, ?_, ?_, ?_⟩
  · -- `c ≤ ε²`
    nlinarith
  · -- `27 H ≤ ε² r³ c`
    have hr3 : Real.sqrt n ^ 3 = n * Real.sqrt n := by rw [pow_succ, hsq]
    have hsqn : Real.sqrt X / Real.sqrt 2 ≤ Real.sqrt n := by
      rw [← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt 2 ≤ 1.415 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
    -- `n √n ≥ X √X / (2 √2)`
    have hn3 : X * Real.sqrt X / (2 * Real.sqrt 2) ≤ n * Real.sqrt n := by
      have := mul_le_mul hn1 hsqn (by positivity) hn.le
      calc X * Real.sqrt X / (2 * Real.sqrt 2) = X / 2 * (Real.sqrt X / Real.sqrt 2) := by
            field_simp
        _ ≤ _ := this
    -- `c ≥ Θ²/(2π²)`
    have hcΘ : Θ ^ 2 / (2 * Real.pi ^ 2) ≤ c := by
      refine le_trans ?_ hclow
      rw [div_le_div_iff₀ (by positivity) hpi0]
      have h1 : Θ ^ 2 ≤ 4 * τ ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right h1 hpi0.le
      nlinarith
    have key : ε ^ 2 * (X * Real.sqrt X / (2 * Real.sqrt 2)) * (Θ ^ 2 / (2 * Real.pi ^ 2)) ≤
        ε ^ 2 * Real.sqrt n ^ 3 * c := by
      rw [hr3]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hn3 (by positivity)) hcΘ (by positivity)
        (by positivity)
    have e : ε ^ 2 * (X * Real.sqrt X / (2 * Real.sqrt 2)) * (Θ ^ 2 / (2 * Real.pi ^ 2)) =
        (ε ^ 2 * Θ ^ 2 * (X * Real.sqrt X)) / (4 * Real.sqrt 2 * Real.pi ^ 2) := by
      field_simp; ring
    rw [e] at key
    have hg2 : 2000 * H ≤ ε ^ 2 * Θ ^ 2 * (X * Real.sqrt X) := hg.g2
    have hden : 4 * Real.sqrt 2 * Real.pi ^ 2 ≤ 56 := by nlinarith
    have : 27 * H ≤ (ε ^ 2 * Θ ^ 2 * (X * Real.sqrt X)) / (4 * Real.sqrt 2 * Real.pi ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : 27 * H * (4 * Real.sqrt 2 * Real.pi ^ 2) ≤ 27 * H * 56 :=
        mul_le_mul_of_nonneg_left hden (by linarith)
      linarith
    linarith
  · -- `r² √c ≤ H/2`
    rw [hsq]
    have hsc : Real.sqrt c ≤ τ := by
      rw [Real.sqrt_le_left hτ.le]; nlinarith
    have : X * Θ ≤ H / 8 := hg.g3
    have : n * Real.sqrt c ≤ 2 * X * (2 * Θ) :=
      mul_le_mul hn2 (hsc.trans hτ2) (Real.sqrt_nonneg _) (by positivity)
    linarith
  · -- `2 r ≤ H`
    have h4 : 16 * X ≤ H ^ 2 := hg.g4
    have : Real.sqrt n ≤ H / 2 := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    linarith


/-- **`W` on a good piece**: `|W - 18√3 H/(nτ)| ≤ 14 ε · 18√3 H/(nτ)`. -/
theorem W_compare {H ε n τ θ : ℝ} {i j : ℕ} (hg : Good H ε i j) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 10) (hH : 1 ≤ H) (hn1 : (2 : ℝ) ^ i / 2 ≤ n) (hn2 : n ≤ 2 * 2 ^ i)
    (hτ1 : (1 / 2 : ℝ) ^ j / 2 ≤ τ) (hτ2 : τ ≤ 2 * (1 / 2) ^ j)
    (hcos : Real.cos θ = Real.cos τ) :
    |W H n θ - 18 * Real.sqrt 3 * H / (n * τ)| ≤ 14 * ε * (18 * Real.sqrt 3 * H / (n * τ)) := by
  have hb := bulk_of_good hg hε0 hε1 hH hn1 hn2 hτ1 hτ2
  have hn : 0 < n := by have : (0 : ℝ) < 2 ^ i := by positivity
                        linarith
  have hτ : 0 < τ := by have : (0 : ℝ) < (1 / 2) ^ j := by positivity
                        linarith
  have hτε : τ ≤ ε / 2 := by linarith [hg.g1]
  have hτ1' : |τ| ≤ 1 := by rw [abs_of_pos hτ]; linarith
  set c := 1 - Real.cos τ with hc
  set r := Real.sqrt n
  have hr : 0 < r := Real.sqrt_pos.mpr hn
  have hrn : r ^ 2 = n := Real.sq_sqrt hn.le
  have hW := W_bulk hb (by rw [hcos]; ring)
  rw [hrn] at hW
  -- `2m = 18√3 H/(n s)` with `s = √(2c)`
  set s := Real.sqrt (2 * c)
  have hc0 : 0 < c := hb.hc
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have h3 : 0 < Real.sqrt 3 := by positivity
  have hsV : sV r c = r * s / Real.sqrt 3 := by
    simp only [sV, s]
    rw [show 2 / 3 * r ^ 2 * c = r ^ 2 * (2 * c) / 3 by ring, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
  have hm2 : 2 * m H r c = 18 * Real.sqrt 3 * H / (n * s) := by
    simp only [m]; rw [hsV, ← hrn]; field_simp; ring
  -- `τ (1 - τ²/8) ≤ s ≤ τ`
  have hcb := Real.cos_bound hτ1'
  rw [abs_of_pos hτ] at hcb
  have hcup : c ≤ τ ^ 2 / 2 := by simp only [c]; linarith [Real.one_sub_sq_div_two_le_cos (x := τ)]
  have hclow : τ ^ 2 - 5 * τ ^ 4 / 48 ≤ 2 * c := by
    simp only [c]; have := (abs_le.mp hcb).2; linarith
  have hτsq : τ ^ 2 ≤ 1 / 400 := by
    have := pow_le_pow_left₀ hτ.le (hτε.trans (by linarith : ε / 2 ≤ 1 / 20)) 2
    norm_num at this ⊢; linarith
  have h4 : τ ^ 4 ≤ τ ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hτsq.trans (by norm_num : (1 / 400 : ℝ) ≤ 1))
      (sq_nonneg τ)
    nlinarith [this]
  have h6 : τ ^ 6 ≤ τ ^ 4 := by
    have := mul_le_mul_of_nonneg_left (hτsq.trans (by norm_num : (1 / 400 : ℝ) ≤ 1))
      (pow_nonneg hτ.le 4)
    nlinarith [this]
  have hsup : s ≤ τ := by rw [Real.sqrt_le_left hτ.le]; linarith
  have hx0 : 0 ≤ τ * (1 - τ ^ 2 / 8) := mul_nonneg hτ.le (by linarith)
  have hslow : τ * (1 - τ ^ 2 / 8) ≤ s := by
    rw [Real.le_sqrt hx0 (by linarith)]
    have e : (τ * (1 - τ ^ 2 / 8)) ^ 2 = τ ^ 2 - τ ^ 4 / 4 + τ ^ 6 / 64 := by ring
    rw [e]; linarith
  set M₀ := 18 * Real.sqrt 3 * H / (n * τ)
  have hM₀ : 0 < M₀ := by have : (0 : ℝ) < H := by linarith
                          positivity
  have hk : 2 * m H r c = M₀ * (τ / s) := by
    rw [hm2]; simp only [M₀]; field_simp
  have hk1 : 1 ≤ τ / s := by rw [le_div_iff₀ hs]; linarith
  have hk2 : τ / s ≤ 1 + τ ^ 2 / 4 := by
    rw [div_le_iff₀ hs]
    have := mul_le_mul_of_nonneg_left hslow (by positivity : (0 : ℝ) ≤ 1 + τ ^ 2 / 4)
    have e : (1 + τ ^ 2 / 4) * (τ * (1 - τ ^ 2 / 8)) = τ + τ * (τ ^ 2 / 8) - τ * (τ ^ 4 / 32) := by
      ring
    have : τ * (τ ^ 4 / 32) ≤ τ * (τ ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) hτ.le
    linarith
  have hε2 : ε * ε ≤ ε * (1 / 10) := mul_le_mul_of_nonneg_left hε1 hε0.le
  have hτ2' : τ ^ 2 / 4 ≤ ε / 100 := by
    have := pow_le_pow_left₀ hτ.le hτε 2
    have e : (ε / 2) ^ 2 = ε * ε / 4 := by ring
    linarith
  have hmM : m H r c ≤ M₀ := by
    have : M₀ * (τ / s) ≤ M₀ * 2 := mul_le_mul_of_nonneg_left (by linarith) hM₀.le
    linarith
  have hεm := mul_le_mul_of_nonneg_left hmM hε0.le
  rw [abs_le] at hW ⊢
  constructor
  · have h1 := hW.1
    have : M₀ ≤ 2 * m H r c := by
      rw [hk]; have := mul_le_mul_of_nonneg_left hk1 hM₀.le; linarith
    linarith
  · have h1 := hW.2
    have : 2 * m H r c ≤ M₀ * (1 + ε / 100) := by
      rw [hk]; exact mul_le_mul_of_nonneg_left (by linarith) hM₀.le
    have e : M₀ * (1 + ε / 100) = M₀ + ε * M₀ / 100 := by ring
    have : 0 ≤ ε * M₀ := by positivity
    linarith

end Cubic.BoxAsymptotic.BulkW
