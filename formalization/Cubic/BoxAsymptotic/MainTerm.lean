import Cubic.BoxAsymptotic.Discard

/-!
# The leading term: `2 Σ_{good} M(i) = A₃ H (log H)³ + O(H log² H (1 + log(1/ε)))`

`M(i) = 18√3 (log 2/π) H ((a i log 2 + b₀) log 2 + a c₁)`, so
`2 Σ M = 36√3 (log 2/π) H (a (log 2)² Σ i + (b₀ log 2 + a c₁) #G)`. With
`Σ_{good} i = (11/54) h³ + O(D h²)`, `h = log₂ H`, `(log 2)³ h³ = (log H)³`, the leading
term is `(36√3/π)(11/54) a H (log H)³ = A₃ H (log H)³` for `a = 11C/54`,
`A₃ = 121C/(27π√3)`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.MainTerm

open Real
open CubicTargets.BoxAsymptotic (aStar A3)
open Cubic.BoxAsymptotic.GoodSet (G)
open Cubic.BoxAsymptotic.BulkSum (M)
open Cubic.BoxAsymptotic.PartitionIntegrals (c₁)
open Cubic.BoxAsymptotic.GoodCount (D sum_scales)

theorem A3_eq : A3 = 36 * Real.sqrt 3 / π * (11 / 54) * aStar := by
  simp only [A3, aStar]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := by positivity
  have hπ : 0 < π := Real.pi_pos
  have h3' : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [h3']; ring

theorem M_eq (H b₀ : ℝ) (i : ℕ) :
    M H b₀ i = 18 * Real.sqrt 3 * (Real.log 2 / π) * H *
      (aStar * Real.log 2 ^ 2 * i + (b₀ * Real.log 2 + aStar * c₁)) := by
  simp only [M, Real.log_pow]; ring

theorem logb_cube (H : ℝ) : Real.log 2 ^ 3 * logb 2 H ^ 3 = Real.log H ^ 3 := by
  rw [← mul_pow, logb, mul_div_cancel₀ _ (by positivity : Real.log 2 ≠ 0)]

/-- **The leading term.** -/
theorem main_eval {H ε b₀ : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    |2 * ∑ p ∈ G H ε, M H b₀ p.1 - A3 * H * Real.log H ^ 3| ≤
      36 * Real.sqrt 3 * Real.log 2 ^ 3 / π * |aStar| * H *
          (D ε * (2 * logb 2 H + 2) ^ 2 + 16 * logb 2 H ^ 2) +
        36 * Real.sqrt 3 * (Real.log 2 / π) * H * |b₀ * Real.log 2 + aStar * c₁| *
          (30 * Real.log H ^ 2) := by
  have hH0 : 0 < H := by linarith
  have hS := sum_scales hH hε0 hε1
  have hcard := Cubic.BoxAsymptotic.GoodSet.card_G (ε := ε) hH
  have hpi : 0 < π := Real.pi_pos
  set k := b₀ * Real.log 2 + aStar * c₁
  set Si := ∑ p ∈ G H ε, (p.1 : ℝ)
  have e1 : 2 * ∑ p ∈ G H ε, M H b₀ p.1 = 36 * Real.sqrt 3 * (Real.log 2 / π) * H *
      (aStar * Real.log 2 ^ 2 * Si + k * (G H ε).card) := by
    simp only [M_eq, Si, k]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    ring
  have e2 : A3 * H * Real.log H ^ 3 = 36 * Real.sqrt 3 * (Real.log 2 / π) * H *
      (aStar * Real.log 2 ^ 2 * (11 / 54 * logb 2 H ^ 3)) := by
    rw [A3_eq, ← logb_cube H]; ring
  rw [e1, e2, ← mul_sub]
  have hc0 : 0 ≤ 36 * Real.sqrt 3 * (Real.log 2 / π) * H := by positivity
  rw [abs_mul, abs_of_nonneg hc0]
  have e3 : aStar * Real.log 2 ^ 2 * Si + k * (G H ε).card -
      aStar * Real.log 2 ^ 2 * (11 / 54 * logb 2 H ^ 3) =
      aStar * Real.log 2 ^ 2 * (Si - 11 / 54 * logb 2 H ^ 3) + k * (G H ε).card := by ring
  rw [e3]
  have h1 : |aStar * Real.log 2 ^ 2 * (Si - 11 / 54 * logb 2 H ^ 3) + k * (G H ε).card| ≤
      |aStar| * Real.log 2 ^ 2 * (D ε * (2 * logb 2 H + 2) ^ 2 + 16 * logb 2 H ^ 2) +
        |k| * (30 * Real.log H ^ 2) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.log 2 ^ 2)]
      exact mul_le_mul_of_nonneg_left hS (by positivity)
    · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (G H ε).card)]
      exact mul_le_mul_of_nonneg_left hcard (abs_nonneg _)
  calc 36 * Real.sqrt 3 * (Real.log 2 / π) * H *
        |aStar * Real.log 2 ^ 2 * (Si - 11 / 54 * logb 2 H ^ 3) + k * (G H ε).card|
      ≤ 36 * Real.sqrt 3 * (Real.log 2 / π) * H *
        (|aStar| * Real.log 2 ^ 2 * (D ε * (2 * logb 2 H + 2) ^ 2 + 16 * logb 2 H ^ 2) +
          |k| * (30 * Real.log H ^ 2)) := mul_le_mul_of_nonneg_left h1 hc0
    _ = _ := by ring

/-- `Σ |M| ≤ C H (log H)³`. -/
theorem sum_absM {H ε b₀ : ℝ} (hH : 3 ≤ H) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ∑ p ∈ G H ε, |M H b₀ p.1| ≤ 18 * Real.sqrt 3 * (Real.log 2 / π) * H *
      (|aStar| * Real.log 2 ^ 2 * (4 * Real.log H) + |b₀ * Real.log 2 + aStar * c₁|) *
        (30 * Real.log H ^ 2) := by
  have hH0 : 0 < H := by linarith
  have hL : 1 ≤ Real.log H := by
    have : Real.log 3 ≤ Real.log H := Real.log_le_log (by norm_num) hH
    have h3 : 1 < Real.log 3 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hcard := Cubic.BoxAsymptotic.GoodSet.card_G (ε := ε) hH
  set k := b₀ * Real.log 2 + aStar * c₁
  have hi : ∀ p ∈ G H ε, (p.1 : ℝ) ≤ 4 * Real.log H := by
    intro p hp
    have hg := Cubic.BoxAsymptotic.GoodSet.mem_G hp
    have h4 : 16 * (2 : ℝ) ^ p.1 ≤ H ^ 2 := hg.g4
    have : (2 : ℝ) ^ p.1 ≤ H ^ 2 := by linarith [pow_pos (by norm_num : (0 : ℝ) < 2) p.1]
    have hl := Real.log_le_log (by positivity) this
    rw [Real.log_pow, Real.log_pow] at hl
    have hl2 := Real.log_two_gt_d9
    have : (p.1 : ℝ) * Real.log 2 ≤ 2 * Real.log H := by push_cast at hl; linarith
    nlinarith
  have hterm : ∀ p ∈ G H ε, |M H b₀ p.1| ≤ 18 * Real.sqrt 3 * (Real.log 2 / π) * H *
      (|aStar| * Real.log 2 ^ 2 * (4 * Real.log H) + |k|) := by
    intro p hp
    rw [M_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 18 * Real.sqrt 3 *
      (Real.log 2 / π) * H)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.log 2 ^ 2),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) p.1)]
    exact mul_le_mul_of_nonneg_left (hi p hp) (by positivity)
  calc ∑ p ∈ G H ε, |M H b₀ p.1| ≤ ∑ _p ∈ G H ε, 18 * Real.sqrt 3 * (Real.log 2 / π) * H *
        (|aStar| * Real.log 2 ^ 2 * (4 * Real.log H) + |k|) := Finset.sum_le_sum hterm
    _ = (G H ε).card * (18 * Real.sqrt 3 * (Real.log 2 / π) * H *
        (|aStar| * Real.log 2 ^ 2 * (4 * Real.log H) + |k|)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (30 * Real.log H ^ 2) * (18 * Real.sqrt 3 * (Real.log 2 / π) * H *
        (|aStar| * Real.log 2 ^ 2 * (4 * Real.log H) + |k|)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end Cubic.BoxAsymptotic.MainTerm
