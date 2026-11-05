import Cubic.Counting.RiemannSum

/-!
# Riemann sums over arithmetic progressions in a subinterval of `[-1, 1]`

Supporting estimate for `thm:traceDistribution`. Let `g` be Lipschitz (constant `M`) and
bounded (by `B`) on `[-2, 2]`, let `0 < δ ≤ 1` and `-1 ≤ a ≤ b ≤ 1`. If the points
`x₀ + jδ`, `0 ≤ j < n`, are exactly the points of the progression `x₀ + δℤ` in `[a, b]`
(that is, `a ≤ x₀ < a + δ` and `b < x₀ + nδ ≤ b + δ`), then
`|δ Σ_{j<n} g(x₀ + jδ) - ∫_a^b g| ≤ (3M + 2B)δ`. The constant does not depend on `a`, `b`
or `x₀`.
-/

noncomputable section

namespace Cubic.Counting.IntervalRiemannSum

open MeasureTheory intervalIntegral

variable {g : ℝ → ℝ} {M B : ℝ}

theorem integral_abs_le (hB : ∀ x ∈ Set.Icc (-2 : ℝ) 2, |g x| ≤ B) {a b : ℝ}
    (ha : -2 ≤ a) (ha' : a ≤ 2) (hb : -2 ≤ b) (hb' : b ≤ 2) :
    |∫ t in a..b, g t| ≤ B * |b - a| := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := B)
    (f := g) (by
      intro t ht
      rw [Set.mem_uIoc] at ht
      rw [Real.norm_eq_abs]
      apply hB
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith)
  rwa [Real.norm_eq_abs] at this

theorem riemann_interval (hg : Continuous g) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-2 : ℝ) 2, |g x - g y| ≤ M * |x - y|)
    (hB : ∀ x ∈ Set.Icc (-2 : ℝ) 2, |g x| ≤ B) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {a b x₀ : ℝ} (n : ℕ) (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hx₀ : a ≤ x₀)
    (hx₀' : x₀ < a + δ) (hn₁ : b < x₀ + n * δ) (hn₂ : x₀ + n * δ ≤ b + δ) :
    |δ * ∑ j ∈ Finset.range n, g (x₀ + j * δ) - ∫ x in a..b, g x| ≤ (3 * M + 2 * B) * δ := by
  set y : ℕ → ℝ := fun j => x₀ + j * δ with hy
  have hsum : ∑ j ∈ Finset.range n, ∫ t in y j..y (j + 1), g t = ∫ t in y 0..y n, g t :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ => hg.intervalIntegrable _ _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnδ : (n : ℝ) * δ ≤ 3 := by linarith
  have hcells : |δ * ∑ j ∈ Finset.range n, g (y j) - ∫ t in y 0..y n, g t| ≤
      n * (M * δ ^ 2) := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j ∈ Finset.range n,
        |δ * g (y j) - ∫ t in y j..y (j + 1), g t| ≤ M * δ ^ 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
      have hyj : y (j + 1) = y j + δ := by simp only [y]; push_cast; ring
      rw [hyj]
      refine Cubic.Counting.RiemannSum.cell_bound hg hM0 hM hδ0.le ?_ ?_
      · simp only [y]; nlinarith [Nat.cast_nonneg (α := ℝ) j]
      · simp only [y]; nlinarith
    refine (Finset.sum_le_sum hj).trans (le_of_eq ?_)
    simp
  have hy0 : y 0 = x₀ := by simp [y]
  have hyn : y n = x₀ + n * δ := rfl
  rw [hy0, hyn] at hcells
  have hsplit : ∫ t in a..b, g t = (∫ t in a..x₀, g t) + (∫ t in x₀..x₀ + n * δ, g t) +
      ∫ t in x₀ + n * δ..b, g t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have hnδ0 : 0 ≤ (n : ℝ) * δ := mul_nonneg hn0 hδ0.le
  have he1 := integral_abs_le hB (a := a) (b := x₀) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have he2 := integral_abs_le hB (a := x₀ + n * δ) (b := b) (by linarith) (by linarith)
    (by linarith) (by linarith)
  rw [abs_of_nonneg (by linarith : 0 ≤ x₀ - a)] at he1
  rw [abs_of_nonpos (by linarith : b - (x₀ + n * δ) ≤ 0)] at he2
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 ⟨by norm_num, by norm_num⟩)
  have e1 : B * (x₀ - a) ≤ B * δ := mul_le_mul_of_nonneg_left (by linarith) hB0
  have e2 : B * -(b - (x₀ + n * δ)) ≤ B * δ := mul_le_mul_of_nonneg_left (by linarith) hB0
  have e3 : (n : ℝ) * (M * δ ^ 2) ≤ 3 * M * δ := by
    have : (n : ℝ) * (M * δ ^ 2) = (n * δ) * (M * δ) := by ring
    rw [this]
    nlinarith [mul_nonneg hM0 hδ0.le]
  rw [hsplit]
  rw [abs_le] at hcells he1 he2 ⊢
  constructor <;> nlinarith

end Cubic.Counting.IntervalRiemannSum
