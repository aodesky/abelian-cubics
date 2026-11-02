import CubicTargets.BoxAsymptotic.Statement
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The smooth dyadic partition and the product profiles

`χ(u) = smoothTransition(2 - u)` is smooth, equal to `1` for `u ≤ 1` and `0` for `u ≥ 2`,
and nonincreasing. `φ(u) = χ(u) - χ(2u)` is smooth, supported in `[1/2, 2]`, takes values in
`[0, 1]`, and `Σ_{i=a}^{b} φ(u/2^i) = χ(u/2^b) - χ(2u/2^a)` telescopes to `1` on
`2^a ≤ u ≤ 2^b`.

The profiles for `SmoothSectorCounting` are `Φ(u) = φ(u)/u` and `Ψ(v) = φ(|v|)/|v|`: then
`H/(nτ) · φ(n/X) φ(τ/Θ) = (H/(XΘ)) Φ(n/X) Ψ(±τ/Θ)`. Both are `C^∞` because `φ` vanishes
near `0`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothPartition

open Real
open scoped ContDiff

/-- `χ(u) = smoothTransition(2 - u)`. -/
def χ (u : ℝ) : ℝ := smoothTransition (2 - u)

/-- `φ(u) = χ(u) - χ(2u)`. -/
def φ (u : ℝ) : ℝ := χ u - χ (2 * u)

/-- `Φ(u) = φ(u)/u`. -/
def Φ (u : ℝ) : ℝ := φ u / u

/-- `Ψ(v) = φ(|v|)/|v|`. -/
def Ψ (v : ℝ) : ℝ := φ |v| / |v|

theorem χ_contDiff : ContDiff ℝ ∞ χ :=
  smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem χ_eq_one {u : ℝ} (h : u ≤ 1) : χ u = 1 := smoothTransition.one_of_one_le (by linarith)

theorem χ_eq_zero {u : ℝ} (h : 2 ≤ u) : χ u = 0 := smoothTransition.zero_of_nonpos (by linarith)

theorem χ_nonneg (u : ℝ) : 0 ≤ χ u := smoothTransition.nonneg _

theorem χ_le_one (u : ℝ) : χ u ≤ 1 := smoothTransition.le_one _

theorem χ_anti {u v : ℝ} (h : u ≤ v) : χ v ≤ χ u :=
  smoothTransition.monotone (by linarith)

theorem φ_contDiff : ContDiff ℝ ∞ φ :=
  χ_contDiff.sub (χ_contDiff.comp (contDiff_const.mul contDiff_id))

theorem φ_eq_zero_of_le {u : ℝ} (h : u ≤ 1 / 2) : φ u = 0 := by
  rw [φ, χ_eq_one (by linarith), χ_eq_one (by linarith)]; ring

theorem φ_eq_zero_of_ge {u : ℝ} (h : 2 ≤ u) : φ u = 0 := by
  rw [φ, χ_eq_zero h, χ_eq_zero (by linarith)]; ring

theorem φ_nonneg (u : ℝ) : 0 ≤ φ u := by
  rcases le_total u 0 with h | h
  · rw [φ_eq_zero_of_le (by linarith)]
  · rw [φ]; linarith [χ_anti (by linarith : u ≤ 2 * u)]

theorem φ_le_one (u : ℝ) : φ u ≤ 1 := by
  rw [φ]; linarith [χ_le_one u, χ_nonneg (2 * u)]

theorem φ_support : Function.support φ ⊆ Set.Icc (1 / 2) 2 := by
  intro u hu
  by_contra h
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact hu (φ_eq_zero_of_le h.le)
  · exact hu (φ_eq_zero_of_ge h.le)

theorem Φ_contDiff : ContDiff ℝ ∞ Φ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x (1 / 4) with hx | hx
  · have : Φ =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (by linarith : x < 1 / 2)] with y hy
      rw [Φ, φ_eq_zero_of_le (le_of_lt hy), zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact φ_contDiff.contDiffAt.div contDiffAt_id (by simp; linarith)

theorem Φ_support : Function.support Φ ⊆ Set.Icc (1 / 2) 4 := by
  intro u hu
  have : φ u ≠ 0 := by
    intro h; apply hu; rw [Φ, h, zero_div]
  have := φ_support this
  exact ⟨this.1, by linarith [this.2]⟩

theorem Ψ_contDiff : ContDiff ℝ ∞ Ψ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge |x| (1 / 4) with hx | hx
  · have : Ψ =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      have ho : IsOpen {y : ℝ | |y| < 1 / 2} := isOpen_lt continuous_abs continuous_const
      filter_upwards [ho.mem_nhds (by show |x| < 1 / 2; linarith)] with y hy
      rw [Ψ, φ_eq_zero_of_le (le_of_lt hy), zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · rcases le_or_gt 0 x with h0 | h0
    · have hx0 : 0 < x := by rw [abs_of_nonneg h0] at hx; linarith
      have : Ψ =ᶠ[nhds x] fun y => φ y / y := by
        filter_upwards [Ioi_mem_nhds hx0] with y hy
        rw [Ψ, abs_of_pos hy]
      exact (φ_contDiff.contDiffAt.div contDiffAt_id hx0.ne').congr_of_eventuallyEq this
    · have : Ψ =ᶠ[nhds x] fun y => φ (-y) / (-y) := by
        filter_upwards [Iio_mem_nhds h0] with y hy
        rw [Ψ, abs_of_neg hy]
      exact ((φ_contDiff.comp contDiff_neg).contDiffAt.div contDiff_neg.contDiffAt
        (by simp; linarith)).congr_of_eventuallyEq this

theorem Ψ_support : Function.support Ψ ⊆ Set.Icc (-4) 4 := by
  intro v hv
  have : φ |v| ≠ 0 := by
    intro h; apply hv; rw [Ψ, h, zero_div]
  have := φ_support this
  rw [Set.mem_Icc]; constructor <;> linarith [abs_le.mp (le_of_le_of_eq this.2 rfl : |v| ≤ 2)]


/-- Telescoping in the norm scale: `Σ_{a ≤ i ≤ b} φ(u/2^i) = χ(u/2^b) - χ(2u/2^a)`. -/
theorem sum_φ_norm (u : ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Icc a b, φ (u / 2 ^ i) = χ (u / 2 ^ b) - χ (2 * u / 2 ^ a) := by
  induction b, hab using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton, φ, mul_div_assoc]
  | succ b hab ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, φ]
    have : 2 * (u / 2 ^ (b + 1)) = u / 2 ^ b := by rw [pow_succ]; field_simp
    rw [this]; ring

/-- Telescoping in the angle scale: `Σ_{a ≤ j ≤ b} φ(τ 2^j) = χ(τ 2^a) - χ(τ 2^{b+1})`. -/
theorem sum_φ_angle (τ : ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc a b, φ (τ * 2 ^ j) = χ (τ * 2 ^ a) - χ (τ * 2 ^ (b + 1)) := by
  induction b, hab using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton, φ, pow_succ]; ring_nf
  | succ b hab ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, φ]
    rw [show 2 * (τ * 2 ^ (b + 1)) = τ * 2 ^ (b + 1 + 1) by ring]; ring

/-- The norm partition sums to `1` on `[2^a, 2^b]`. -/
theorem sum_φ_norm_eq_one {u : ℝ} {a b : ℕ} (hab : a ≤ b) (h1 : 2 ^ a ≤ u) (h2 : u ≤ 2 ^ b) :
    ∑ i ∈ Finset.Icc a b, φ (u / 2 ^ i) = 1 := by
  rw [sum_φ_norm u hab, χ_eq_one (by rw [div_le_one (by positivity)]; exact h2),
    χ_eq_zero (by rw [le_div_iff₀ (by positivity)]; linarith)]
  ring

/-- The angle partition sums to `1` on `[2^{-b}, 2^{-a}]`. -/
theorem sum_φ_angle_eq_one {τ : ℝ} {a b : ℕ} (hab : a ≤ b) (h1 : τ * 2 ^ a ≤ 1)
    (h2 : 1 ≤ τ * 2 ^ b) : ∑ j ∈ Finset.Icc a b, φ (τ * 2 ^ j) = 1 := by
  rw [sum_φ_angle τ hab, χ_eq_one h1, χ_eq_zero (by rw [pow_succ]; linarith)]
  ring

end Cubic.BoxAsymptotic.SmoothPartition
