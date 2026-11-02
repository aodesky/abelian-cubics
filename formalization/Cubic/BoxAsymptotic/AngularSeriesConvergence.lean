import Cubic.BoxAsymptotic.AngularLocal
import Cubic.BoxAsymptotic.ZeroModeSeries

/-! Absolute convergence of the actual angular series, by domination by the
zero mode, whose convergence follows directly from the fourfold divisor majorant. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularSeriesConvergence

open Complex CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularLocalData
open Cubic.BoxAsymptotic.AngularLocal

theorem summable
    (k : ℤ) (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (coefficient k) s := by
  have h := (ZeroModeSeries.series_hasSum s hs).summable.norm
  rw [LSeriesSummable, ← summable_norm_iff]
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => LSeries.norm_term_le s ?_
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mass_nonneg n)] using
    norm_coefficient_le k n

theorem norm_away_le {k : ℤ} (hk : Even k) (M : ℕ) :
    ‖awayCoefficient k M‖ ≤ 3 * ZeroModeData.mass M := by
  by_cases h3 : 3 ∣ M
  · simp only [awayCoefficient, if_pos h3, norm_zero]
    exact mul_nonneg (by norm_num) (mass_nonneg M)
  · have hM : 0 < M := by
      by_contra h; have : M = 0 := by omega
      exact h3 (this ▸ dvd_zero 3)
    have h := norm_coefficient_le k M
    rw [coefficient_away hM h3 hk, norm_mul] at h
    norm_num at h
    linarith

theorem away_summable
    {k : ℤ} (hk : Even k) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (awayCoefficient k) s := by
  have h := (ZeroModeSeries.series_hasSum s hs).summable.norm.mul_left (3 : ℝ)
  rw [LSeriesSummable, ← summable_norm_iff]
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mass_nonneg n)]
    calc
      _ ≤ (3 * ZeroModeData.mass n) / (n : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right (norm_away_le hk n) (by positivity)
      _ = _ := by ring

theorem series_zero (s : ℂ) : series 0 s = ZeroModeData.series s := by
  change LSeries (coefficient 0) s = _
  rw [show coefficient 0 = (fun n => (ZeroModeData.mass n : ℂ)) from funext coefficient_zero]
  rfl

theorem series_odd {k : ℤ} (hk : Odd k) (s : ℂ) : series k s = 0 := by
  rw [series]
  calc
    _ = LSeries (fun _ => 0) s := LSeries_congr (fun {n} hn => coefficient_odd hk
      (Nat.pos_of_ne_zero hn)) s
    _ = 0 := by simp [LSeries, LSeries.term]

/-- The negative-frequency relation, with the vertical parameter conjugated.
This is an identity of the defining series; continuation is a separate step. -/
theorem series_neg (k : ℤ) (s : ℂ) : series (-k) s = star (series k (star s)) := by
  simp only [series, LSeries, tsum_star]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    coefficient_neg_index, star_div₀]
  congr 1
  simpa using Complex.cpow_conj (n : ℂ) (star s) (by simpa using Real.pi_pos.ne)

end Cubic.BoxAsymptotic.AngularSeriesConvergence
