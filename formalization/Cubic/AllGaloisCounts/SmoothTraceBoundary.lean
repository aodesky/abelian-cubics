import Cubic.AllGaloisCounts.SmoothTraceGrid

/-! Restoring the two omitted endpoint intervals produces the real-height
fractional-part term in the trace trapezoidal sum. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SmoothTraceBoundary
open SmoothTraceData MeasureTheory
open Cubic.Counting.GeneralMonicCount (T)

theorem tail_error {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f domain) {L a : ℝ}
    (hL : 0 ≤ L) (hb : ∀ x ∈ interval, |deriv f x| ≤ L) (ha : a ∈ Set.Icc 0 1) :
    |(∫ x in a..1, f x) - (1 - a) * f 1| ≤ L * (1 - a) ^ 2 := by
  have hsub : Set.Icc a 1 ⊆ interval := fun x hx => ⟨by linarith [hx.1, ha.1], hx.2⟩
  have hi : IntervalIntegrable f volume a 1 :=
    (hf.continuousOn.mono (hsub.trans subset)).intervalIntegrable_of_Icc ha.2
  have he : (∫ x in a..1, f x) - (1 - a) * f 1 = ∫ x in a..1, f x - f 1 := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [he]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => f x - f 1) (a := a) (b := 1) (C := L * (1 - a)) (by
      intro x hx
      rw [Set.uIoc_of_le ha.2] at hx
      have h := lipschitz hf hb (hsub ⟨hx.1.le, hx.2⟩) (show (1 : ℝ) ∈ interval by norm_num [interval])
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2)] at h
      rw [Real.norm_eq_abs]
      exact h.trans (mul_le_mul_of_nonneg_left (by linarith [hx.1]) hL))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha.2)] at h
  nlinarith

theorem full_integral {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f domain)
    (heven : Function.Even f) {a : ℝ} (ha : a ∈ Set.Icc 0 1) :
    (∫ x in (-1 : ℝ)..1, f x) = (∫ x in -a..a, f x) + 2 * ∫ x in a..1, f x := by
  have hi {u v : ℝ} (hu : -1 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
      IntervalIntegrable f volume u v :=
    (hf.continuousOn.mono (show Set.Icc u v ⊆ domain from
      fun x hx => subset ⟨hu.trans hx.1, hx.2.trans hv⟩)).intervalIntegrable_of_Icc huv
  have hn : (∫ x in (-1 : ℝ)..-a, f x) = ∫ x in a..1, f x := by
    calc _ = ∫ x in (-1 : ℝ)..-a, f (-x) :=
          intervalIntegral.integral_congr (fun x _ => (heven x).symm)
      _ = _ := by simpa only [neg_neg] using
          (intervalIntegral.integral_comp_neg (f := f) (a := -1) (b := -a))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi (u := -1) (v := -a) le_rfl (by linarith [ha.2]) (by linarith [ha.1]))
    (hi (u := -a) (v := 1) (by linarith [ha.2]) (by linarith [ha.1]) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hi (u := -a) (v := a) (by linarith [ha.2]) (by linarith [ha.1]) ha.2)
      (hi (u := a) (v := 1) (by linarith [ha.1]) ha.2 le_rfl), hn]
  ring

theorem estimate {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f domain) (heven : Function.Even f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ H : ℝ, 1 ≤ H →
      |(∑ r ∈ T H, f ((r : ℝ) / H)) -
        (H * (∫ x in (-1 : ℝ)..1, f x) + (1 - 2 * Int.fract H) * f 1)| ≤ K / H := by
  obtain ⟨L, M, hL, hM, hLb, hMb⟩ := derivative_bounds hf
  refine ⟨2 * M + 3 * L, by positivity, fun H hH => ?_⟩
  have hp : 0 < H := by linarith
  let N : ℕ := ⌊H⌋₊
  let a : ℝ := N / H
  have hN : (N : ℝ) ≤ H := Nat.floor_le hp.le
  have ha : a ∈ Set.Icc 0 1 := ⟨by positivity, (div_le_one hp).mpr hN⟩
  have hNc : (N : ℝ) = (⌊H⌋ : ℝ) := by
    exact_mod_cast (Int.natCast_floor_eq_floor hp.le)
  have hT : T H = Finset.Icc (-(N : ℤ)) N := by
    rw [T, ← Int.natCast_floor_eq_floor hp.le]
  have hfract : H * (1 - a) = Int.fract H := by
    dsimp [a]
    rw [hNc, Int.fract]
    field_simp
  have hdelta : 1 - a ≤ 1 / H := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [Int.fract_lt_one H]
  have hgrid := SmoothTraceGrid.truncated hf heven hM hMb hp N hN
  have heq : -(N : ℝ) / H = -a := by dsimp [a]; ring
  rw [← hT, heq] at hgrid
  have htail := tail_error hf hL hLb ha
  have hend := lipschitz hf hLb (show a ∈ interval from ⟨by linarith [ha.1], ha.2⟩)
    (show (1 : ℝ) ∈ interval by norm_num [interval])
  rw [abs_of_nonpos (sub_nonpos.mpr ha.2)] at hend
  have hend' : |f a - f 1| ≤ L / H := by
    calc _ ≤ L * (1 - a) := by simpa only [neg_sub] using hend
      _ ≤ L * (1 / H) := mul_le_mul_of_nonneg_left hdelta hL
      _ = L / H := by ring
  have htail' : |2 * H * ((∫ x in a..1, f x) - (1 - a) * f 1)| ≤ 2 * L / H := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * H)]
    calc _ ≤ (2 * H) * (L * (1 - a) ^ 2) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (2 * H) * (L * (1 / H) ^ 2) := by gcongr; exact sub_nonneg.mpr ha.2
      _ = 2 * L / H := by field_simp
  have he : (∑ r ∈ T H, f ((r : ℝ) / H)) -
      (H * (∫ x in (-1 : ℝ)..1, f x) + (1 - 2 * Int.fract H) * f 1) =
      ((∑ r ∈ T H, f ((r : ℝ) / H)) - (H * (∫ x in -a..a, f x) + f a)) -
        2 * H * ((∫ x in a..1, f x) - (1 - a) * f 1) + (f a - f 1) := by
    rw [full_integral hf heven ha, ← hfract]
    ring
  rw [he]
  calc _ ≤ |(∑ r ∈ T H, f ((r : ℝ) / H)) - (H * (∫ x in -a..a, f x) + f a)| +
        |2 * H * ((∫ x in a..1, f x) - (1 - a) * f 1)| + |f a - f 1| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 2 * M / H + 2 * L / H + L / H := by gcongr
    _ = (2 * M + 3 * L) / H := by ring

end Cubic.AllGaloisCounts.SmoothTraceBoundary
