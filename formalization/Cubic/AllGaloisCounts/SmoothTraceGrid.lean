import Cubic.AllGaloisCounts.SmoothTraceData

/-! The trace trapezoidal sum on the truncated interval, retaining both
endpoint half-weights. Evenness combines them into one endpoint value. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SmoothTraceGrid
open SmoothTraceData SliceCellEstimate MeasureTheory

theorem scaled_mem {H : ℝ} (hH : 0 < H) {N : ℕ} (hN : (N : ℝ) ≤ H)
    {r : ℤ} (hr : r ∈ Finset.Icc (-(N : ℤ)) N) : (r : ℝ) / H ∈ interval := by
  have hr1 : -(N : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hr2 : (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).2
  exact ⟨(le_div_iff₀ hH).mpr (by linarith), (div_le_iff₀ hH).mpr (by linarith)⟩

theorem truncated {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f domain) (heven : Function.Even f)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ interval, |deriv (deriv f) x| ≤ M)
    {H : ℝ} (hH : 0 < H) (N : ℕ) (hN : (N : ℝ) ≤ H) :
    |(∑ r ∈ Finset.Icc (-(N : ℤ)) N, f ((r : ℝ) / H)) -
      (H * (∫ x in -(N : ℝ) / H..(N : ℝ) / H, f x) + f ((N : ℝ) / H))| ≤ 2 * M / H := by
  have hn0 : 0 ≤ (N : ℝ) / H := by positivity
  have hn1 : (N : ℝ) / H ≤ 1 := (div_le_one hH).mpr hN
  have hi : Set.Icc (-(N : ℝ) / H) ((N : ℝ) / H) ⊆ interval := by
    intro x hx
    rw [neg_div] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcell : ∀ r ∈ Finset.Ico (-(N : ℤ)) N,
      |error (clipped f) ((r : ℝ) / H) (((r : ℝ) + 1) / H)| ≤ M / H ^ 3 := by
    intro r hr
    have hr' := Finset.mem_Ico.mp hr
    have ha : (r : ℝ) / H ∈ interval := scaled_mem hH hN (Finset.mem_Icc.mpr ⟨hr'.1, hr'.2.le⟩)
    have hb : ((r : ℝ) + 1) / H ∈ interval := by
      have h := scaled_mem hH hN (r := r + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      simpa only [Int.cast_add, Int.cast_one] using h
    have hab : (r : ℝ) / H < ((r : ℝ) + 1) / H :=
      (div_lt_div_iff_of_pos_right hH).mpr (by linarith)
    have hsub : Set.Icc ((r : ℝ) / H) (((r : ℝ) + 1) / H) ⊆ interval :=
      fun x hx => ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
    rw [error_congr hab.le (fun x hx => clipped_eq (f := f) (hsub hx))]
    have hc := TrapezoidalEstimate.smooth_cell hab hM
      (fun x hx => has_deriv hf (hsub hx)) (fun x hx => has_second_deriv hf (hsub hx))
      ((second_continuous hf).mono hsub) (fun x hx => hbound x (hsub hx))
    have hw : ((r : ℝ) + 1) / H - (r : ℝ) / H = 1 / H := by ring
    change |error f _ _| ≤ _ at hc
    rw [hw] at hc
    calc _ ≤ (1 / H) ^ 3 * M / 12 := hc
      _ = (M / H ^ 3) / 12 := by ring
      _ ≤ M / H ^ 3 := div_le_self (by positivity) (by norm_num)
  have hcard : ((Finset.Ico (-(N : ℤ)) N).card : ℝ) ≤ 2 * H := by
    rw [Int.card_Ico, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    linarith
  have hsum : |∑ r ∈ Finset.Ico (-(N : ℤ)) N,
      error (clipped f) ((r : ℝ) / H) (((r : ℝ) + 1) / H)| ≤ 2 * M / H ^ 2 := by
    calc _ ≤ ∑ r ∈ Finset.Ico (-(N : ℤ)) N,
          |error (clipped f) ((r : ℝ) / H) (((r : ℝ) + 1) / H)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.Ico (-(N : ℤ)) N, M / H ^ 3 := Finset.sum_le_sum hcell
      _ = ((Finset.Ico (-(N : ℤ)) N).card : ℝ) * (M / H ^ 3) := by simp
      _ ≤ (2 * H) * (M / H ^ 3) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * M / H ^ 2 := by field_simp
  rw [TrapezoidalGrid.error_cells (clipped_continuous hf)] at hsum
  have hs : (∑ r ∈ Finset.Icc (-(N : ℤ)) N, clipped f ((r : ℝ) / H)) =
      ∑ r ∈ Finset.Icc (-(N : ℤ)) N, f ((r : ℝ) / H) :=
    Finset.sum_congr rfl (fun r hr => clipped_eq (scaled_mem hH hN hr))
  have he1 : clipped f (-(N : ℝ) / H) = f ((N : ℝ) / H) := by
    rw [clipped_eq (hi ⟨le_rfl, by rw [neg_div]; linarith⟩), neg_div, heven]
  have he2 : clipped f ((N : ℝ) / H) = f ((N : ℝ) / H) :=
    clipped_eq ⟨by linarith, hn1⟩
  have hint : (∫ x in -(N : ℝ) / H..(N : ℝ) / H, clipped f x) =
      ∫ x in -(N : ℝ) / H..(N : ℝ) / H, f x := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (by rw [neg_div]; linarith)]
    intro x hx
    exact clipped_eq (hi hx)
  rw [hs, he1, he2, hint] at hsum
  have he : (∑ r ∈ Finset.Icc (-(N : ℤ)) N, f ((r : ℝ) / H)) -
      (H * (∫ x in -(N : ℝ) / H..(N : ℝ) / H, f x) + f ((N : ℝ) / H)) =
      H * ((1 / H) * ((∑ r ∈ Finset.Icc (-(N : ℤ)) N, f ((r : ℝ) / H)) -
        (f ((N : ℝ) / H) + f ((N : ℝ) / H)) / 2) -
          ∫ x in -(N : ℝ) / H..(N : ℝ) / H, f x) := by field_simp; ring
  rw [he, abs_mul, abs_of_pos hH]
  calc _ ≤ H * (2 * M / H ^ 2) := mul_le_mul_of_nonneg_left hsum hH.le
    _ = 2 * M / H := by field_simp

end Cubic.AllGaloisCounts.SmoothTraceGrid
