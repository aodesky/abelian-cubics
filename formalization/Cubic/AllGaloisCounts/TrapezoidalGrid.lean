import Cubic.AllGaloisCounts.SliceCellEstimate
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-! Exact summation of trapezoidal cell errors on a symmetric integer grid,
including the endpoint half-weights. -/

noncomputable section

namespace Cubic.AllGaloisCounts.TrapezoidalGrid
open MeasureTheory SliceCellEstimate

theorem integral_cells {f : ℝ → ℝ} (hf : Continuous f) (N : ℕ) (H : ℝ) :
    (∑ r ∈ Finset.Ico (-(N : ℤ)) N, ∫ x in (r : ℝ) / H..((r : ℝ) + 1) / H, f x) =
      ∫ x in -(N : ℝ) / H..(N : ℝ) / H, f x := by
  let A : ℤ → ℝ := fun r => ∫ x in (0 : ℝ)..(r : ℝ) / H, f x
  have he (r : ℤ) : (∫ x in (r : ℝ) / H..((r : ℝ) + 1) / H, f x) = A (r + 1) - A r := by
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable (0 : ℝ) ((r : ℝ) / H))
      (hf.intervalIntegrable ((r : ℝ) / H) (((r : ℝ) + 1) / H))
    dsimp [A]
    push_cast
    linarith
  simp_rw [he]
  have h := Finset.sum_Ico_int_sub N A
  rw [Finset.sum_sub_distrib] at h ⊢
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (0 : ℝ) (-(N : ℝ) / H))
    (hf.intervalIntegrable (-(N : ℝ) / H) ((N : ℝ) / H))
  simp only [A, Int.cast_neg, Int.cast_natCast] at h
  linarith

theorem trapezoid_cells (f : ℝ → ℝ) (N : ℕ) (H : ℝ) :
    (∑ r ∈ Finset.Ico (-(N : ℤ)) N,
      ((((r : ℝ) + 1) / H - (r : ℝ) / H) / 2 *
        (f ((r : ℝ) / H) + f (((r : ℝ) + 1) / H)))) =
      (1 / H) * ((∑ r ∈ Finset.Icc (-(N : ℤ)) N, f ((r : ℝ) / H)) -
        (f (-(N : ℝ) / H) + f ((N : ℝ) / H)) / 2) := by
  have hw (r : ℤ) : ((r : ℝ) + 1) / H - (r : ℝ) / H = 1 / H := by ring
  simp_rw [hw]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have ht := Finset.sum_Ico_int_sub N (fun r : ℤ => f ((r : ℝ) / H))
  simp only [Finset.sum_sub_distrib, Int.cast_add, Int.cast_one,
    Int.cast_neg, Int.cast_natCast] at ht
  have hs := Finset.sum_Icc_eq_sum_Ico_add (fun r : ℤ => f ((r : ℝ) / H))
    (show -(N : ℤ) ≤ N by omega)
  rw [hs]
  push_cast
  linear_combination - (1 / H) / 2 * ht

theorem error_cells {f : ℝ → ℝ} (hf : Continuous f) (N : ℕ) (H : ℝ) :
    (∑ r ∈ Finset.Ico (-(N : ℤ)) N,
      error f ((r : ℝ) / H) (((r : ℝ) + 1) / H)) =
      (1 / H) * ((∑ r ∈ Finset.Icc (-(N : ℤ)) N, f ((r : ℝ) / H)) -
        (f (-(N : ℝ) / H) + f ((N : ℝ) / H)) / 2) -
      ∫ x in -(N : ℝ) / H..(N : ℝ) / H, f x := by
  simp only [error, Finset.sum_sub_distrib]
  rw [trapezoid_cells, integral_cells hf]

end Cubic.AllGaloisCounts.TrapezoidalGrid
