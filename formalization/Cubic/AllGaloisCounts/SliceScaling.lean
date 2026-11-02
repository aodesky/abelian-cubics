import Cubic.AllGaloisCounts.LinearFactorSlice

/-! The interval in the actual marked-root parametrization has length
`H² F(r/H,a/H)`, including the slice `r=0`. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceScaling
open CountData MeasureTheory

def sliceSet (x y : ℝ) : Set ℝ :=
  {v | |v - (x ^ 2 + x * y)| ≤ 1 ∧ |x * v| ≤ 1}

def allowedInterval (H a r : ℝ) : Set ℝ :=
  {v | |v - r * (r + a)| ≤ H ^ 2 ∧ |r * v| ≤ H ^ 3}

theorem sliceSet_eq {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    sliceSet x y = Set.Icc (x ^ 2 + x * y - 1) (x ^ 2 + x * y + 1) ∩
      Set.Icc (-|x|⁻¹) |x|⁻¹ := by
  ext v
  have he : |x * v| ≤ 1 ↔ |v| ≤ |x|⁻¹ := by
    rw [abs_mul, mul_comm, ← le_div_iff₀ (abs_pos.mpr hx), one_div]
  simp only [sliceSet, Set.mem_setOf_eq]
  rw [he]
  simp only [Set.mem_inter_iff, Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, h3⟩

theorem slice_volume (x y : ℝ) : volume.real (sliceSet x y) = F x y := by
  by_cases hx : x = 0
  · subst x
    have he : sliceSet 0 y = Set.Icc (-1) 1 := by
      ext v
      simp [sliceSet, abs_le]
    rw [he, Real.volume_real_Icc]
    norm_num [F]
  · rw [sliceSet_eq hx, F, if_neg hx]

theorem allowedInterval_preimage {H : ℝ} (hH : 0 < H) (a r : ℝ) :
    allowedInterval H a r = ((H ^ 2)⁻¹ * ·) ⁻¹' sliceSet (r / H) (a / H) := by
  ext v
  have h2 : 0 < H ^ 2 := sq_pos_of_pos hH
  have h3 : 0 < H ^ 3 := pow_pos hH 3
  have e1 : (H ^ 2)⁻¹ * v - ((r / H) ^ 2 + r / H * (a / H)) =
      (v - r * (r + a)) / H ^ 2 := by field_simp
  have e2 : r / H * ((H ^ 2)⁻¹ * v) = (r * v) / H ^ 3 := by field_simp
  simp only [allowedInterval, sliceSet, Set.mem_preimage, Set.mem_setOf_eq, e1, e2,
    abs_div, abs_of_pos h2, abs_of_pos h3, div_le_iff₀ h2, div_le_iff₀ h3, one_mul]

theorem interval_length {H : ℝ} (hH : 0 < H) (a r : ℝ) :
    volume.real (allowedInterval H a r) = H ^ 2 * F (r / H) (a / H) := by
  rw [allowedInterval_preimage hH, measureReal_def,
    Real.volume_preimage_mul_left (inv_ne_zero (pow_ne_zero 2 hH.ne')),
    ENNReal.toReal_mul, inv_inv, abs_of_nonneg (sq_nonneg H),
    ENNReal.toReal_ofReal (sq_nonneg H)]
  rw [← measureReal_def, slice_volume]

end Cubic.AllGaloisCounts.SliceScaling
