import Cubic.AllGaloisCounts.SliceCellEstimate

/-! At most eight grid cells can contain one of the four slice junctions,
including a junction that is exactly a lattice endpoint. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceJunctionGrid
open CountData SliceCellEstimate

def bad (H y : ℝ) : Finset ℤ :=
  (junctions y).image (fun t => ⌊H * t⌋) ∪ (junctions y).image (fun t => ⌊H * t⌋ - 1)

theorem bad_card (H y : ℝ) : (bad H y).card ≤ 8 := by
  have h := Finset.card_union_le ((junctions y).image (fun t => ⌊H * t⌋))
    ((junctions y).image (fun t => ⌊H * t⌋ - 1))
  have h1 := Finset.card_image_le (s := junctions y) (f := fun t => ⌊H * t⌋)
  have h2 := Finset.card_image_le (s := junctions y) (f := fun t => ⌊H * t⌋ - 1)
  have h3 := junctions_card y
  exact h.trans (by omega)

theorem good {H y : ℝ} (hH : 0 < H) {r : ℤ} (hr : r ∉ bad H y) :
    ∀ t ∈ junctions y, t ∉ Set.Icc ((r : ℝ) / H) (((r : ℝ) + 1) / H) := by
  intro t ht h
  have hl : r ≤ ⌊H * t⌋ := Int.le_floor.mpr (by
    have h' := (div_le_iff₀ hH).mp h.1
    nlinarith)
  have hu : ⌊H * t⌋ ≤ r + 1 := Int.floor_le_iff.mpr (by
    have h' := (le_div_iff₀ hH).mp h.2
    push_cast
    nlinarith)
  apply hr
  by_cases he : ⌊H * t⌋ = r
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ht, he⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, by omega⟩)

theorem cell_bound {H y : ℝ} (hH : 0 < H) (hy : y ∈ Set.Icc (-1) 1) (r : ℤ) :
    |error (fun x => F x y) ((r : ℝ) / H) (((r : ℝ) + 1) / H)| ≤
      2 / H ^ 3 + if r ∈ bad H y then 18 / H ^ 2 else 0 := by
  have hab : (r : ℝ) / H < ((r : ℝ) + 1) / H := (div_lt_div_iff_of_pos_right hH).mpr (by linarith)
  have hw : ((r : ℝ) + 1) / H - (r : ℝ) / H = 1 / H := by ring
  by_cases hr : r ∈ bad H y
  · rw [if_pos hr]
    have h := junction_cell hy hab.le
    rw [hw] at h
    have he : 18 * (1 / H) ^ 2 = 18 / H ^ 2 := by ring
    rw [he] at h
    exact h.trans (le_add_of_nonneg_left (by positivity))
  · rw [if_neg hr, add_zero]
    have h := smooth_cell hy hab (good hH hr)
    rw [hw] at h
    convert h using 1 <;> ring

theorem sum_bound {H y : ℝ} (hH : 1 ≤ H) (hy : y ∈ Set.Icc (-1) 1)
    (s : Finset ℤ) (hs : (s.card : ℝ) ≤ 6 * H) :
    |∑ r ∈ s, error (fun x => F x y) ((r : ℝ) / H) (((r : ℝ) + 1) / H)| ≤ 156 / H ^ 2 := by
  classical
  have hp : 0 < H := by linarith
  have hb : ((s.filter (fun r => r ∈ bad H y)).card : ℝ) ≤ 8 := by
    have hsub : s.filter (fun r => r ∈ bad H y) ⊆ bad H y := by
      intro r hr
      exact (Finset.mem_filter.mp hr).2
    exact_mod_cast (Finset.card_le_card hsub).trans (bad_card H y)
  calc _ ≤ ∑ r ∈ s, |error (fun x => F x y) ((r : ℝ) / H) (((r : ℝ) + 1) / H)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ s, (2 / H ^ 3 + if r ∈ bad H y then 18 / H ^ 2 else 0) :=
          Finset.sum_le_sum (fun r _ => cell_bound hp hy r)
    _ = (s.card : ℝ) * (2 / H ^ 3) +
        ((s.filter (fun r => r ∈ bad H y)).card : ℝ) * (18 / H ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter]
          simp
    _ ≤ (6 * H) * (2 / H ^ 3) + 8 * (18 / H ^ 2) := by gcongr
    _ = 156 / H ^ 2 := by field_simp; ring

end Cubic.AllGaloisCounts.SliceJunctionGrid
