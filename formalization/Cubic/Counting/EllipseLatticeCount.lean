import Cubic.Counting.EllipseLatticeCells

/-!
# `eqn:ellipseLatticeCount`

`#(E_H° ∩ ℤ²) = (2π/(3√3)) H² + O(H)` for `H ≥ 1`.

Following the proof of `lemma:reducibles`: the union `U` of the unit cells at
the points of `E_H° ∩ ℤ²` has area equal to their number
(`EllipseLatticeCells.volume_biUnion_cell`). By the strip estimate
`EllipseLatticeCells.mem_region_add_three`, `E_{H-3}° ⊆ U ⊆ E_{H+3}°`
(the former when `H ≥ 3`). Since `E_h°` has area `2π h² / (3√3)`
(`EllipseArea.volume_region`), the two bounds differ from
`2π H² / (3√3)` by `O(H)`.
-/

namespace Cubic.Counting.EllipseLatticeCount

open MeasureTheory Real Cubic.Counting.EllipseArea Cubic.Counting.EllipseLatticeCells
open CubicTargets.Counting.EllipseLatticeCount (latticePoints)

/-- The union of the cells at the lattice points lies in `E_{H+3}°`. -/
theorem biUnion_cell_subset {H : ℝ} (hH : 0 ≤ H) (hfin : (latticePoints H).Finite) :
    (⋃ p ∈ hfin.toFinset, cell p) ⊆ region (H + 3) := by
  intro z hz
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset] at hz
  obtain ⟨p, hp, hzp⟩ := hz
  simp only [cell, Set.mem_prod, Set.mem_Ico] at hzp
  refine mem_region_add_three hH (w := ((p.1 : ℝ), (p.2 : ℝ))) ?_ ?_ hp <;>
    · rw [abs_le]; constructor <;> linarith

/-- For `H ≥ 3`, `E_{H-3}°` lies in the union of the cells at the lattice points. -/
theorem subset_biUnion_cell {H : ℝ} (hH : 3 ≤ H) (hfin : (latticePoints H).Finite) :
    region (H - 3) ⊆ ⋃ p ∈ hfin.toFinset, cell p := by
  intro z hz
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
  refine ⟨(⌊z.1⌋, ⌊z.2⌋), ?_, (mem_cell_iff _ _).mpr rfl⟩
  rw [mem_latticePoints_iff]
  have f1 := Int.floor_le z.1
  have f1' := Int.lt_floor_add_one z.1
  have f2 := Int.floor_le z.2
  have f2' := Int.lt_floor_add_one z.2
  have h := mem_region_add_three (by linarith) (w := z)
    (z := ((⌊z.1⌋ : ℝ), (⌊z.2⌋ : ℝ))) (abs_le.mpr ⟨by dsimp only; linarith, by dsimp only; linarith⟩)
    (abs_le.mpr ⟨by dsimp only; linarith, by dsimp only; linarith⟩) hz
  simpa using h

theorem «eqn:ellipseLatticeCount» : CubicTargets.Counting.EllipseLatticeCount.Claim := by
  refine ⟨fun H hH => latticePoints_finite (by linarith), ?_⟩
  set α : ℝ := 2 * π / (3 * √3)
  have hα : 0 < α := by positivity
  refine ⟨15 * α, fun H hH => ?_⟩
  have hfin := latticePoints_finite (H := H) (by linarith)
  set N : ℝ := (Nat.card (latticePoints H) : ℝ)
  have hN : ENNReal.ofReal N = volume (⋃ p ∈ hfin.toFinset, cell p) := by
    rw [volume_biUnion_cell, ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq,
      ENNReal.ofReal_natCast]
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  -- Upper bound: `N ≤ α (H + 3)²`.
  have hup : N ≤ α * (H + 3) ^ 2 := by
    have := measure_mono (μ := volume) (biUnion_cell_subset (by linarith) hfin)
    rw [← hN, volume_region (by linarith), ENNReal.ofReal_le_ofReal_iff (by positivity)]
      at this
    exact this
  -- Lower bound: `α H² - 6 α H ≤ N`.
  have hlow : α * H ^ 2 - 6 * α * H ≤ N := by
    rcases le_or_gt 3 H with h3 | h3
    · have := measure_mono (μ := volume) (subset_biUnion_cell h3 hfin)
      rw [← hN, volume_region (by linarith), ENNReal.ofReal_le_ofReal_iff hN0] at this
      nlinarith
    · nlinarith
  rw [abs_le]
  constructor <;> nlinarith

end Cubic.Counting.EllipseLatticeCount
