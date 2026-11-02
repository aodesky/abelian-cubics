import Cubic.Counting.EllipseArea
import CubicTargets.Counting.EllipseLatticeCount

/-!
# Unit cells at the lattice points of `E_H°`

Lemmas for `eqn:ellipseLatticeCount`. The proof of
`lemma:reducibles` compares `#(E_H° ∩ ℤ²)` with the area of the union of the
unit squares attached to these points. We use the half-open squares
`[a, a+1) × [b, b+1)`, which are pairwise disjoint and have area one, so their
union has area equal to the count. Moving a point by at most one in each
coordinate changes `‖ψ‖` by at most `√3`, i.e. passes from `E_h°` into
`E_{h+3}°`; this is the fixed-width strip around the boundary.
-/

namespace Cubic.Counting.EllipseLatticeCells

open MeasureTheory Real Cubic.Counting.EllipseArea
open CubicTargets.Counting.EllipseLatticeCount (latticePoints)

theorem mem_latticePoints_iff (H : ℝ) (p : ℤ × ℤ) :
    p ∈ latticePoints H ↔ ((p.1 : ℝ), (p.2 : ℝ)) ∈ region H := Iff.rfl

/-- `E_H° ∩ ℤ²` is finite: on `E_H°` one has `|x - 1/3|, |y - 1/3| ≤ H`. -/
theorem latticePoints_finite {H : ℝ} (hH : 0 ≤ H) : (latticePoints H).Finite := by
  set M : ℤ := ⌈H⌉ + 1
  refine ((Set.finite_Icc (-M) M).prod (Set.finite_Icc (-M) M)).subset ?_
  intro p hp
  rw [mem_latticePoints_iff] at hp
  simp only [region, ellipseForm, Set.mem_setOf_eq] at hp
  have hM : H + 1 / 3 ≤ (M : ℝ) := by
    have := Int.le_ceil H
    simp only [M, Int.cast_add, Int.cast_one]
    linarith
  have h1 : ((p.1 : ℝ) - 1 / 3) ^ 2 ≤ H ^ 2 := by
    nlinarith [sq_nonneg ((p.2 : ℝ) - 1 / 3 + ((p.1 : ℝ) - 1 / 3) / 2), sq_nonneg H]
  have h2 : ((p.2 : ℝ) - 1 / 3) ^ 2 ≤ H ^ 2 := by
    nlinarith [sq_nonneg ((p.1 : ℝ) - 1 / 3 + ((p.2 : ℝ) - 1 / 3) / 2), sq_nonneg H]
  obtain ⟨a1, b1⟩ := abs_le_of_sq_le_sq' h1 hH
  obtain ⟨a2, b2⟩ := abs_le_of_sq_le_sq' h2 hH
  have hM' : ((-M : ℤ) : ℝ) = -(M : ℝ) := Int.cast_neg M
  have c1 : ((-M : ℤ) : ℝ) ≤ (p.1 : ℝ) := by linarith
  have c2 : (p.1 : ℝ) ≤ (M : ℝ) := by linarith
  have c3 : ((-M : ℤ) : ℝ) ≤ (p.2 : ℝ) := by linarith
  have c4 : (p.2 : ℝ) ≤ (M : ℝ) := by linarith
  exact ⟨⟨by exact_mod_cast c1, by exact_mod_cast c2⟩, ⟨by exact_mod_cast c3, by exact_mod_cast c4⟩⟩

/-- The half-open unit square `[a, a+1) × [b, b+1)` attached to `(a, b) ∈ ℤ²`. -/
def cell (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Set.Ico (p.1 : ℝ) (p.1 + 1) ×ˢ Set.Ico (p.2 : ℝ) (p.2 + 1)

theorem mem_cell_iff (p : ℤ × ℤ) (z : ℝ × ℝ) : z ∈ cell p ↔ (⌊z.1⌋, ⌊z.2⌋) = p := by
  simp only [cell, Set.mem_prod, Set.mem_Ico, Prod.ext_iff, Int.floor_eq_iff]

theorem volume_cell (p : ℤ × ℤ) : volume (cell p) = 1 := by
  rw [cell, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
  simp

/-- The union of the cells at the points of a finite set has area equal to its size. -/
theorem volume_biUnion_cell (T : Finset (ℤ × ℤ)) :
    volume (⋃ p ∈ T, cell p) = T.card := by
  rw [measure_biUnion_finset]
  · simp [volume_cell]
  · intro p _ q _ hpq
    refine Set.disjoint_left.mpr fun z hp hq => hpq ?_
    rw [mem_cell_iff] at hp hq
    rw [← hp, ← hq]
  · intro p _
    exact measurableSet_Ico.prod measurableSet_Ico

/-- The strip estimate: a displacement of at most one in each coordinate
moves a point of `E_h°` into `E_{h+3}°`. -/
theorem mem_region_add_three {h : ℝ} (hh : 0 ≤ h) {z w : ℝ × ℝ}
    (h1 : |z.1 - w.1| ≤ 1) (h2 : |z.2 - w.2| ≤ 1) (hw : w ∈ region h) :
    z ∈ region (h + 3) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √3 := by positivity
  rw [mem_region_iff hh] at hw
  rw [mem_region_iff (by linarith)]
  set a := z.1 - w.1
  set b := z.2 - w.2
  have hsq : ‖ψ z - ψ w‖ ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    rw [ψ_sub, Complex.sq_norm, Complex.normSq_apply]
    linear_combination (b ^ 2 / 4) * h3
  have ha : a ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one a).mpr h1
  have hb : b ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one b).mpr h2
  have hab : a * b ≤ 1 := by
    have : |a * b| ≤ 1 := by
      rw [abs_mul]; exact mul_le_one₀ h1 (abs_nonneg _) h2
    exact (le_abs_self _).trans this
  have hd : ‖ψ z - ψ w‖ ≤ √3 := by
    rw [← sq_le_sq₀ (norm_nonneg _) hpos.le, hsq, h3]
    linarith
  have htri := norm_sub_norm_le (ψ z) (ψ w)
  have : (h + 3) / √3 = h / √3 + √3 := by
    field_simp
    rw [h3]
  rw [this]
  linarith

end Cubic.Counting.EllipseLatticeCells
