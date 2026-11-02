import Cubic.Counting.EllipseLatticeCells

/-!
# Lattice points in `x² + xy + y² ≤ X`

Supporting count for `prop:traceZeroAsymptotic`: the ellipse `x² + xy + y² ≤ X` has area
`2πX/√3` and contains `2πX/√3 + O(X^{1/2})` lattice points for `X ≥ 1`.

The ellipse is the translate by `(-1/3, -1/3)` of the region `E_h°` of
`eqn:ellipseLatticeCount` with `h = √(3X)`, since
`x² + y² + xy - x - y = (x - 1/3)² + (x - 1/3)(y - 1/3) + (y - 1/3)² - 1/3`. The argument is
the one used there: the unit cells at the lattice points have total area equal to their
number and lie between the translates of `E_{h-3}°` and `E_{h+3}°`.
-/

noncomputable section

namespace Cubic.Counting.CenteredEllipseCount

open MeasureTheory Real Cubic.Counting.EllipseArea Cubic.Counting.EllipseLatticeCells

/-- The quadratic form `x² + xy + y²`. -/
def form (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2

/-- Lattice points with `x² + xy + y² ≤ X`. -/
def points (X : ℝ) : Set (ℤ × ℤ) := {p | form ((p.1 : ℝ), (p.2 : ℝ)) ≤ X}

/-- The translation by `(1/3, 1/3)`. -/
def shift (z : ℝ × ℝ) : ℝ × ℝ := z + (1 / 3, 1 / 3)

theorem mem_region_shift {X : ℝ} (hX : 0 ≤ X) (z : ℝ × ℝ) :
    shift z ∈ region (√(3 * X)) ↔ form z ≤ X := by
  simp only [region, Set.mem_setOf_eq, ellipseForm, shift, form, Prod.fst_add, Prod.snd_add,
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 3 * X)]
  constructor <;> intro h <;> linarith

/-- A coordinate of a lattice point of `x² + xy + y² ≤ X` is at most `2|X|` in size. -/
theorem abs_le_of_form {a b : ℤ} {X : ℝ} (h : form ((a : ℝ), (b : ℝ)) ≤ X) :
    |(a : ℝ)| ≤ 2 * |X| := by
  simp only [form] at h
  have ha : |(a : ℝ)| ≤ (a : ℝ) ^ 2 := by
    rw [← sq_abs]; exact_mod_cast (by
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      · nlinarith [Int.one_le_abs ha, abs_nonneg a] : |a| ≤ |a| ^ 2)
  nlinarith [sq_nonneg ((a : ℝ) + 2 * b), le_abs_self X]

theorem points_finite (X : ℝ) : (points X).Finite := by
  refine ((Set.finite_Icc (-⌈2 * |X|⌉) ⌈2 * |X|⌉).prod
    (Set.finite_Icc (-⌈2 * |X|⌉) ⌈2 * |X|⌉)).subset ?_
  rintro ⟨a, b⟩ (h : form ((a : ℝ), (b : ℝ)) ≤ X)
  have h' : form ((b : ℝ), (a : ℝ)) ≤ X := by simp only [form] at h ⊢; linarith
  have hc := Int.le_ceil (2 * |X|)
  have key : ∀ x : ℤ, |(x : ℝ)| ≤ 2 * |X| → -⌈2 * |X|⌉ ≤ x ∧ x ≤ ⌈2 * |X|⌉ := fun x hx => by
    rw [abs_le] at hx
    constructor
    · have : ((-⌈2 * |X|⌉ : ℤ) : ℝ) ≤ x := by push_cast; linarith
      exact_mod_cast this
    · have : (x : ℝ) ≤ ((⌈2 * |X|⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  exact ⟨key a (abs_le_of_form h), key b (abs_le_of_form h')⟩

theorem volume_shift_preimage (h : ℝ) : volume (shift ⁻¹' region h) = volume (region h) :=
  measure_preimage_add_right _ _ _

theorem biUnion_cell_subset {X : ℝ} (hX : 0 ≤ X) :
    (⋃ p ∈ (points_finite X).toFinset, cell p) ⊆ shift ⁻¹' region (√(3 * X) + 3) := by
  intro z hz
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset] at hz
  obtain ⟨p, hp, hzp⟩ := hz
  simp only [cell, Set.mem_prod, Set.mem_Ico] at hzp
  have hw : shift ((p.1 : ℝ), (p.2 : ℝ)) ∈ region (√(3 * X)) := (mem_region_shift hX _).mpr hp
  refine mem_region_add_three (Real.sqrt_nonneg _) ?_ ?_ hw <;>
    · simp only [shift, Prod.fst_add, Prod.snd_add]; rw [abs_le]; constructor <;> linarith

theorem subset_biUnion_cell {X : ℝ} (hX : 0 ≤ X) (h3 : 3 ≤ √(3 * X)) :
    shift ⁻¹' region (√(3 * X) - 3) ⊆ ⋃ p ∈ (points_finite X).toFinset, cell p := by
  intro z hz
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
  refine ⟨(⌊z.1⌋, ⌊z.2⌋), ?_, (mem_cell_iff _ _).mpr rfl⟩
  have f1 := Int.floor_le z.1
  have f1' := Int.lt_floor_add_one z.1
  have f2 := Int.floor_le z.2
  have f2' := Int.lt_floor_add_one z.2
  have h := mem_region_add_three (by linarith) (w := shift z)
    (z := shift ((⌊z.1⌋ : ℝ), (⌊z.2⌋ : ℝ)))
    (by simp only [shift, Prod.fst_add]; rw [abs_le]; constructor <;> linarith)
    (by simp only [shift, Prod.snd_add]; rw [abs_le]; constructor <;> linarith) hz
  rw [sub_add_cancel, mem_region_shift hX] at h
  exact h

/-- `#{(x, y) ∈ ℤ² : x² + xy + y² ≤ X} = 2πX/√3 + O(X^{1/2})` for `X ≥ 1`. -/
theorem count_bound : ∃ K : ℝ, ∀ X : ℝ, 1 ≤ X →
    |(Nat.card (points X) : ℝ) - 2 * π / √3 * X| ≤ K * √X := by
  set α : ℝ := 2 * π / (3 * √3)
  have hα : 0 < α := by positivity
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨6 * α * √3 + 9 * α, fun X hX => ?_⟩
  have hX0 : (0 : ℝ) ≤ X := by linarith
  set h := √(3 * X) with hh
  have hh0 : 0 ≤ h := Real.sqrt_nonneg _
  have hhX : h = √3 * √X := by rw [hh, Real.sqrt_mul (by norm_num)]
  have hsX : 1 ≤ √X := Real.one_le_sqrt.mpr hX
  have hh2 : h ^ 2 = 3 * X := Real.sq_sqrt (by linarith)
  have hmain : 2 * π / √3 * X = α * h ^ 2 := by
    rw [hh2]; simp only [α]; field_simp
  set N : ℝ := (Nat.card (points X) : ℝ)
  have hfin := points_finite X
  have hN : ENNReal.ofReal N = volume (⋃ p ∈ hfin.toFinset, cell p) := by
    rw [volume_biUnion_cell, ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq,
      ENNReal.ofReal_natCast]
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hup : N ≤ α * (h + 3) ^ 2 := by
    have := measure_mono (μ := volume) (biUnion_cell_subset hX0)
    rw [← hN, volume_shift_preimage, volume_region (by linarith),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    exact this
  have hlow : α * h ^ 2 - 6 * α * h ≤ N := by
    rcases le_or_gt 3 h with h3 | h3
    · have := measure_mono (μ := volume) (subset_biUnion_cell hX0 h3)
      rw [← hN, volume_shift_preimage, volume_region (by linarith),
        ENNReal.ofReal_le_ofReal_iff hN0] at this
      nlinarith
    · nlinarith [mul_nonneg (mul_nonneg hα.le hh0) (by linarith : (0 : ℝ) ≤ 6 - h)]
  rw [hmain, abs_le]
  have hb : 6 * α * h + 9 * α ≤ (6 * α * √3 + 9 * α) * √X := by
    rw [hhX]; nlinarith
  constructor <;> nlinarith

end Cubic.Counting.CenteredEllipseCount
