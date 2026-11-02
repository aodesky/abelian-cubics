import Cubic.Counting.CenteredEllipseCount

/-! The paper's unit-square comparison, uniformly over translated ellipses.
The area and cell estimates are reused from the earlier trace-zero argument;
only the center is allowed to vary. -/

noncomputable section

namespace Cubic.AllGaloisCounts.TranslatedEllipseCount
open MeasureTheory Real Cubic.Counting.EllipseArea Cubic.Counting.EllipseLatticeCells
open Cubic.Counting.CenteredEllipseCount (form)

def points (c : ℝ × ℝ) (X : ℝ) : Set (ℤ × ℤ) :=
  {p | form (((p.1 : ℝ), (p.2 : ℝ)) - c) ≤ X}

def shift (c z : ℝ × ℝ) : ℝ × ℝ := z + ((1 / 3, 1 / 3) - c)

theorem mem_region_shift {X : ℝ} (hX : 0 ≤ X) (c z : ℝ × ℝ) :
    shift c z ∈ region (√(3 * X)) ↔ form (z - c) ≤ X := by
  simp only [region, Set.mem_setOf_eq, ellipseForm, shift, form, Prod.fst_add,
    Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 3 * X)]
  constructor <;> intro h <;> nlinarith

theorem coordinate_bound {x y X : ℝ} (h : x ^ 2 + x * y + y ^ 2 ≤ X) :
    |x| ≤ 2 * √|X| := by
  have hs : x ^ 2 ≤ (2 * √|X|) ^ 2 := by
    nlinarith [sq_nonneg (x + 2 * y), Real.sq_sqrt (abs_nonneg X), le_abs_self X]
  exact abs_le.mpr (abs_le_of_sq_le_sq' hs (by positivity))

theorem points_finite (c : ℝ × ℝ) (X : ℝ) : (points c X).Finite := by
  let B := 2 * √|X| + max |c.1| |c.2|
  refine ((Set.finite_Icc (-⌈B⌉) ⌈B⌉).prod (Set.finite_Icc (-⌈B⌉) ⌈B⌉)).subset ?_
  rintro ⟨a, b⟩ (h : form (((a : ℝ), (b : ℝ)) - c) ≤ X)
  simp only [form, Prod.fst_sub, Prod.snd_sub] at h
  have hx := coordinate_bound h
  have hy := coordinate_bound (x := (b : ℝ) - c.2) (y := (a : ℝ) - c.1)
    (by nlinarith : ((b : ℝ) - c.2) ^ 2 + ((b : ℝ) - c.2) * ((a : ℝ) - c.1) +
      ((a : ℝ) - c.1) ^ 2 ≤ X)
  have key : ∀ n : ℤ, |(n : ℝ)| ≤ B → -⌈B⌉ ≤ n ∧ n ≤ ⌈B⌉ := by
    intro n hn
    have hp : (n : ℝ) ≤ ⌈B⌉ := (le_abs_self _).trans (hn.trans (Int.le_ceil B))
    have hm : ((-n : ℤ) : ℝ) ≤ ⌈B⌉ := by
      push_cast
      exact (neg_le_abs _).trans (hn.trans (Int.le_ceil B))
    have hp' : n ≤ ⌈B⌉ := by exact_mod_cast hp
    have hm' : -n ≤ ⌈B⌉ := by exact_mod_cast hm
    exact ⟨by omega, hp'⟩
  refine ⟨key a ?_, key b ?_⟩
  · calc |(a : ℝ)| = |((a : ℝ) - c.1) + c.1| := by congr 1; ring
      _ ≤ |(a : ℝ) - c.1| + |c.1| := abs_add_le _ _
      _ ≤ B := add_le_add hx (le_max_left _ _)
  · calc |(b : ℝ)| = |((b : ℝ) - c.2) + c.2| := by congr 1; ring
      _ ≤ |(b : ℝ) - c.2| + |c.2| := abs_add_le _ _
      _ ≤ B := add_le_add hy (le_max_right _ _)

theorem volume_shift_preimage (c : ℝ × ℝ) (h : ℝ) :
    volume (shift c ⁻¹' region h) = volume (region h) :=
  measure_preimage_add_right _ _ _

theorem biUnion_cell_subset {X : ℝ} (hX : 0 ≤ X) (c : ℝ × ℝ) :
    (⋃ p ∈ (points_finite c X).toFinset, cell p) ⊆ shift c ⁻¹' region (√(3 * X) + 3) := by
  intro z hz
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset] at hz
  obtain ⟨p, hp, hzp⟩ := hz
  simp only [cell, Set.mem_prod, Set.mem_Ico] at hzp
  have hw : shift c ((p.1 : ℝ), (p.2 : ℝ)) ∈ region (√(3 * X)) :=
    (mem_region_shift hX _ _).mpr hp
  refine mem_region_add_three (Real.sqrt_nonneg _) ?_ ?_ hw <;>
    · simp only [shift, Prod.fst_add, Prod.snd_add]
      rw [abs_le]
      constructor <;> linarith

theorem subset_biUnion_cell {X : ℝ} (hX : 0 ≤ X) (h3 : 3 ≤ √(3 * X)) (c : ℝ × ℝ) :
    shift c ⁻¹' region (√(3 * X) - 3) ⊆ ⋃ p ∈ (points_finite c X).toFinset, cell p := by
  intro z hz
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
  refine ⟨(⌊z.1⌋, ⌊z.2⌋), ?_, (mem_cell_iff _ _).mpr rfl⟩
  have f1 := Int.floor_le z.1
  have f1' := Int.lt_floor_add_one z.1
  have f2 := Int.floor_le z.2
  have f2' := Int.lt_floor_add_one z.2
  have h := mem_region_add_three (by linarith) (w := shift c z)
    (z := shift c ((⌊z.1⌋ : ℝ), (⌊z.2⌋ : ℝ)))
    (by simp only [shift, Prod.fst_add]; rw [abs_le]; constructor <;> linarith)
    (by simp only [shift, Prod.snd_add]; rw [abs_le]; constructor <;> linarith) hz
  rw [sub_add_cancel, mem_region_shift hX] at h
  exact h

/-- The constant is independent of the center, so it is uniform in the trace. -/
theorem count_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ × ℝ, ∀ X : ℝ, 1 ≤ X →
    |(Nat.card (points c X) : ℝ) - 2 * π / √3 * X| ≤ K * √X := by
  set α : ℝ := 2 * π / (3 * √3)
  have hα : 0 < α := by positivity
  refine ⟨6 * α * √3 + 9 * α, by positivity, fun c X hX => ?_⟩
  have hX0 : (0 : ℝ) ≤ X := by linarith
  set h := √(3 * X) with hh
  have hh0 : 0 ≤ h := Real.sqrt_nonneg _
  have hhX : h = √3 * √X := by rw [hh, Real.sqrt_mul (by norm_num)]
  have hsX : 1 ≤ √X := Real.one_le_sqrt.mpr hX
  have hh2 : h ^ 2 = 3 * X := Real.sq_sqrt (by linarith)
  have hmain : 2 * π / √3 * X = α * h ^ 2 := by
    rw [hh2]; simp only [α]; field_simp
  set N : ℝ := (Nat.card (points c X) : ℝ)
  have hfin := points_finite c X
  have hN : ENNReal.ofReal N = volume (⋃ p ∈ hfin.toFinset, cell p) := by
    rw [volume_biUnion_cell, ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq,
      ENNReal.ofReal_natCast]
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hup : N ≤ α * (h + 3) ^ 2 := by
    have := measure_mono (μ := volume) (biUnion_cell_subset hX0 c)
    rw [← hN, volume_shift_preimage, volume_region (by linarith),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    exact this
  have hlow : α * h ^ 2 - 6 * α * h ≤ N := by
    rcases le_or_gt 3 h with h3 | h3
    · have := measure_mono (μ := volume) (subset_biUnion_cell hX0 h3 c)
      rw [← hN, volume_shift_preimage, volume_region (by linarith),
        ENNReal.ofReal_le_ofReal_iff hN0] at this
      nlinarith
    · nlinarith [mul_nonneg (mul_nonneg hα.le hh0) (by linarith : (0 : ℝ) ≤ 6 - h)]
  rw [hmain, abs_le]
  have hb : 6 * α * h + 9 * α ≤ (6 * α * √3 + 9 * α) * √X := by
    rw [hhX]; nlinarith
  constructor <;> nlinarith

end Cubic.AllGaloisCounts.TranslatedEllipseCount
