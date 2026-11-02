import Cubic.AllGaloisCounts.SliceScaling

/-! Counting integers in the actual closed interval for the marked
quadratic coefficient. Empty intervals and zero marked roots are included. -/

noncomputable section

namespace Cubic.AllGaloisCounts.IntegerIntervalCount
open CountData SliceScaling MeasureTheory

def integerPoints (s : Set ℝ) : Set ℤ := (fun n : ℤ => (n : ℝ)) ⁻¹' s

theorem integerPoints_Icc (a b : ℝ) :
    integerPoints (Set.Icc a b) = Set.Icc ⌈a⌉ ⌊b⌋ := by
  ext n
  simp only [integerPoints, Set.mem_preimage, Set.mem_Icc, Int.ceil_le, Int.le_floor]

theorem interval_error (a b : ℝ) :
    |((integerPoints (Set.Icc a b)).ncard : ℝ) - volume.real (Set.Icc a b)| ≤ 1 := by
  rw [integerPoints_Icc, Real.volume_real_Icc, ← Finset.coe_Icc, Set.ncard_coe_finset,
    Int.card_Icc]
  have ha := Int.le_ceil a
  have ha' := Int.ceil_lt_add_one a
  have hb := Int.floor_le b
  have hb' := Int.lt_floor_add_one b
  by_cases hn : 0 ≤ ⌊b⌋ + 1 - ⌈a⌉
  · rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
    push_cast
    rw [abs_le]
    have hn' : (⌈a⌉ : ℝ) ≤ ⌊b⌋ + 1 := by exact_mod_cast (by omega : ⌈a⌉ ≤ ⌊b⌋ + 1)
    by_cases hab : a ≤ b
    · rw [max_eq_left (sub_nonneg.mpr hab)]
      constructor <;> linarith
    · rw [max_eq_right (by linarith : b - a ≤ 0)]
      constructor <;> linarith
  · rw [Int.toNat_of_nonpos (by omega), Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (le_max_right _ _)]
    apply max_le _ (by norm_num)
    have hn' : (⌊b⌋ : ℝ) + 1 < ⌈a⌉ := by exact_mod_cast (by omega : ⌊b⌋ + 1 < ⌈a⌉)
    linarith

theorem allowedInterval_Icc {H : ℝ} (hH : 0 ≤ H) (a r : ℝ) :
    ∃ l u : ℝ, allowedInterval H a r = Set.Icc l u := by
  by_cases hr : r = 0
  · refine ⟨-H ^ 2, H ^ 2, ?_⟩
    subst r
    ext v
    simp [allowedInterval, abs_le, pow_nonneg hH 3]
  · refine ⟨max (r * (r + a) - H ^ 2) (- (H ^ 3 / |r|)),
      min (r * (r + a) + H ^ 2) (H ^ 3 / |r|), ?_⟩
    have he : ∀ v : ℝ, |r * v| ≤ H ^ 3 ↔ |v| ≤ H ^ 3 / |r| := by
      intro v
      rw [abs_mul, mul_comm, ← le_div_iff₀ (abs_pos.mpr hr)]
    ext v
    simp only [allowedInterval, Set.mem_setOf_eq, he, Set.mem_Icc, abs_le,
      max_le_iff, le_min_iff]
    constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;>
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

def vSet (H : ℝ) (a r : ℤ) : Set ℤ := integerPoints (allowedInterval H a r)

theorem vSet_finite {H : ℝ} (hH : 0 ≤ H) (a r : ℤ) : (vSet H a r).Finite := by
  obtain ⟨l, u, he⟩ := allowedInterval_Icc hH (a : ℝ) r
  rw [vSet, he, integerPoints_Icc]
  exact Set.finite_Icc _ _

theorem vSet_error {H : ℝ} (hH : 0 < H) (a r : ℤ) :
    |(Nat.card (vSet H a r) : ℝ) - H ^ 2 * F (r / H) (a / H)| ≤ 1 := by
  obtain ⟨l, u, he⟩ := allowedInterval_Icc hH.le (a : ℝ) r
  rw [← interval_length hH (a : ℝ) r, vSet, he, Nat.card_coe_set_eq]
  exact interval_error l u

end Cubic.AllGaloisCounts.IntegerIntervalCount
