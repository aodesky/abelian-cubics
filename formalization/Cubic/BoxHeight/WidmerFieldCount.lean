import Cubic.BoxHeight.FieldCount
import CubicTargets.BoxHeight.WidmerBlackBox
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The polynomial count of one cyclic cubic field

The second formula of `lem:widmer` in `box_height_research_note.tex`, as a lower bound. Let `K`
be a totally real cyclic cubic field and `c > 0` with `B_K ≥ 8/c` (for the note's fields
`B_K = 8/c_K`). The unit rank is `2`, so [Widmer 2016, Theorem 1.1] (`WidmerBlackBox`) gives
`#{α ∈ 𝒪_K : M(α) ≤ Y} ≥ B_K Y (1 + 2 log Y + ½ (log Y)²) − c₁ X² (log⁺ X)²` with `Y = X³`, and
`#{α} ≤ 2X + 1 + 3 P_K(Y)` (`FieldCount.count_le`). Hence
`3 P_K(Y) ≥ (4/c) Y (log Y)² − c₁ X² (log⁺ X)² − 2X − 1`, with `c₁` independent of `K`.
-/

noncomputable section

namespace Cubic.BoxHeight.WidmerFieldCount

open NumberField Polynomial CubicTargets.BoxHeight
open Cubic.BoxHeight.FieldPolynomials Cubic.BoxHeight.FieldCount

theorem rank_eq_two {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (h3 : Module.finrank ℚ K = 3) : Units.rank K = 2 := by
  rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, ← IsTotallyReal.finrank, h3]

/-- `B_K = 8/√|Δ_K|` for a totally real cubic field, so `|Δ_K| ≤ c²` gives `B_K ≥ 8/c`. -/
theorem B_ge {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (h3 : Module.finrank ℚ K = 3) {c : ℝ} (hc : 0 < c) (hΔ : |(discr K : ℝ)| ≤ c ^ 2) :
    8 / c ≤ WidmerBlackBox.B K := by
  have hΔ0 : 0 < |(discr K : ℝ)| := by
    rw [abs_pos]; exact_mod_cast discr_ne_zero K
  have hsq : Real.sqrt |(discr K : ℝ)| ≤ c := by
    rw [Real.sqrt_le_left hc.le]; exact hΔ
  rw [WidmerBlackBox.B, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
    ← IsTotallyReal.finrank, h3]
  norm_num
  exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hΔ0) hsq

/-- The lower bound for one field, with a constant `c₁` independent of the field. -/
theorem card_polySet_ge (hW : WidmerBlackBox.BlackBox) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] [IsTotallyReal K],
      Module.finrank ℚ K = 3 → ∀ c : ℝ, 0 < c → 8 / c ≤ WidmerBlackBox.B K → ∀ X : ℝ, 1 ≤ X →
        4 / c * X ^ 3 * Real.log (X ^ 3) ^ 2 - c₁ * X ^ 2 * max 1 (Real.log X) ^ 2 -
          2 * X - 1 ≤ 3 * (Nat.card (polySet K (X ^ 3)) : ℝ) := by
  obtain ⟨c₁, hc₁, hW⟩ := hW
  refine ⟨c₁, hc₁, fun K _ _ _ _ h3 c hc hB X hX => ?_⟩
  have hb := hW K h3 inferInstance X hX
  rw [rank_eq_two h3] at hb
  have hX0 : 0 < X := by linarith
  set Y := X ^ 3
  have hY1 : 1 ≤ Y := one_le_pow₀ hX
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hB0 : 0 ≤ WidmerBlackBox.B K := le_trans (by positivity) hB
  -- the main term is at least `D₂ Y (log Y)² ≥ (4/c) Y (log Y)²`
  have hmain : 4 / c * Y * Real.log Y ^ 2 ≤
      ∑ i ∈ Finset.range (2 + 1), WidmerBlackBox.D K i * Y * Real.log Y ^ i := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, WidmerBlackBox.D, rank_eq_two h3]
    norm_num
    have h0 : 0 ≤ WidmerBlackBox.B K * Y := mul_nonneg hB0 (by positivity)
    have h1 : 0 ≤ WidmerBlackBox.B K * 2 * Y * Real.log Y :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity)) hlog
    have h2 : 4 / c * Y * Real.log Y ^ 2 ≤ WidmerBlackBox.B K / 2 * Y * Real.log Y ^ 2 := by
      have : 4 / c ≤ WidmerBlackBox.B K / 2 := by
        have := div_le_div_of_nonneg_right hB (by norm_num : (0 : ℝ) ≤ 2)
        calc 4 / c = 8 / c / 2 := by ring
          _ ≤ _ := this
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity))
        (by positivity)
    nlinarith
  have hcount := count_le h3 Y (by positivity)
  have hX13 : Y ^ (1 / 3 : ℝ) = X := by
    simp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  rw [hX13] at hcount
  rw [abs_le] at hb
  linarith [hb.1]

end Cubic.BoxHeight.WidmerFieldCount
