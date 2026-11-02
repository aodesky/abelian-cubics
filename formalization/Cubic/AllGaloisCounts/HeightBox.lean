import Cubic.AllGaloisCounts.CountData
import Mathlib.Data.Int.Interval

/-! The coefficient box, its exact cardinality, and the real-root height
reduction used in the completely split count. -/

noncomputable section

namespace Cubic.AllGaloisCounts.HeightBox

open Polynomial CountData Cubic.Counting.GeneralMonicData
open Cubic.Counting.GeneralHeightReduction

theorem height_nonneg (f : ℤ[X]) : 0 ≤ weightedHeight f :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem height_iff {f : ℤ[X]} {H : ℝ} (hH : 0 ≤ H) :
    weightedHeight f ≤ H ↔ |(f.coeff 2 : ℝ)| ≤ H ∧
      |(f.coeff 1 : ℝ)| ≤ H ^ 2 ∧ |(f.coeff 0 : ℝ)| ≤ H ^ 3 := by
  have hpow : |(f.coeff 0 : ℝ)| ^ (1 / 3 : ℝ) ≤ H ↔
      |(f.coeff 0 : ℝ)| ≤ H ^ 3 := by
    simpa only [one_div, Real.rpow_ofNat] using
      (Real.rpow_inv_le_iff_of_pos (abs_nonneg (f.coeff 0 : ℝ)) hH (by norm_num : (0 : ℝ) < 3))
  simp only [weightedHeight, max_le_iff, Real.sqrt_le_left hH, hpow]

theorem int_abs_iff (n : ℤ) (t : ℝ) :
    |(n : ℝ)| ≤ t ↔ n ∈ Set.Icc (-⌊t⌋) ⌊t⌋ := by
  rw [abs_le, Set.mem_Icc]
  constructor
  · rintro ⟨hn, hp⟩
    have hm : -n ≤ ⌊t⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact ⟨by omega, Int.le_floor.mpr hp⟩
  · rintro ⟨hn, hp⟩
    have hm : ((-n : ℤ) : ℝ) ≤ t := Int.le_floor.mp (by omega : -n ≤ ⌊t⌋)
    push_cast at hm
    exact ⟨by linarith, Int.le_floor.mp hp⟩

def coefficientBox (H : ℝ) : Set (ℤ × ℤ × ℤ) :=
  Set.Icc (-⌊H⌋) ⌊H⌋ ×ˢ
    (Set.Icc (-⌊H ^ 2⌋) ⌊H ^ 2⌋ ×ˢ Set.Icc (-⌊H ^ 3⌋) ⌊H ^ 3⌋)

def coefficientPolynomial (a : ℤ × ℤ × ℤ) : ℤ[X] := monicCubic a.1 a.2.1 a.2.2

theorem coefficientPolynomial_injective : Function.Injective coefficientPolynomial := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ he
  have h2 := congrArg (fun f : ℤ[X] => f.coeff 2) he
  have h1 := congrArg (fun f : ℤ[X] => f.coeff 1) he
  have h0 := congrArg (fun f : ℤ[X] => f.coeff 0) he
  simp only [coefficientPolynomial, monicCubic_coeff_two, monicCubic_coeff_one,
    monicCubic_coeff_zero] at h2 h1 h0
  exact Prod.ext h2 (Prod.ext h1 h0)

theorem coefficient_bijOn {H : ℝ} (hH : 0 ≤ H) :
    Set.BijOn coefficientPolynomial (coefficientBox H) (cubicBox H) := by
  refine ⟨?_, coefficientPolynomial_injective.injOn, ?_⟩
  · rintro ⟨a, b, c⟩ ⟨ha, hb, hc⟩
    refine ⟨⟨a, b, c, rfl⟩, (height_iff hH).mpr ?_⟩
    simpa only [coefficientPolynomial, monicCubic_coeff_two, monicCubic_coeff_one,
      monicCubic_coeff_zero] using
      And.intro ((int_abs_iff a H).mpr ha)
        (And.intro ((int_abs_iff b (H ^ 2)).mpr hb) ((int_abs_iff c (H ^ 3)).mpr hc))
  · rintro f ⟨⟨a, b, c, rfl⟩, hf⟩
    have hh := (height_iff hH).mp hf
    simp only [monicCubic_coeff_two, monicCubic_coeff_one, monicCubic_coeff_zero] at hh
    exact ⟨(a, b, c), ⟨(int_abs_iff a H).mp hh.1,
      (int_abs_iff b (H ^ 2)).mp hh.2.1, (int_abs_iff c (H ^ 3)).mp hh.2.2⟩, rfl⟩

theorem coefficientBox_finite (H : ℝ) : (coefficientBox H).Finite :=
  (Set.finite_Icc _ _).prod ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))

theorem cubicBox_finite (H : ℝ) : (cubicBox H).Finite := by
  by_cases hH : 0 ≤ H
  · rw [← (coefficient_bijOn hH).image_eq]
    exact (coefficientBox_finite H).image _
  · have he : cubicBox H = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro f hf
      exact hH ((height_nonneg f).trans hf.2)
    rw [he]
    exact Set.finite_empty

theorem galoisSet_finite (G : GaloisType) (H : ℝ) : (galoisSet G H).Finite :=
  (cubicBox_finite H).subset (fun _ hf => hf.1)

theorem interval_card {t : ℝ} (ht : 0 ≤ t) :
    ((Set.Icc (-⌊t⌋) ⌊t⌋).ncard : ℝ) = 2 * (⌊t⌋ : ℝ) + 1 := by
  have hf : 0 ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  push_cast
  ring

theorem box_count {H : ℝ} (hH : 0 ≤ H) :
    (Nat.card (cubicBox H) : ℝ) = boxFormula H := by
  rw [← Nat.card_congr (coefficient_bijOn hH).equiv, Nat.card_coe_set_eq,
    coefficientBox, Set.ncard_prod, Set.ncard_prod, Nat.cast_mul, Nat.cast_mul,
    interval_card hH, interval_card (sq_nonneg H), interval_card (pow_nonneg hH 3)]
  norm_num [boxFormula, Finset.prod_Icc_succ_top]
  ring

/-- The arithmetic-geometric-mean step holds for any three real roots, including
coincident roots; it does not use the cyclic Galois condition. -/
theorem real_root_bounds {a b c x y z H : ℝ}
    (ha : a = -(x + y + z)) (hb : b = x * y + x * z + y * z)
    (hc : c = -(x * y * z)) (hs : |a| ≤ H) (hb_lower : -H ^ 2 ≤ b) :
    |b| ≤ H ^ 2 ∧ |c| ≤ H ^ 3 := by
  have hH : 0 ≤ H := (abs_nonneg a).trans hs
  have ha2 : a ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  have hinv : 0 ≤ a ^ 2 - 3 * b := by
    rw [ha, hb]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  refine ⟨abs_le.mpr ⟨hb_lower, by nlinarith⟩, ?_⟩
  have hsum : x ^ 2 + y ^ 2 + z ^ 2 ≤ 3 * H ^ 2 := by
    have he : x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 - 2 * b := by rw [ha, hb]; ring
    rw [he]
    linarith
  have hsq : c ^ 2 ≤ (H ^ 3) ^ 2 := by
    have h := amgm (sq_nonneg x) (sq_nonneg y) (sq_nonneg z)
    have hm : ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ^ 3 ≤ (H ^ 2) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    calc c ^ 2 = x ^ 2 * y ^ 2 * z ^ 2 := by rw [hc]; ring
      _ ≤ (H ^ 2) ^ 3 := h.trans hm
      _ = (H ^ 3) ^ 2 := by ring
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))

def splitCubic (x y z : ℤ) : ℤ[X] :=
  monicCubic (-(x + y + z)) (x * y + x * z + y * z) (-(x * y * z))

theorem splitCubic_factorization (x y z : ℤ) :
    splitCubic x y z = (X - C x) * (X - C y) * (X - C z) := by
  simp only [splitCubic, monicCubic, map_neg, map_add, map_mul]
  ring

/-- The actual ellipse used for each integral trace in the paper's proof. -/
theorem split_height_ellipse (x y s : ℤ) (H : ℝ) :
    weightedHeight (splitCubic x y (s - x - y)) ≤ H ↔ |(s : ℝ)| ≤ H ∧
      ((x : ℝ) - s / 3) ^ 2 + ((x : ℝ) - s / 3) * ((y : ℝ) - s / 3) +
        ((y : ℝ) - s / 3) ^ 2 ≤ H ^ 2 + (s : ℝ) ^ 2 / 3 := by
  by_cases hH : 0 ≤ H
  · rw [height_iff hH]
    simp only [splitCubic, monicCubic_coeff_two, monicCubic_coeff_one, monicCubic_coeff_zero]
    push_cast
    have hs : -((x : ℝ) + y + (s - x - y)) = -(s : ℝ) := by ring
    rw [hs, abs_neg]
    constructor
    · rintro ⟨ht, hb, -⟩
      exact ⟨ht, by nlinarith [(abs_le.mp hb).1]⟩
    · rintro ⟨ht, he⟩
      have hb : -H ^ 2 ≤ (x : ℝ) * y + x * (s - x - y) + y * (s - x - y) := by
        nlinarith
      exact ⟨ht, real_root_bounds (by ring : -(s : ℝ) = -(x + y + (s - x - y)))
        rfl rfl (by simpa only [abs_neg] using ht) hb⟩
  · have hn : H < 0 := lt_of_not_ge hH
    exact iff_of_false (fun h => hH ((height_nonneg _).trans h))
      (fun h => hH ((abs_nonneg _).trans h.1))

end Cubic.AllGaloisCounts.HeightBox
