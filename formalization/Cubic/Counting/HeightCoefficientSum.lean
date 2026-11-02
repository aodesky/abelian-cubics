import Cubic.Counting.XiMeanValue
import Cubic.Counting.HeightCoefficientMeanValue
import Cubic.Counting.CountPolynomialNormalization
import Cubic.Counting.HeightCoefficientBounds
import Cubic.Counting.HeightCoefficientContinuation
import Cubic.Counting.HeightCoefficientContour
import Cubic.Analysis.DoublePoleRectangle
import Cubic.Analysis.ZetaStripGrowth
import Cubic.Analysis.PerronHalfInteger
import Cubic.Analysis.MeanValueExtension
import CubicTargets.Counting.HeightCoefficientSum

/-!
# `eqn:dSummatoryForGeneralTrace`

Direct proof retained at the author's request (2026-10-19). The printed
paper invokes Alberts, Theorem 1.1; Lean uses the following approved alternative:
truncated Perron and contour shifting, with no Tauberian theorem assumed.

1. `𝒵(s) = ζ_E(s)² E(2s)` with `E(2s)` bounded on `Re s ≥ β`; with the mean value on
   the lines `β ≤ σ ≤ 2` this gives `∫_U^{2U} |𝒵(σ+it)| dt ≪ U^{1+η}`
   (`HeightCoefficientMeanValue.calZ_mean`, the bounded-strip part of
   `eqn:heightMeanBound`).
2. Truncated Perron at half-integers `X`, with `c = 1 + 1/log X`, using `d_n ≪ n^η`
   and `𝒵(c) ≪ (log X)²` (`series_bound`).
3. A height `T ∈ [X, 2X]` with small horizontal integrals, the dyadic bound on
   `Re s = β`, and the residue `A X log X + (B - A) X` at the double pole `s = 1`.
4. General `X`: replace it by `⌊X⌋ + 1/2`.

The strip mean value is `lemma:xiMeanValue`, proved by the Gaussian
contour argument with a reflected kernel using Chandrasekharan–Narasimhan Theorem 4. The Poisson input enters through
`prop:leadingTerms` and the coefficient formula.
-/

noncomputable section

namespace Cubic.Counting.HeightCoefficientSum

open Complex MeasureTheory Set Filter
open Cubic.Counting.HeightCoefficientData Cubic.Counting.HeightCoefficientContour
open CubicTargets.PoissonSummation.LeadingTerms
open Cubic.Counting.HeightCoefficientMeanValue

theorem calZ_conj' : ∀ s ∈ region, calZ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (calZ s) :=
  fun s hs => HeightCoefficientContinuation.calZ_conj s hs.1 hs.2

theorem one_le_log {X : ℝ} (hX : 3 ≤ X) : 1 ≤ Real.log X := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- `𝒵(c) ≪ (log X)²` at `c = 1 + 1/log X`, as a bound on the real Dirichlet series. -/
theorem series_bound (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    ∃ B : ℝ, ∀ X : ℝ, 3 ≤ X →
      ∑' n : ℕ, d n / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ B * Real.log X ^ 2 := by
  obtain ⟨D, F, γ, c₂, c₁, hE⟩ := Cubic.PoissonSummation.leadingTerms_expansion hPoisson
  obtain ⟨C, hC⟩ := HeightCoefficientBounds.correction_bounded 1 (by norm_num)
  refine ⟨4 * C, fun X hX => ?_⟩
  have hL := one_le_log hX
  set c : ℝ := 1 + 1 / Real.log X with hc
  have hc1 : 1 < c := by have : 0 < 1 / Real.log X := by positivity
                         linarith
  have hcast : ((∑' n : ℕ, d n / (n : ℝ) ^ c : ℝ) : ℂ) = LSeries (fun n => (d n : ℂ)) c := by
    rw [Complex.ofReal_tsum, LSeries]
    congr 1
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, Real.zero_rpow (by linarith : c ≠ 0)]
    · rw [LSeries.term_of_ne_zero hn.ne', Complex.ofReal_div,
        Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
  have hZ : LSeries (fun n => (d n : ℂ)) c = calZ c :=
    HeightCoefficientContinuation.LSeries_eq hE c (by simpa using hc1)
  have hle : ∑' n : ℕ, d n / (n : ℝ) ^ c ≤ ‖calZ c‖ := by
    rw [← hZ, ← hcast, Complex.norm_real]
    exact Real.le_norm_self _
  have hzeta : ‖zetaE c‖ ≤ 2 * Real.log X := by
    rw [zetaE, norm_mul]
    have h1 := Cubic.Analysis.ZetaStripGrowth.riemannZeta_real_le c hc1
    have h2 := Cubic.Analysis.ZetaStripGrowth.LFunction_real_le c hc1
    have hc' : 1 / (c - 1) = Real.log X := by rw [hc]; field_simp; ring
    rw [hc'] at h1
    calc ‖riemannZeta c‖ * ‖DirichletCharacter.LFunction
          Cubic.PoissonSummation.QuadraticDirichletCharacter.character c‖
        ≤ (1 + Real.log X) * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
      _ ≤ 2 * Real.log X := by linarith
  have hcor : ‖Cubic.PoissonSummation.LeadingTermsData.correction (2 * c)‖ ≤ C :=
    hC c (by simp; linarith)
  calc ∑' n : ℕ, d n / (n : ℝ) ^ c ≤ ‖calZ c‖ := hle
    _ = ‖zetaE c‖ ^ 2 * ‖Cubic.PoissonSummation.LeadingTermsData.correction (2 * c)‖ := by
        rw [calZ, norm_mul, norm_pow]
    _ ≤ (2 * Real.log X) ^ 2 * C :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzeta 2) hcor (norm_nonneg _) (by positivity)
    _ = 4 * C * Real.log X ^ 2 := by ring

/-- The main term `A X log X + (B - A) X` with `A = c₂/4`, `B = c₁/2`. -/
def mainTerm (c₂ c₁ : ℂ) (X : ℝ) : ℂ := c₂ / 4 * X * Real.log X + (c₁ / 2 - c₂ / 4) * X

theorem rpow_inv_log {X : ℝ} (hX : 1 < X) : X ^ (1 / Real.log X) = Real.exp 1 := by
  rw [Real.rpow_def_of_pos (by linarith)]
  congr 1
  have : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  field_simp

/-- The contour-shift estimate at half-integers. -/
theorem half_integer_bound
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    {D F : ℂ → ℂ} {γ c₂ c₁ : ℂ} (hE : Expansion D F γ c₂ c₁)
    {δ η : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hη : 0 < η) (hstrip : StripMean δ η) :
    ∃ K : ℝ, ∀ m : ℕ, ∀ X : ℝ, X = m + 1 / 2 → 3 ≤ X →
      ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (d n : ℂ)) - mainTerm c₂ c₁ X‖ ≤
        K * (X ^ η * Real.log X ^ 2 + X ^ η + X ^ (1 / 2 + δ + η)) := by
  set β : ℝ := 1 / 2 + δ with hβdef
  have hβ : 1 / 2 < β := by linarith
  have hβ1 : β < 1 := by linarith
  obtain ⟨KZ, hKZ⟩ := calZ_mean hδ hstrip
  obtain ⟨B, hB⟩ := series_bound hPoisson
  obtain ⟨K₁, hK₁⟩ := Cubic.Analysis.Perron.norm_sum_sub_perronIntegral_halfInteger_le d
    HeightCoefficientBounds.d_nonneg (HeightCoefficientBounds.d_le_rpow hPoisson) B hB η hη
  obtain ⟨CL, hCL⟩ := left_bound (Z := calZ) hβ hβ1 hη calZ_continuousOn calZ_conj'
    (hKZ β le_rfl (by linarith))
  refine ⟨|K₁| + 4 * Real.exp 1 * |KZ| + 2 ^ η * |CL|, fun m X hXm hX3 => ?_⟩
  have hX0 : 0 < X := by linarith
  have hL := one_le_log hX3
  set c : ℝ := 1 + 1 / Real.log X with hc
  have hc1 : 1 < c := by have : 0 < 1 / Real.log X := by positivity
                         linarith
  have hc2 : c ≤ 2 := by
    have : 1 / Real.log X ≤ 1 := by rw [div_le_one (by linarith)]; exact hL
    linarith
  obtain ⟨T, hT, hTop, hBot⟩ := exists_height (Z := calZ) hβ calZ_continuousOn calZ_conj' hKZ
    X c (by linarith) (by linarith) hc2
  have hT0 : 0 < T := by linarith [hT.1]
  set g : ℂ → ℂ := fun s => calZ s * (X : ℂ) ^ s / s with hg
  -- the rectangle residue
  have hrect := Cubic.Analysis.DoublePoleRectangle.rectangle_double_pole (f := calZ)
    (A := c₂ / 4) (B := c₁ / 2) (by linarith : 0 < β) hβ1 hc1 hT0 hX0
    (U := {s : ℂ | (1 / 2 : ℝ) < s.re}) (isOpen_lt continuous_const Complex.continuous_re)
    (fun s hs => by
      simp only [Complex.Rectangle, Complex.mem_reProdIm] at hs
      simp only [mem_setOf_eq]
      have := hs.1.1
      simp at this
      rcases this with h | h <;> linarith)
    HeightCoefficientContinuation.calZ_differentiableOn
    (HeightCoefficientContinuation.calZ_laurent hE)
  rw [Cubic.Analysis.DoublePoleRectangle.rectangleIntegral_eq] at hrect
  set Hb := ∫ x in β..c, calZ (↑x + -↑T * I) * (X : ℂ) ^ ((x : ℂ) + -↑T * I) / (↑x + -↑T * I)
    with hHb
  set Ht := ∫ x in β..c, calZ (↑x + ↑T * I) * (X : ℂ) ^ ((x : ℂ) + ↑T * I) / (↑x + ↑T * I)
    with hHt
  set V := ∫ t in (-T)..T, calZ (↑c + ↑t * I) * (X : ℂ) ^ ((c : ℂ) + ↑t * I) / (↑c + ↑t * I)
    with hV
  set Lv := ∫ t in (-T)..T, calZ (↑β + ↑t * I) * (X : ℂ) ^ ((β : ℂ) + ↑t * I) / (↑β + ↑t * I)
    with hLv
  -- the Perron integral is the right side of the rectangle
  have hperron : Cubic.Analysis.Perron.perronIntegral (fun n => (d n : ℂ)) c T X =
      (2 * Real.pi * I)⁻¹ * (I * V) := by
    unfold Cubic.Analysis.Perron.perronIntegral
    congr 1
    rw [intervalIntegral.integral_mul_const, mul_comm, hV]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [HeightCoefficientContinuation.LSeries_eq hE _ (by simpa using hc1)]
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hdiff : Cubic.Analysis.Perron.perronIntegral (fun n => (d n : ℂ)) c T X - mainTerm c₂ c₁ X =
      (2 * Real.pi * I)⁻¹ * (Ht - Hb + I * Lv) := by
    rw [hperron, mainTerm]
    have hIV : I * V = 2 * Real.pi * I * (c₂ / 4 * X * Real.log X + (c₁ / 2 - c₂ / 4) * X) -
        Hb + Ht + I * Lv := by rw [← hrect]; ring
    rw [hIV]
    field_simp
    ring
  have hnpi : ‖(2 * Real.pi * I : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    apply inv_le_one_of_one_le₀
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  -- the three bounds
  have hHt : ‖Ht‖ ≤ 2 * Real.exp 1 * |KZ| * X ^ η := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (hTop.trans ?_)
    rw [show c - 1 + η = 1 / Real.log X + η by rw [hc]; ring, Real.rpow_add hX0,
      rpow_inv_log (by linarith)]
    have : KZ * (c - β) ≤ |KZ| * 2 :=
      (le_abs_self _).trans (by rw [abs_mul, abs_of_pos (by linarith : 0 < c - β)]
                                exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
    have hXη : 0 < X ^ η := Real.rpow_pos_of_pos hX0 η
    calc KZ * (c - β) * (Real.exp 1 * X ^ η) ≤ |KZ| * 2 * (Real.exp 1 * X ^ η) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 * Real.exp 1 * |KZ| * X ^ η := by ring
  have hHb : ‖Hb‖ ≤ 2 * Real.exp 1 * |KZ| * X ^ η := by
    push_cast at hBot
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (hBot.trans ?_)
    rw [show c - 1 + η = 1 / Real.log X + η by rw [hc]; ring, Real.rpow_add hX0,
      rpow_inv_log (by linarith)]
    have : KZ * (c - β) ≤ |KZ| * 2 :=
      (le_abs_self _).trans (by rw [abs_mul, abs_of_pos (by linarith : 0 < c - β)]
                                exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
    have hXη : 0 < X ^ η := Real.rpow_pos_of_pos hX0 η
    calc KZ * (c - β) * (Real.exp 1 * X ^ η) ≤ |KZ| * 2 * (Real.exp 1 * X ^ η) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 * Real.exp 1 * |KZ| * X ^ η := by ring
  have hLv : ‖Lv‖ ≤ 2 ^ η * |CL| * X ^ (β + η) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans
      ((hCL X T hX0 (by linarith [hT.1])).trans ?_)
    have hTη : T ^ η ≤ 2 ^ η * X ^ η := by
      rw [← Real.mul_rpow (by norm_num) hX0.le]
      exact Real.rpow_le_rpow hT0.le hT.2 hη.le
    rw [Real.rpow_add hX0 β η]
    have hXβ : 0 < X ^ β := Real.rpow_pos_of_pos hX0 β
    calc CL * X ^ β * T ^ η ≤ |CL| * X ^ β * T ^ η := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0.le _)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hXβ.le
      _ ≤ |CL| * X ^ β * (2 ^ η * X ^ η) :=
          mul_le_mul_of_nonneg_left hTη (by positivity)
      _ = 2 ^ η * |CL| * (X ^ β * X ^ η) := by ring
  have hmain : ‖Cubic.Analysis.Perron.perronIntegral (fun n => (d n : ℂ)) c T X -
      mainTerm c₂ c₁ X‖ ≤
      4 * Real.exp 1 * |KZ| * X ^ η + 2 ^ η * |CL| * X ^ (β + η) := by
    rw [hdiff, norm_mul]
    have h3 : ‖Ht - Hb + I * Lv‖ ≤ ‖Ht‖ + ‖Hb‖ + ‖Lv‖ := by
      calc ‖Ht - Hb + I * Lv‖ ≤ ‖Ht - Hb‖ + ‖I * Lv‖ := norm_add_le _ _
        _ ≤ ‖Ht‖ + ‖Hb‖ + ‖Lv‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
          linarith [norm_sub_le Ht Hb]
    calc ‖(2 * Real.pi * I : ℂ)⁻¹‖ * ‖Ht - Hb + I * Lv‖ ≤ 1 * ‖Ht - Hb + I * Lv‖ :=
          mul_le_mul_of_nonneg_right hnpi (norm_nonneg _)
      _ ≤ _ := by linarith
  have hper := hK₁ m X hXm hX3 T hT.1
  have hsplit : ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (d n : ℂ)) - mainTerm c₂ c₁ X‖ ≤
      ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (d n : ℂ)) -
        Cubic.Analysis.Perron.perronIntegral (fun n => (d n : ℂ)) c T X‖ +
      ‖Cubic.Analysis.Perron.perronIntegral (fun n => (d n : ℂ)) c T X - mainTerm c₂ c₁ X‖ := by
    rw [← sub_add_sub_cancel _ (Cubic.Analysis.Perron.perronIntegral (fun n => (d n : ℂ)) c T X)]
    exact norm_add_le _ _
  have hA : 0 ≤ X ^ η * Real.log X ^ 2 := by positivity
  have hB' : 0 ≤ X ^ η := by positivity
  have hC' : 0 ≤ X ^ (β + η) := by positivity
  have hK₁' : K₁ * X ^ η * Real.log X ^ 2 ≤ |K₁| * (X ^ η * Real.log X ^ 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hA
  have e1 : 0 ≤ |K₁| := abs_nonneg _
  have e2 : 0 ≤ 4 * Real.exp 1 * |KZ| := by positivity
  have e3 : 0 ≤ 2 ^ η * |CL| := by positivity
  calc _ ≤ _ := hsplit
    _ ≤ |K₁| * (X ^ η * Real.log X ^ 2) +
        (4 * Real.exp 1 * |KZ| * X ^ η + 2 ^ η * |CL| * X ^ (β + η)) := by
        linarith
    _ ≤ (|K₁| + 4 * Real.exp 1 * |KZ| + 2 ^ η * |CL|) *
        (X ^ η * Real.log X ^ 2 + X ^ η + X ^ (β + η)) := by
        nlinarith [mul_nonneg e1 hB', mul_nonneg e1 hC', mul_nonneg e2 hA, mul_nonneg e2 hC',
          mul_nonneg e3 hA, mul_nonneg e3 hB']

/-- `|log X - log Y| ≤ |X - Y| / min X Y`, in the form used below. -/
theorem abs_log_sub_log_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (m : ℝ) (hm : 0 < m)
    (hmX : m ≤ X) (hmY : m ≤ Y) : |Real.log X - Real.log Y| ≤ |X - Y| / m := by
  have h1 : Real.log X - Real.log Y ≤ (X - Y) / Y := by
    rw [← Real.log_div hX.ne' hY.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hX hY)
    rw [sub_div, div_self hY.ne'] at *
    linarith
  have h2 : Real.log Y - Real.log X ≤ (Y - X) / X := by
    rw [← Real.log_div hY.ne' hX.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hY hX)
    rw [sub_div, div_self hX.ne'] at *
    linarith
  rw [abs_le]
  have hXY : (X - Y) / Y ≤ |X - Y| / m := by
    calc (X - Y) / Y ≤ |X - Y| / Y := div_le_div_of_nonneg_right (le_abs_self _) hY.le
      _ ≤ |X - Y| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hmY
  have hYX : (Y - X) / X ≤ |X - Y| / m := by
    calc (Y - X) / X ≤ |X - Y| / X := by
          apply div_le_div_of_nonneg_right _ hX.le; rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ |X - Y| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hmX
  constructor <;> linarith

/-- Replacing `X` by `⌊X⌋ + 1/2` changes the main term by `O(log X)`. -/
theorem mainTerm_shift (c₂ c₁ : ℂ) {X : ℝ} (hX : 3 ≤ X) :
    ‖mainTerm c₂ c₁ X - mainTerm c₂ c₁ (⌊X⌋₊ + 1 / 2)‖ ≤
      (‖c₂ / 4‖ + ‖c₁ / 2 - c₂ / 4‖) * (Real.log X + 2) := by
  set Y : ℝ := ⌊X⌋₊ + 1 / 2 with hY
  have hfl := Nat.floor_le (by linarith : 0 ≤ X)
  have hfl' := Nat.lt_floor_add_one X
  have hXY : |X - Y| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hfl3 : (3 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hX)
  have hY0 : X / 2 ≤ Y := by linarith
  have hlog : |X * Real.log X - Y * Real.log Y| ≤ Real.log X + 2 := by
    have hL0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have hsplit : X * Real.log X - Y * Real.log Y =
        (X - Y) * Real.log X + Y * (Real.log X - Real.log Y) := by ring
    have hl := abs_log_sub_log_le (X := X) (Y := Y) (by linarith) (by linarith) (X / 2) (by linarith)
      (by linarith) hY0
    have hYpos : 0 ≤ Y := by linarith
    rw [hsplit]
    calc |(X - Y) * Real.log X + Y * (Real.log X - Real.log Y)|
        ≤ |X - Y| * Real.log X + Y * |Real.log X - Real.log Y| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hL0, abs_of_nonneg hYpos]
      _ ≤ 1 / 2 * Real.log X + Y * (|X - Y| / (X / 2)) := by
          gcongr
      _ ≤ 1 / 2 * Real.log X + (X + 1 / 2) * ((1 / 2) / (X / 2)) := by
          gcongr
          linarith
      _ ≤ Real.log X + 2 := by
          have : (X + 1 / 2) * ((1 / 2) / (X / 2)) ≤ 2 := by
            rw [show (X + 1 / 2) * ((1 / 2) / (X / 2)) = 1 + 1 / (2 * X) by field_simp]
            have : 1 / (2 * X) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
            linarith
          linarith
  have hdiff : mainTerm c₂ c₁ X - mainTerm c₂ c₁ Y =
      c₂ / 4 * ((X * Real.log X - Y * Real.log Y : ℝ) : ℂ) + (c₁ / 2 - c₂ / 4) * ((X - Y : ℝ) : ℂ) := by
    simp only [mainTerm]; push_cast; ring
  rw [hdiff]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hL0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have h1 : ‖c₂ / 4‖ * |X * Real.log X - Y * Real.log Y| ≤ ‖c₂ / 4‖ * (Real.log X + 2) :=
    mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
  have h2 : ‖c₁ / 2 - c₂ / 4‖ * |X - Y| ≤ ‖c₁ / 2 - c₂ / 4‖ * (Real.log X + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  linarith

/-- `eqn:dSummatoryForGeneralTrace`, given the strip mean value of `|ζ_E|²`. -/
theorem of_stripMean
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hstrip : ∀ δ η : ℝ, 0 < δ → 0 < η → StripMean δ η) :
    CubicTargets.Counting.HeightCoefficientSum.CoefficientClaim := by
  intro D F γ c₂ c₁ hE ε hε
  -- Reduce to an error exponent below one, then take δ = η = e/3.
  set e : ℝ := min ε (1 / 2) with he
  have he0 : 0 < e := lt_min hε (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  have he1 : e < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  set δ : ℝ := e / 3 with hδ
  set η : ℝ := e / 3 with hη
  have hδ0 : 0 < δ := by positivity
  have hδε : δ ≤ ε / 3 := by linarith
  have hη0 : 0 < η := by linarith
  obtain ⟨K, hK⟩ := half_integer_bound hPoisson hE hδ0 (by linarith) hη0
    (hstrip δ η hδ0 hη0)
  set E : ℝ := 1 / 2 + ε with hE'
  have hE0 : 0 < E := by linarith
  refine ⟨|K| * (4 / η ^ 2 + 2) * 2 ^ E + (‖c₂ / 4‖ + ‖c₁ / 2 - c₂ / 4‖) * (1 / E + 2), 3,
    fun X hX => ?_⟩
  have hX1 : 1 ≤ X := by linarith
  set Y : ℝ := ⌊X⌋₊ + 1 / 2 with hY
  have hfl := Nat.floor_le (by linarith : 0 ≤ X)
  have hfl3 : (3 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hX)
  have hY3 : 3 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY2X : Y ≤ 2 * X := by linarith
  have hfloorY : ⌊Y⌋₊ = ⌊X⌋₊ := by
    rw [hY, Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  -- the sum is unchanged
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (Cubic.PoissonSummation.HeightCountingData.count n : ℂ)) =
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (d n : ℂ) := by
    rw [hfloorY]
    exact Finset.sum_congr rfl fun n _ => (HeightCoefficientContinuation.d_cast n).symm
  have hhalf := hK ⌊X⌋₊ Y rfl hY3
  have hshift := mainTerm_shift c₂ c₁ hX
  -- every error term is at most `X^E` up to constants
  have hYE : Y ^ E ≤ 2 ^ E * X ^ E := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hY2X hE0.le
  have hlogY : Real.log Y ^ 2 ≤ 4 / η ^ 2 * Y ^ η := by
    have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ Y) (by linarith : 0 < η / 2)
    have hl0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
    have : Real.log Y ^ 2 ≤ (Y ^ (η / 2) / (η / 2)) ^ 2 := pow_le_pow_left₀ hl0 h 2
    have hsq : (Y ^ (η / 2)) ^ 2 = Y ^ η := by
      rw [← Real.rpow_natCast (Y ^ (η / 2)) 2, ← Real.rpow_mul (by linarith)]
      congr 1; push_cast; ring
    rw [div_pow, hsq] at this
    calc Real.log Y ^ 2 ≤ Y ^ η / (η / 2) ^ 2 := this
      _ = 4 / η ^ 2 * Y ^ η := by field_simp; ring
  have ht1 : Y ^ η * Real.log Y ^ 2 ≤ 4 / η ^ 2 * Y ^ E := by
    have h2η : Y ^ η * Y ^ η ≤ Y ^ E := by
      rw [← Real.rpow_add (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have hYη : 0 ≤ Y ^ η := by positivity
    calc Y ^ η * Real.log Y ^ 2 ≤ Y ^ η * (4 / η ^ 2 * Y ^ η) :=
          mul_le_mul_of_nonneg_left hlogY hYη
      _ = 4 / η ^ 2 * (Y ^ η * Y ^ η) := by ring
      _ ≤ 4 / η ^ 2 * Y ^ E := mul_le_mul_of_nonneg_left h2η (by positivity)
  have ht2 : Y ^ η ≤ Y ^ E := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have ht3 : Y ^ (1 / 2 + δ + η) ≤ Y ^ E := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hsumY : Y ^ η * Real.log Y ^ 2 + Y ^ η + Y ^ (1 / 2 + δ + η) ≤
      (4 / η ^ 2 + 2) * (2 ^ E * X ^ E) := by
    have : Y ^ η * Real.log Y ^ 2 + Y ^ η + Y ^ (1 / 2 + δ + η) ≤ (4 / η ^ 2 + 2) * Y ^ E := by
      linarith
    exact this.trans (mul_le_mul_of_nonneg_left hYE (by positivity))
  have hlogX : Real.log X + 2 ≤ (1 / E + 2) * X ^ E := by
    have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ X) hE0
    have h1 : 1 ≤ X ^ E := Real.one_le_rpow hX1 hE0.le
    rw [add_mul, div_mul_eq_mul_div, one_mul]
    linarith
  have hsumnn : 0 ≤ Y ^ η * Real.log Y ^ 2 + Y ^ η + Y ^ (1 / 2 + δ + η) := by positivity
  have hmain : mainTerm c₂ c₁ X = c₂ / 4 * X * Real.log X + (c₁ / 2 - c₂ / 4) * X := rfl
  rw [hsum, ← hmain]
  calc ‖(∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (d n : ℂ)) - mainTerm c₂ c₁ X‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (d n : ℂ)) - mainTerm c₂ c₁ Y‖ +
          ‖mainTerm c₂ c₁ X - mainTerm c₂ c₁ Y‖ := by
        rw [← sub_add_sub_cancel _ (mainTerm c₂ c₁ Y) (mainTerm c₂ c₁ X)]
        refine (norm_add_le _ _).trans ?_
        rw [norm_sub_rev (mainTerm c₂ c₁ Y)]
    _ ≤ |K| * ((4 / η ^ 2 + 2) * (2 ^ E * X ^ E)) +
          (‖c₂ / 4‖ + ‖c₁ / 2 - c₂ / 4‖) * ((1 / E + 2) * X ^ E) := by
        gcongr
        · exact hhalf.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hsumnn) |>.trans
            (mul_le_mul_of_nonneg_left hsumY (abs_nonneg K))
        · exact hshift.trans (mul_le_mul_of_nonneg_left hlogX (by positivity))
    _ = (|K| * (4 / η ^ 2 + 2) * 2 ^ E + (‖c₂ / 4‖ + ‖c₁ / 2 - c₂ / 4‖) * (1 / E + 2)) *
          X ^ (1 / 2 + ε) := by rw [hE']; ring

/-- `eqn:dSummatoryForGeneralTrace`, relative to the two black-box hypotheses:
the Poisson summation input `PoissonWithDualMeasure.BlackBox` (through `prop:leadingTerms` and the coefficient formula) and
[Chandrasekharan–Narasimhan 1963, Theorem 4], from which the uniform strip
mean value is derived in `XiMeanValue`. -/
theorem coefficient_estimate
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.HeightCoefficientSum.CoefficientClaim :=
  of_stripMean hPoisson fun δ η hδ hη =>
    Cubic.Counting.XiMeanValue.inner_strip hCN δ hδ η hη

/-- The labelled formula, with its main term expressed using `Q`. -/
theorem polynomial_estimate
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.HeightCoefficientSum.Claim := by
  intro D F μ c₂ c₁ h ε hε
  obtain ⟨K, X₀, hK⟩ := coefficient_estimate hPoisson hCN D F μ c₂ c₁ h ε hε
  refine ⟨K, X₀, fun X hX => ?_⟩
  simpa only [CountPolynomialNormalization.laurent_main h X] using hK X hX

end Cubic.Counting.HeightCoefficientSum
