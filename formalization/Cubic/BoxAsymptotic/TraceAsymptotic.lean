import Cubic.BoxAsymptotic.TraceWidth

/-!
# The critical trace intervals (`eq:width` in `lem:geometry`)

Let `r = √n`, `cos θ = 1 - c` and `V = (2/3) r² c`. In the bulk regime

  `0 < ε ≤ 1/10`, `0 < c ≤ ε²`, `27H ≤ ε² r³ c`, `r² √c ≤ H/2`, `2r ≤ H`,

the trace set `E` consists of two intervals near `s = r`, where `w = |s - r|` satisfies
`(1 - 2ε)√V ≤ w ≤ (1 + 2ε)√V`, and a part of `s ≤ -r` of diameter `≤ 54H/r²` (the
noncritical branch). Each critical interval has length `m (1 + O(ε))` with
`m = 9H/(r√V)`, so `|W - 2m| ≤ 13 ε m`. Since `c ≈ τ²/2`, `2m ≈ 18√3 H/(nτ)`.

Upper bounds come from the factorization of `Q(s₁) - Q(s₂)` as in `TraceWidth`; lower
bounds from the intermediate value theorem and monotonicity of `Q` on `[0, r]` and `[r, ∞)`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.TraceAsymptotic

open MeasureTheory Real Cubic.BoxAsymptotic.TraceWidth

/-- The bulk hypotheses. -/
structure Bulk (H r c ε : ℝ) : Prop where
  hr : 0 < r
  hε : 0 < ε
  hε1 : ε ≤ 1 / 10
  hc : 0 < c
  hcε : c ≤ ε ^ 2
  hH : 27 * H ≤ ε ^ 2 * r ^ 3 * c
  hwidth : r ^ 2 * Real.sqrt c ≤ H / 2
  hrH : 2 * r ≤ H

theorem Q_add (r w : ℝ) : Q (r ^ 2) (r + w) = 2 * r ^ 3 - 3 * r * w ^ 2 - w ^ 3 := by
  simp only [Q]; ring

theorem Q_sub' (r w : ℝ) : Q (r ^ 2) (r - w) = 2 * r ^ 3 - 3 * r * w ^ 2 + w ^ 3 := by
  simp only [Q]; ring

/-- The `Q`-condition of `E` with `cos θ = 1 - c`. -/
def QCond (H r c s : ℝ) : Prop := |Q (r ^ 2) s - 2 * r ^ 3 * (1 - c)| ≤ 27 * H

theorem qcond_of_mem {H r c θ s : ℝ} (hr : 0 ≤ r) (hcos : Real.cos θ = 1 - c)
    (hs : s ∈ E H (r ^ 2) θ) : QCond H r c s := by
  have h := hs.2.2
  rwa [Real.sqrt_sq hr, hcos, show 2 * (r ^ 2 * r) * (1 - c) = 2 * r ^ 3 * (1 - c) by ring] at h

/-- `(1 - 2ε)² V ≤ w² ≤ (1 + 2ε)² V` for `s ≥ 0` satisfying the `Q`-condition. -/
theorem w_sq_bounds {H r c ε s : ℝ} (hb : Bulk H r c ε) (hs0 : 0 ≤ s) (hs : QCond H r c s) :
    (1 - 2 * ε) ^ 2 * (2 / 3 * r ^ 2 * c) ≤ |s - r| ^ 2 ∧
      |s - r| ^ 2 ≤ (1 + 2 * ε) ^ 2 * (2 / 3 * r ^ 2 * c) := by
  obtain ⟨hr, hε, hε1, hc, hcε, hH, -, -⟩ := hb
  have hrc : 0 < r ^ 3 * c := by positivity
  have hH' : 27 * H ≤ ε ^ 2 * (r ^ 3 * c) := by linarith
  set P := r ^ 2 * c with hP
  have hP0 : 0 < P := by positivity
  have hA : r ^ 3 * c = r * P := by rw [hP]; ring
  have num1 : (2 + ε ^ 2) / 3 ≤ (1 + 2 * ε) ^ 2 * (2 / 3) := by nlinarith
  have num2 : (1 - 2 * ε) ^ 2 * (2 / 3) ≤ (2 - ε ^ 2) / (3 + ε) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have num3 : (1 - 2 * ε) ^ 2 * (2 / 3) ≤ (2 - ε ^ 2) / 3 := by nlinarith
  have num4 : (2 + ε ^ 2) / (3 - 2 * ε) ≤ (1 + 2 * ε) ^ 2 * (2 / 3) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hPε : P ≤ r ^ 2 * ε ^ 2 := by rw [hP]; exact mul_le_mul_of_nonneg_left hcε (by positivity)
  have hH'' : 27 * H ≤ ε ^ 2 * (r * P) := by rw [← hA]; linarith
  have reorg : ∀ k : ℝ, k * (2 / 3 * r ^ 2 * c) = k * (2 / 3) * P := fun k => by rw [hP]; ring
  rcases le_total r s with h | h
  · set w := s - r with hw
    have hw0 : 0 ≤ w := by linarith
    rw [abs_of_nonneg hw0, reorg, reorg]
    have e : s = r + w := by ring
    rw [QCond, e, Q_add, abs_le] at hs
    obtain ⟨h1, h2⟩ := hs
    have hw3 : 0 ≤ w ^ 3 := pow_nonneg hw0 3
    have up : r * (3 * w ^ 2) ≤ r * ((2 + ε ^ 2) * P) := by nlinarith
    have up' : w ^ 2 ≤ (2 + ε ^ 2) / 3 * P := by
      have := le_of_mul_le_mul_left up hr; linarith
    have hwr : w ≤ r * ε := by
      have : w ^ 2 ≤ (r * ε) ^ 2 := by nlinarith
      exact (pow_le_pow_iff_left₀ hw0 (by positivity) (by norm_num)).mp this
    have hw3' : w ^ 3 ≤ r * ε * w ^ 2 := by
      have := mul_le_mul_of_nonneg_right hwr (sq_nonneg w)
      nlinarith
    refine ⟨?_, up'.trans (mul_le_mul_of_nonneg_right num1 hP0.le)⟩
    have low : r * ((2 - ε ^ 2) * P) ≤ r * (w ^ 2 * (3 + ε)) := by nlinarith
    have low' : (2 - ε ^ 2) / (3 + ε) * P ≤ w ^ 2 := by
      have := le_of_mul_le_mul_left low hr
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; linarith
    exact (mul_le_mul_of_nonneg_right num2 hP0.le).trans low'
  · set w := r - s with hw
    have hw0 : 0 ≤ w := by linarith
    have hwr0 : w ≤ r := by linarith
    rw [abs_of_nonpos (by linarith : s - r ≤ 0), show -(s - r) = w by ring, reorg, reorg]
    have e : s = r - w := by ring
    rw [QCond, e, Q_sub', abs_le] at hs
    obtain ⟨h1, h2⟩ := hs
    have hw3r : w ^ 3 ≤ r * w ^ 2 := by
      have := mul_le_mul_of_nonneg_right hwr0 (sq_nonneg w)
      calc w ^ 3 = w * w ^ 2 := by ring
        _ ≤ _ := this
    have up : r * (2 * w ^ 2) ≤ r * ((2 + ε ^ 2) * P) := by linarith
    have up' := le_of_mul_le_mul_left up hr
    have hwr : w ≤ r * (2 * ε) := by
      have a1 := mul_le_mul_of_nonneg_left hPε (by positivity : (0 : ℝ) ≤ 2 + ε ^ 2)
      have a2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le (by linarith)
      have a3 : r ^ 2 * ε ^ 2 * ε ^ 2 ≤ r ^ 2 * ε ^ 2 := by
        have := mul_le_mul_of_nonneg_left a2 (by positivity : (0 : ℝ) ≤ r ^ 2 * ε ^ 2)
        linarith
      have : w ^ 2 ≤ (r * (2 * ε)) ^ 2 := by
        have e1 : (r * (2 * ε)) ^ 2 = 4 * (r ^ 2 * ε ^ 2) := by ring
        have e2 : (2 + ε ^ 2) * (r ^ 2 * ε ^ 2) = 2 * (r ^ 2 * ε ^ 2) + r ^ 2 * ε ^ 2 * ε ^ 2 := by
          ring
        rw [e1]; linarith
      exact (pow_le_pow_iff_left₀ hw0 (by positivity) (by norm_num)).mp this
    have hw3 : w ^ 3 ≤ r * (2 * ε) * w ^ 2 := by
      have := mul_le_mul_of_nonneg_right hwr (sq_nonneg w)
      calc w ^ 3 = w * w ^ 2 := by ring
        _ ≤ _ := this
    constructor
    · have low : r * ((2 - ε ^ 2) * P) ≤ r * (3 * w ^ 2) := by linarith [pow_nonneg hw0 3]
      have := le_of_mul_le_mul_left low hr
      have : (2 - ε ^ 2) / 3 * P ≤ w ^ 2 := by linarith
      exact (mul_le_mul_of_nonneg_right num3 hP0.le).trans this
    · have upp : r * (w ^ 2 * (3 - 2 * ε)) ≤ r * ((2 + ε ^ 2) * P) := by linarith
      have h' := le_of_mul_le_mul_left upp hr
      have h'' : w ^ 2 ≤ (2 + ε ^ 2) / (3 - 2 * ε) * P := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
      exact h''.trans (mul_le_mul_of_nonneg_right num4 hP0.le)


/-- `√V` with `V = (2/3) r² c`. -/
def sV (r c : ℝ) : ℝ := Real.sqrt (2 / 3 * r ^ 2 * c)

theorem sV_pos {H r c ε : ℝ} (hb : Bulk H r c ε) : 0 < sV r c := by
  have := hb.hr; have := hb.hc
  exact Real.sqrt_pos.mpr (by positivity)

theorem sV_sq (r c : ℝ) (hc : 0 ≤ c) : sV r c ^ 2 = 2 / 3 * r ^ 2 * c :=
  Real.sq_sqrt (by positivity)

theorem sV_le {H r c ε : ℝ} (hb : Bulk H r c ε) :
    sV r c ≤ r * Real.sqrt c ∧ sV r c ≤ ε * r := by
  have hr := hb.hr; have hc := hb.hc
  have e : Real.sqrt (r ^ 2 * c) = r * Real.sqrt c := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
  have h1 : sV r c ≤ r * Real.sqrt c := by
    rw [← e]; exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨h1, h1.trans ?_⟩
  have : Real.sqrt c ≤ ε := by
    rw [Real.sqrt_le_left hb.hε.le]; exact hb.hcε
  nlinarith

/-- `(1 - 2ε)√V ≤ w ≤ (1 + 2ε)√V`. -/
theorem w_bounds {H r c ε s : ℝ} (hb : Bulk H r c ε) (hs0 : 0 ≤ s) (hs : QCond H r c s) :
    (1 - 2 * ε) * sV r c ≤ |s - r| ∧ |s - r| ≤ (1 + 2 * ε) * sV r c := by
  obtain ⟨h1, h2⟩ := w_sq_bounds hb hs0 hs
  have hsq := sV_sq r c hb.hc.le
  have hv := (sV_pos hb).le
  have hε := hb.hε1
  constructor
  · refine (pow_le_pow_iff_left₀ (by nlinarith) (abs_nonneg _) (by norm_num : 2 ≠ 0)).mp ?_
    rw [mul_pow, hsq]; exact h1
  · refine (pow_le_pow_iff_left₀ (abs_nonneg _) (by nlinarith) (by norm_num : 2 ≠ 0)).mp ?_
    rw [mul_pow, hsq]; exact h2

theorem Q_mono {r x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ r) :
    Q (r ^ 2) x ≤ Q (r ^ 2) y := by
  have := Q_sub (r ^ 2) y x
  have : 0 ≤ 3 * r ^ 2 - y ^ 2 - y * x - x ^ 2 := by nlinarith
  nlinarith

theorem Q_anti {r x y : ℝ} (hr : 0 ≤ r) (hx : r ≤ x) (hxy : x ≤ y) :
    Q (r ^ 2) y ≤ Q (r ^ 2) x := by
  have := Q_sub (r ^ 2) y x
  have : 3 * r ^ 2 - y ^ 2 - y * x - x ^ 2 ≤ 0 := by nlinarith
  nlinarith


/-- The main length `m = 9H/(r√V)` of one critical interval. -/
def m (H r c : ℝ) : ℝ := 9 * H / (r * sV r c)

theorem H_pos {H r c ε : ℝ} (hb : Bulk H r c ε) : 0 < H := by
  have := hb.hr; linarith [hb.hrH]

theorem upper_piece0 {H r c ε θ : ℝ} (hb : Bulk H r c ε) (hcos : Real.cos θ = 1 - c) :
    volume (E H (r ^ 2) θ ∩ piece r 0) ≤
      ENNReal.ofReal (m H r c / (1 - 2 * ε)) := by
  have hr := hb.hr
  have hv := sV_pos hb
  have hε := hb.hε1
  refine volume_le_of_diam fun x hx y hy => ?_
  have hx0 : 0 ≤ x := hx.2.1
  have hy0 : 0 ≤ y := hy.2.1
  have wx := (w_bounds hb hx0 (qcond_of_mem hr.le hcos hx.1)).1
  have wy := (w_bounds hb hy0 (qcond_of_mem hr.le hcos hy.1)).1
  rw [abs_of_nonneg (by linarith [hx.2.2] : 0 ≤ x - r)] at wx
  rw [abs_of_nonneg (by linarith [hy.2.2] : 0 ≤ y - r)] at wy
  have hc := Q_close hx.1 hy.1
  rw [Q_sub, abs_mul] at hc
  have hf : 6 * r * ((1 - 2 * ε) * sV r c) ≤ |3 * r ^ 2 - x ^ 2 - x * y - y ^ 2| := by
    rw [abs_of_nonpos (by nlinarith [hx.2.2, hy.2.2])]
    nlinarith [hx.2.2, hy.2.2]
  have hpos : 0 < 6 * r * ((1 - 2 * ε) * sV r c) := by
    have : 0 < 1 - 2 * ε := by linarith
    positivity
  have : |x - y| * (6 * r * ((1 - 2 * ε) * sV r c)) ≤ 54 * H :=
    (mul_le_mul_of_nonneg_left hf (abs_nonneg _)).trans hc
  calc |x - y| = |x - y| * (6 * r * ((1 - 2 * ε) * sV r c)) / (6 * r * ((1 - 2 * ε) * sV r c)) :=
        (mul_div_cancel_right₀ _ hpos.ne').symm
    _ ≤ 54 * H / (6 * r * ((1 - 2 * ε) * sV r c)) := by gcongr
    _ = m H r c / (1 - 2 * ε) := by
        have : 1 - 2 * ε ≠ 0 := by linarith
        rw [m]; field_simp; ring


theorem upper_piece1 {H r c ε θ : ℝ} (hb : Bulk H r c ε) (hcos : Real.cos θ = 1 - c) :
    volume (E H (r ^ 2) θ ∩ piece r 1) ≤
      ENNReal.ofReal (m H r c / ((1 - 2 * ε) * (1 - ε))) := by
  have hr := hb.hr
  have hv := sV_pos hb
  have hε := hb.hε1
  have hε0 := hb.hε
  have hvε := (sV_le hb).2
  refine volume_le_of_diam fun x hx y hy => ?_
  have hx0 : 0 ≤ x := hx.2.1
  have hy0 : 0 ≤ y := hy.2.1
  have wx := w_bounds hb hx0 (qcond_of_mem hr.le hcos hx.1)
  have wy := w_bounds hb hy0 (qcond_of_mem hr.le hcos hy.1)
  rw [abs_of_nonpos (by linarith [hx.2.2] : x - r ≤ 0)] at wx
  rw [abs_of_nonpos (by linarith [hy.2.2] : y - r ≤ 0)] at wy
  have hc := Q_close hx.1 hy.1
  rw [Q_sub, abs_mul] at hc
  set a := r - x with ha
  set b := r - y with hb'
  have e : 3 * r ^ 2 - x ^ 2 - x * y - y ^ 2 = (a + b) * (3 * r - (a + b)) + a * b := by
    rw [ha, hb']; ring
  have hab : 0 ≤ a * b := mul_nonneg (by linarith [hx.2.2]) (by linarith [hy.2.2])
  have hw : (1 + 2 * ε) * sV r c ≤ 3 / 2 * (ε * r) := by
    have := mul_le_mul_of_nonneg_left hvε (by linarith : (0 : ℝ) ≤ 1 + 2 * ε)
    have : (1 + 2 * ε) * (ε * r) ≤ 3 / 2 * (ε * r) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have wa : a ≤ 3 / 2 * (ε * r) := by rw [ha]; linarith [wx.2]
  have wb : b ≤ 3 / 2 * (ε * r) := by rw [hb']; linarith [wy.2]
  have h3 : 3 * r * (1 - ε) ≤ 3 * r - (a + b) := by nlinarith
  have h2 : 2 * ((1 - 2 * ε) * sV r c) ≤ a + b := by
    have : (1 - 2 * ε) * sV r c ≤ a := by rw [ha]; linarith [wx.1]
    have : (1 - 2 * ε) * sV r c ≤ b := by rw [hb']; linarith [wy.1]
    linarith
  have hpos : 0 < 2 * ((1 - 2 * ε) * sV r c) * (3 * r * (1 - ε)) := by
    have : 0 < 1 - 2 * ε := by linarith
    have : 0 < 1 - ε := by linarith
    positivity
  have hf : 2 * ((1 - 2 * ε) * sV r c) * (3 * r * (1 - ε)) ≤
      |3 * r ^ 2 - x ^ 2 - x * y - y ^ 2| := by
    have h1ε : 0 < 1 - 2 * ε := by linarith
    have hab0 : 0 ≤ a + b := le_trans (by positivity) h2
    have h3r : 0 ≤ 3 * r * (1 - ε) := by
      have : 0 < 1 - ε := by linarith
      positivity
    have hpr : 0 ≤ (a + b) * (3 * r - (a + b)) := mul_nonneg hab0 (h3r.trans h3)
    rw [e, abs_of_nonneg (by linarith)]
    have := mul_le_mul h2 h3 h3r hab0
    linarith
  have : |x - y| * (2 * ((1 - 2 * ε) * sV r c) * (3 * r * (1 - ε))) ≤ 54 * H :=
    (mul_le_mul_of_nonneg_left hf (abs_nonneg _)).trans hc
  calc |x - y| = |x - y| * (2 * ((1 - 2 * ε) * sV r c) * (3 * r * (1 - ε))) /
          (2 * ((1 - 2 * ε) * sV r c) * (3 * r * (1 - ε))) :=
        (mul_div_cancel_right₀ _ hpos.ne').symm
    _ ≤ 54 * H / (2 * ((1 - 2 * ε) * sV r c) * (3 * r * (1 - ε))) := by gcongr
    _ = m H r c / ((1 - 2 * ε) * (1 - ε)) := by
        have : 1 - 2 * ε ≠ 0 := by linarith
        have : 1 - ε ≠ 0 := by linarith
        rw [m]; field_simp; ring

theorem upper_piece2 {H r c ε θ : ℝ} (hb : Bulk H r c ε) (hcos : Real.cos θ = 1 - c) :
    volume (E H (r ^ 2) θ ∩ piece r 2) ≤ ENNReal.ofReal (54 * H / r ^ 2) := by
  have hr := hb.hr
  have hε := hb.hε1
  have hH := hb.hH
  have hc1 : c ≤ 1 / 100 := by nlinarith [hb.hcε, hb.hε]
  have hH1 : 27 * H ≤ r ^ 3 / 100 := by
    have : ε ^ 2 * r ^ 3 * c ≤ r ^ 3 / 100 := by
      have h1 : ε ^ 2 ≤ 1 := by nlinarith [hb.hε]
      have hr3 : 0 < r ^ 3 := by positivity
      have h2 := mul_le_mul_of_nonneg_right h1 (by have := hb.hc; positivity : (0 : ℝ) ≤ r ^ 3 * c)
      have h3 := mul_le_mul_of_nonneg_left hc1 hr3.le
      nlinarith
    linarith
  have key := piece_le_away (H := H) (θ := θ) hr (by positivity : 0 < r / 2) 2 fun s hs => by
    have hq := qcond_of_mem hr.le hcos hs.1
    obtain ⟨hs0, hsr⟩ := hs.2
    set w := -s - r
    have hw0 : 0 ≤ w := by linarith
    have hd : dist' r s = w := by
      simp only [dist', abs_of_nonpos hs0]; rw [abs_of_nonneg (by linarith)]
    rw [hd]
    have e : s = -(r + w) := by simp only [w]; ring
    rw [QCond, e, Q_neg, Q_add, abs_le] at hq
    by_contra hlt; push_neg at hlt
    have : w ^ 3 ≤ r / 2 * w ^ 2 := by
      have := mul_le_mul_of_nonneg_right hlt.le (sq_nonneg w)
      calc w ^ 3 = w * w ^ 2 := by ring
        _ ≤ _ := this
    have hw2 : w ^ 2 ≤ r ^ 2 / 4 := by nlinarith
    have hr3 : 0 < r ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left hw2 (by positivity : (0 : ℝ) ≤ 3 * r)
    have := mul_le_mul_of_nonneg_left hc1 hr3.le
    nlinarith
  refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  field_simp

theorem upper_piece3 {H r c ε θ : ℝ} (hb : Bulk H r c ε) (hcos : Real.cos θ = 1 - c) :
    volume (E H (r ^ 2) θ ∩ piece r 3) = 0 := by
  have hr := hb.hr
  have hε := hb.hε1
  have hc1 : c ≤ 1 / 100 := by nlinarith [hb.hcε, hb.hε]
  have hH1 : 27 * H < r ^ 3 := by
    have : ε ^ 2 * r ^ 3 * c < r ^ 3 := by
      have h1 : ε ^ 2 ≤ 1 := by nlinarith [hb.hε]
      have hr3 : 0 < r ^ 3 := by positivity
      have h2 := mul_le_mul_of_nonneg_right h1 (by have := hb.hc; positivity : (0 : ℝ) ≤ r ^ 3 * c)
      have h3 := mul_le_mul_of_nonneg_left hc1 hr3.le
      nlinarith
    linarith [hb.hH]
  suffices h : E H (r ^ 2) θ ∩ piece r 3 = ∅ by rw [h, measure_empty]
  refine Set.eq_empty_of_forall_notMem fun s hs => ?_
  have hq := qcond_of_mem hr.le hcos hs.1
  obtain ⟨hs0, hsr⟩ := hs.2
  have hQ : Q (r ^ 2) s ≤ 0 := by
    simp only [Q]
    have : 0 ≤ 3 * r ^ 2 - s ^ 2 := by nlinarith
    nlinarith
  rw [QCond, abs_le] at hq
  have hr3 : 0 < r ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_left hc1 hr3.le
  nlinarith


theorem m_pos {H r c ε : ℝ} (hb : Bulk H r c ε) : 0 < m H r c := by
  have := H_pos hb; have := hb.hr; have := sV_pos hb
  unfold m; positivity

theorem noncritical_le {H r c ε : ℝ} (hb : Bulk H r c ε) :
    54 * H / r ^ 2 ≤ 6 * ε * m H r c := by
  have hr := hb.hr; have hv := sV_pos hb; have hH := H_pos hb
  have hvε := (sV_le hb).2
  rw [m, div_le_iff₀ (by positivity)]
  rw [show 6 * ε * (9 * H / (r * sV r c)) * r ^ 2 = 54 * H * (ε * r) / sV r c by
    field_simp; ring]
  rw [le_div_iff₀ hv]
  exact mul_le_mul_of_nonneg_left hvε (by positivity)

theorem volume_upper {H r c ε θ : ℝ} (hb : Bulk H r c ε) (hcos : Real.cos θ = 1 - c) :
    volume (E H (r ^ 2) θ) ≤ ENNReal.ofReal (2 * m H r c + 13 * ε * m H r c) := by
  have hε := hb.hε1; have hε0 := hb.hε
  have hm := m_pos hb
  refine (volume_le_sum H r θ).trans ?_
  rw [Fin.sum_univ_four, upper_piece3 hb hcos, add_zero]
  refine (add_le_add (add_le_add (upper_piece0 hb hcos) (upper_piece1 hb hcos))
    (upper_piece2 hb hcos)).trans ?_
  have h1 : 0 < 1 - 2 * ε := by linarith
  have h2 : 0 < 1 - ε := by linarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by have := hb.hr; have := H_pos hb; positivity)]
  apply ENNReal.ofReal_le_ofReal
  have a1 : m H r c / (1 - 2 * ε) ≤ m H r c * (1 + 5 / 2 * ε) := by
    rw [div_le_iff₀ h1]
    have := mul_nonneg hm.le (mul_nonneg hε0.le (by linarith : (0 : ℝ) ≤ 1 / 2 - 5 * ε))
    nlinarith
  have a2 : m H r c / ((1 - 2 * ε) * (1 - ε)) ≤ m H r c * (1 + 9 / 2 * ε) := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_nonneg hm.le (mul_nonneg hε0.le (by linarith : (0 : ℝ) ≤ 3 / 2 - 23 / 2 * ε))
    have := mul_nonneg hm.le (pow_nonneg hε0.le 3)
    nlinarith
  have a3 := noncritical_le hb
  nlinarith

theorem lower_interval1 {H r c ε θ : ℝ} (hb : Bulk H r c ε) (hcos : Real.cos θ = 1 - c) :
    ∃ a b, 0 ≤ a ∧ a ≤ b ∧ b ≤ r ∧ Set.Icc a b ⊆ E H (r ^ 2) θ ∧
      m H r c / (1 + 2 * ε) ≤ b - a := by
  have hr := hb.hr; have hε := hb.hε1; have hε0 := hb.hε; have hH := H_pos hb
  have hv := sV_pos hb
  have hvε := (sV_le hb).2
  have hvc := (sV_le hb).1
  have hc1 : c ≤ 1 / 100 := by nlinarith [hb.hcε]
  have hr3 : 0 < r ^ 3 := by positivity
  have hHc : 27 * H ≤ r ^ 3 * c := by
    have h1 : ε ^ 2 ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 (by have := hb.hc; positivity : (0 : ℝ) ≤ r ^ 3 * c)
    linarith [hb.hH]
  have hcr := mul_le_mul_of_nonneg_left hc1 hr3.le
  set J := 2 * r ^ 3 * (1 - c)
  have hcont : Continuous (Q (r ^ 2)) := by unfold Q; fun_prop
  have hQ0 : Q (r ^ 2) 0 ≤ J - 27 * H := by simp only [Q, J]; nlinarith
  have hQr : J + 27 * H ≤ Q (r ^ 2) r := by simp only [Q, J]; nlinarith
  obtain ⟨a, ⟨ha0, har⟩, hQa⟩ := intermediate_value_Icc hr.le hcont.continuousOn
    ⟨hQ0, by linarith⟩
  obtain ⟨b, ⟨hab, hbr⟩, hQb⟩ := intermediate_value_Icc har hcont.continuousOn
    ⟨by rw [hQa]; linarith, hQr⟩
  have hsub : ∀ s ∈ Set.Icc a b, QCond H r c s ∧ |s - r| ≤ (1 + 2 * ε) * sV r c := by
    intro s ⟨has, hsb⟩
    have q1 := Q_mono ha0 has (hsb.trans hbr)
    have q2 := Q_mono (ha0.trans has) hsb hbr
    have hq : QCond H r c s := by
      rw [QCond, abs_le]; constructor <;> linarith
    exact ⟨hq, (w_bounds hb (ha0.trans has) hq).2⟩
  refine ⟨a, b, ha0, hab, hbr, fun s hs => ?_, ?_⟩
  · obtain ⟨hq, hw⟩ := hsub s hs
    have hs0 : 0 ≤ s := ha0.trans hs.1
    have hsr : s ≤ r := hs.2.trans hbr
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_nonneg hs0]; linarith [hb.hrH]
    · rw [abs_of_nonpos (by nlinarith : s ^ 2 - r ^ 2 ≤ 0)]
      rw [abs_of_nonpos (by linarith : s - r ≤ 0)] at hw
      have : r ^ 2 - s ^ 2 = (r - s) * (r + s) := by ring
      have h1 : (r - s) * (r + s) ≤ (1 + 2 * ε) * sV r c * (2 * r) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      have h2 : (1 + 2 * ε) * sV r c * (2 * r) ≤ 3 * (r ^ 2 * Real.sqrt c) := by
        have := mul_le_mul_of_nonneg_left hvc (by linarith : (0 : ℝ) ≤ 1 + 2 * ε)
        have h3 := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ 2 * r)
        have h4 : (2 * (1 + 2 * ε)) * (r ^ 2 * Real.sqrt c) ≤ 3 * (r ^ 2 * Real.sqrt c) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have e : (1 + 2 * ε) * (r * Real.sqrt c) * (2 * r) =
            (2 * (1 + 2 * ε)) * (r ^ 2 * Real.sqrt c) := by ring
        linarith
      linarith [hb.hwidth]
    · rw [Real.sqrt_sq hr.le, hcos]
      have := hq; rw [QCond] at this
      convert this using 2
  · have e := Q_sub (r ^ 2) b a
    rw [hQa, hQb] at e
    set wa := r - a
    set wb := r - b
    have ha' := (hsub a ⟨le_rfl, hab⟩).2
    have hb' := (hsub b ⟨hab, le_rfl⟩).2
    rw [abs_of_nonpos (by linarith : a - r ≤ 0)] at ha'
    rw [abs_of_nonpos (by linarith : b - r ≤ 0)] at hb'
    have hf : 3 * r ^ 2 - b ^ 2 - b * a - a ^ 2 ≤ 6 * r * ((1 + 2 * ε) * sV r c) := by
      have : 3 * r ^ 2 - b ^ 2 - b * a - a ^ 2 =
          3 * r * ((r - a) + (r - b)) - ((r - a) ^ 2 + (r - a) * (r - b) + (r - b) ^ 2) := by ring
      have hnn : 0 ≤ (r - a) ^ 2 + (r - a) * (r - b) + (r - b) ^ 2 := by
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ r - a) (by linarith : (0 : ℝ) ≤ r - b)
        positivity
      nlinarith
    have hpos : 0 < 6 * r * ((1 + 2 * ε) * sV r c) := by positivity
    have : 54 * H ≤ (b - a) * (6 * r * ((1 + 2 * ε) * sV r c)) := by
      have := mul_le_mul_of_nonneg_left hf (by linarith : (0 : ℝ) ≤ b - a)
      linarith
    rw [m, div_div, div_le_iff₀ (by positivity)]
    calc 9 * H = 54 * H / 6 := by ring
      _ ≤ (b - a) * (6 * r * ((1 + 2 * ε) * sV r c)) / 6 := by gcongr
      _ = (b - a) * (r * sV r c * (1 + 2 * ε)) := by ring


theorem lower_interval2 {H r c ε θ : ℝ} (hb : Bulk H r c ε) (hcos : Real.cos θ = 1 - c) :
    ∃ a b, r ≤ a ∧ a ≤ b ∧ Set.Icc a b ⊆ E H (r ^ 2) θ ∧
      m H r c / ((1 + 2 * ε) * (1 + ε)) ≤ b - a := by
  have hr := hb.hr; have hε := hb.hε1; have hε0 := hb.hε; have hH := H_pos hb
  have hv := sV_pos hb
  have hvε := (sV_le hb).2
  have hvc := (sV_le hb).1
  have hc1 : c ≤ 1 / 100 := by nlinarith [hb.hcε]
  have hr3 : 0 < r ^ 3 := by positivity
  have hHc : 27 * H ≤ r ^ 3 * c := by
    have h1 : ε ^ 2 ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 (by have := hb.hc; positivity : (0 : ℝ) ≤ r ^ 3 * c)
    linarith [hb.hH]
  have hcr := mul_le_mul_of_nonneg_left hc1 hr3.le
  set J := 2 * r ^ 3 * (1 - c)
  have hcont : Continuous (Q (r ^ 2)) := by unfold Q; fun_prop
  have hQ2 : Q (r ^ 2) (2 * r) ≤ J - 27 * H := by simp only [Q, J]; nlinarith
  have hQr : J + 27 * H ≤ Q (r ^ 2) r := by simp only [Q, J]; nlinarith
  obtain ⟨a, ⟨hra, ha2⟩, hQa⟩ := intermediate_value_Icc' (by linarith : r ≤ 2 * r)
    hcont.continuousOn ⟨by linarith, hQr⟩
  obtain ⟨b, ⟨hab, hb2⟩, hQb⟩ := intermediate_value_Icc' ha2 hcont.continuousOn
    ⟨hQ2, by rw [hQa]; linarith⟩
  have hsub : ∀ s ∈ Set.Icc a b, QCond H r c s ∧ |s - r| ≤ (1 + 2 * ε) * sV r c := by
    intro s ⟨has, hsb⟩
    have q1 := Q_anti hr.le hra has
    have q2 := Q_anti hr.le (hra.trans has) hsb
    have hq : QCond H r c s := by
      rw [QCond, abs_le]; constructor <;> linarith
    exact ⟨hq, (w_bounds hb (by linarith) hq).2⟩
  refine ⟨a, b, hra, hab, fun s hs => ?_, ?_⟩
  · obtain ⟨hq, hw⟩ := hsub s hs
    have hrs : r ≤ s := hra.trans hs.1
    rw [abs_of_nonneg (by linarith : 0 ≤ s - r)] at hw
    have hw' : s - r ≤ 3 / 2 * (ε * r) := by
      have := mul_le_mul_of_nonneg_left hvε (by linarith : (0 : ℝ) ≤ 1 + 2 * ε)
      have : (1 + 2 * ε) * (ε * r) ≤ 3 / 2 * (ε * r) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)]; nlinarith [hb.hrH]
    · rw [abs_of_nonneg (by nlinarith : 0 ≤ s ^ 2 - r ^ 2)]
      have : s ^ 2 - r ^ 2 = (s - r) * (s + r) := by ring
      have h1 : (s - r) * (s + r) ≤ (1 + 2 * ε) * sV r c * (3 * r) :=
        mul_le_mul hw (by nlinarith) (by linarith) (by positivity)
      have h2 : (1 + 2 * ε) * sV r c * (3 * r) ≤ 3 * (r ^ 2 * Real.sqrt c) * (6 / 5) := by
        have := mul_le_mul_of_nonneg_left hvc (by linarith : (0 : ℝ) ≤ 1 + 2 * ε)
        have h3 := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ 3 * r)
        have h4 : (3 * (1 + 2 * ε)) * (r ^ 2 * Real.sqrt c) ≤ 18 / 5 * (r ^ 2 * Real.sqrt c) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have e : (1 + 2 * ε) * (r * Real.sqrt c) * (3 * r) =
            (3 * (1 + 2 * ε)) * (r ^ 2 * Real.sqrt c) := by ring
        linarith
      linarith [hb.hwidth]
    · rw [Real.sqrt_sq hr.le, hcos]
      have := hq; rw [QCond] at this
      convert this using 2
  · have e := Q_sub (r ^ 2) a b
    rw [hQa, hQb] at e
    have ha' := (hsub a ⟨le_rfl, hab⟩).2
    have hb' := (hsub b ⟨hab, le_rfl⟩).2
    rw [abs_of_nonneg (by linarith : 0 ≤ a - r)] at ha'
    rw [abs_of_nonneg (by linarith : 0 ≤ b - r)] at hb'
    have hwp : (1 + 2 * ε) * sV r c ≤ 3 / 2 * (ε * r) := by
      have := mul_le_mul_of_nonneg_left hvε (by linarith : (0 : ℝ) ≤ 1 + 2 * ε)
      have : (1 + 2 * ε) * (ε * r) ≤ 3 / 2 * (ε * r) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    set w := (1 + 2 * ε) * sV r c
    have hf : a ^ 2 + a * b + b ^ 2 - 3 * r ^ 2 ≤ 6 * r * w * (1 + ε) := by
      have e2 : a ^ 2 + a * b + b ^ 2 - 3 * r ^ 2 =
          3 * r * ((a - r) + (b - r)) + ((a - r) ^ 2 + (a - r) * (b - r) + (b - r) ^ 2) := by ring
      have t1 : (a - r) ^ 2 + (a - r) * (b - r) + (b - r) ^ 2 ≤ 3 * w ^ 2 := by
        have := mul_le_mul ha' hb' (by linarith) (by positivity)
        have := mul_le_mul ha' ha' (by linarith) (by positivity)
        have := mul_le_mul hb' hb' (by linarith) (by positivity)
        linarith
      have t2 : 3 * w ^ 2 ≤ 6 * r * w * ε := by
        have hw0 : 0 ≤ w := by positivity
        have := mul_le_mul_of_nonneg_left hwp hw0
        have : 0 ≤ r * w * ε := by positivity
        linarith
      have t3 := mul_le_mul_of_nonneg_left (add_le_add ha' hb') (by linarith : (0 : ℝ) ≤ 3 * r)
      linarith
    have hpos : 0 < 6 * r * w * (1 + ε) := by positivity
    have : 54 * H ≤ (b - a) * (6 * r * w * (1 + ε)) := by
      have := mul_le_mul_of_nonneg_left hf (by linarith : (0 : ℝ) ≤ b - a)
      have e3 : Q (r ^ 2) a - Q (r ^ 2) b = (b - a) * (a ^ 2 + a * b + b ^ 2 - 3 * r ^ 2) := by
        rw [Q_sub]; ring
      linarith
    rw [m, div_div, div_le_iff₀ (by positivity)]
    calc 9 * H = 54 * H / 6 := by ring
      _ ≤ (b - a) * (6 * r * w * (1 + ε)) / 6 := by gcongr
      _ = (b - a) * (r * sV r c * ((1 + 2 * ε) * (1 + ε))) := by simp only [w]; ring

theorem volume_lower {H r c ε θ : ℝ} (hb : Bulk H r c ε) (hcos : Real.cos θ = 1 - c) :
    ENNReal.ofReal (2 * m H r c - 5 * ε * m H r c) ≤ volume (E H (r ^ 2) θ) := by
  obtain ⟨a, b, -, hab, hbr, h1, l1⟩ := lower_interval1 hb hcos
  obtain ⟨a', b', hra', hab', h2, l2⟩ := lower_interval2 hb hcos
  have hε := hb.hε1; have hε0 := hb.hε
  have hm := m_pos hb
  have hdisj : Disjoint (Set.Icc a b) (Set.Ioc a' b') := by
    rw [Set.disjoint_left]
    intro x hx hx'
    linarith [hx.2, hx'.1]
  have hU : Set.Icc a b ∪ Set.Ioc a' b' ⊆ E H (r ^ 2) θ :=
    Set.union_subset h1 (Set.Ioc_subset_Icc_self.trans h2)
  refine le_trans ?_ (measure_mono hU)
  rw [measure_union hdisj measurableSet_Ioc, Real.volume_Icc, Real.volume_Ioc,
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  have c1 : m H r c * (1 - 2 * ε) ≤ m H r c / (1 + 2 * ε) := by
    rw [le_div_iff₀ (by linarith)]
    have := mul_nonneg hm.le (sq_nonneg ε)
    nlinarith
  have c2 : m H r c * (1 - 3 * ε) ≤ m H r c / ((1 + 2 * ε) * (1 + ε)) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_nonneg hm.le (sq_nonneg ε)
    have := mul_nonneg hm.le (pow_nonneg hε0.le 3)
    nlinarith
  nlinarith

theorem E_subset (H n θ : ℝ) : E H n θ ⊆ Set.Icc (-H) H := fun _ hs => abs_le.mp hs.1

theorem volume_E_ne_top (H n θ : ℝ) : volume (E H n θ) ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (measure_mono (E_subset H n θ))

/-- **`eq:width`**: in the bulk, `|W - 2m| ≤ 13 ε m`, `m = 9H/(r√V)`, `V = (2/3) r² c`. -/
theorem W_bulk {H r c ε θ : ℝ} (hb : Bulk H r c ε) (hcos : Real.cos θ = 1 - c) :
    |W H (r ^ 2) θ - 2 * m H r c| ≤ 13 * ε * m H r c := by
  have hm := m_pos hb
  have hε0 := hb.hε
  have up := W_le_of_volume (by positivity) (volume_upper hb hcos)
  have low : 2 * m H r c - 5 * ε * m H r c ≤ W H (r ^ 2) θ := by
    have := volume_lower hb hcos
    rw [W]
    exact (ENNReal.ofReal_le_iff_le_toReal (volume_E_ne_top _ _ _)).mp this
  rw [abs_le]; constructor <;> nlinarith

end Cubic.BoxAsymptotic.TraceAsymptotic
