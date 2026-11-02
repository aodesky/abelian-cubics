import Cubic.BoxAsymptotic.SectorBound
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The trace set `W_H(n, θ)` (upper bounds of `lem:geometry`)

For `β` of norm `n³` and argument `θ`, the real traces `s` allowed by `eq:box` form
`E = {s : |s| ≤ H, |s² - n| ≤ 3H, |Q(s) - 2n^{3/2} cos θ| ≤ 27H}` with `Q(s) = 3sn - s³`,
and `W_H(n, θ)` is its Lebesgue measure.

Write `r = √n` and `w = ||s| - r|`. On each of the four pieces `s ≥ r`, `0 ≤ s ≤ r`,
`-r ≤ s ≤ 0`, `s ≤ -r` (where `Q` is monotone),
`Q(s₁) - Q(s₂) = (s₁ - s₂)(3n - s₁² - s₁s₂ - s₂²)` gives
`|Q(s₁) - Q(s₂)| ≥ r (w₁ + w₂) |s₁ - s₂|`. Since `Q` varies by at most `54H` on `E`, each
piece of `E` has diameter `≤ √(54H/r)`, and `≤ 54H/(2rω)` if `w ≥ ω` there. This is the
draft's normalization `s = √n v` with the nondegenerate critical points `v = ±1`.
Moreover `|Q(s)| ≥ 2r³ - 3rw² - w³`, so on `E`,
`2r³(1 - |cos θ|) ≤ 3rw² + w³ + 27H`: points of `E` stay away from `±r` unless `θ` is
close to `πℤ`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.TraceWidth

open MeasureTheory Real

/-- `Q(s) = 3sn - s³`. -/
def Q (n s : ℝ) : ℝ := 3 * s * n - s ^ 3

/-- The real traces allowed by `eq:box`. -/
def E (H n θ : ℝ) : Set ℝ :=
  {s | |s| ≤ H ∧ |s ^ 2 - n| ≤ 3 * H ∧ |Q n s - 2 * (n * Real.sqrt n) * Real.cos θ| ≤ 27 * H}

/-- `W_H(n, θ)`. -/
def W (H n θ : ℝ) : ℝ := (volume (E H n θ)).toReal

theorem Q_neg (n s : ℝ) : Q n (-s) = -Q n s := by simp only [Q]; ring

theorem Q_sub (n s₁ s₂ : ℝ) :
    Q n s₁ - Q n s₂ = (s₁ - s₂) * (3 * n - s₁ ^ 2 - s₁ * s₂ - s₂ ^ 2) := by
  simp only [Q]; ring

/-- The distance of `|s|` from the critical point `r`. -/
def dist' (r s : ℝ) : ℝ := |(|s| - r)|

/-- Monotone pieces. -/
def piece (r : ℝ) : Fin 4 → Set ℝ
  | 0 => {s | 0 ≤ s ∧ r ≤ s}
  | 1 => {s | 0 ≤ s ∧ s ≤ r}
  | 2 => {s | s ≤ 0 ∧ r ≤ -s}
  | 3 => {s | s ≤ 0 ∧ -s ≤ r}

theorem mem_some_piece (r s : ℝ) : ∃ k, s ∈ piece r k := by
  rcases le_total 0 s with h | h <;> rcases le_total r |s| with h' | h'
  · exact ⟨0, h, by rwa [abs_of_nonneg h] at h'⟩
  · exact ⟨1, h, by rwa [abs_of_nonneg h] at h'⟩
  · exact ⟨2, h, by rwa [abs_of_nonpos h] at h'⟩
  · exact ⟨3, h, by rwa [abs_of_nonpos h] at h'⟩

/-- The key inequality on a nonnegative piece. -/
theorem key_nonneg {r s₁ s₂ : ℝ} (hr : 0 ≤ r) (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂)
    (hs : (r ≤ s₁ ∧ r ≤ s₂) ∨ (s₁ ≤ r ∧ s₂ ≤ r)) :
    r * (dist' r s₁ + dist' r s₂) * |s₁ - s₂| ≤ |Q (r ^ 2) s₁ - Q (r ^ 2) s₂| ∧
      |s₁ - s₂| ≤ dist' r s₁ + dist' r s₂ := by
  simp only [dist', abs_of_nonneg h₁, abs_of_nonneg h₂]
  rw [Q_sub, abs_mul]
  rcases hs with ⟨a, b⟩ | ⟨a, b⟩
  · rw [abs_of_nonneg (by linarith : 0 ≤ s₁ - r), abs_of_nonneg (by linarith : 0 ≤ s₂ - r)]
    refine ⟨?_, ?_⟩
    · rw [abs_of_nonpos (by nlinarith : 3 * r ^ 2 - s₁ ^ 2 - s₁ * s₂ - s₂ ^ 2 ≤ 0)]
      have : r * (s₁ - r + (s₂ - r)) ≤ -(3 * r ^ 2 - s₁ ^ 2 - s₁ * s₂ - s₂ ^ 2) := by nlinarith
      nlinarith [abs_nonneg (s₁ - s₂)]
    · rw [abs_le]; constructor <;> linarith
  · rw [abs_of_nonpos (by linarith : s₁ - r ≤ 0), abs_of_nonpos (by linarith : s₂ - r ≤ 0)]
    refine ⟨?_, ?_⟩
    · have hf : r * (-(s₁ - r) + -(s₂ - r)) ≤ 3 * r ^ 2 - s₁ ^ 2 - s₁ * s₂ - s₂ ^ 2 := by
        nlinarith
      rw [abs_of_nonneg (by nlinarith : 0 ≤ 3 * r ^ 2 - s₁ ^ 2 - s₁ * s₂ - s₂ ^ 2)]
      nlinarith [abs_nonneg (s₁ - s₂)]
    · rw [abs_le]; constructor <;> linarith

theorem dist'_neg (r s : ℝ) : dist' r (-s) = dist' r s := by simp [dist']

/-- The key inequality on any piece. -/
theorem key {r s₁ s₂ : ℝ} (hr : 0 ≤ r) {k : Fin 4} (h₁ : s₁ ∈ piece r k) (h₂ : s₂ ∈ piece r k) :
    r * (dist' r s₁ + dist' r s₂) * |s₁ - s₂| ≤ |Q (r ^ 2) s₁ - Q (r ^ 2) s₂| ∧
      |s₁ - s₂| ≤ dist' r s₁ + dist' r s₂ := by
  fin_cases k <;> simp only [piece, Set.mem_setOf_eq] at h₁ h₂
  · exact key_nonneg hr h₁.1 h₂.1 (Or.inl ⟨h₁.2, h₂.2⟩)
  · exact key_nonneg hr h₁.1 h₂.1 (Or.inr ⟨h₁.2, h₂.2⟩)
  · have := key_nonneg (s₁ := -s₁) (s₂ := -s₂) hr (by linarith) (by linarith)
      (Or.inl ⟨h₁.2, h₂.2⟩)
    rwa [dist'_neg, dist'_neg, Q_neg, Q_neg, show -Q (r ^ 2) s₁ - -Q (r ^ 2) s₂ =
      -(Q (r ^ 2) s₁ - Q (r ^ 2) s₂) by ring, abs_neg, show -s₁ - -s₂ = -(s₁ - s₂) by ring,
      abs_neg] at this
  · have := key_nonneg (s₁ := -s₁) (s₂ := -s₂) hr (by linarith) (by linarith)
      (Or.inr ⟨h₁.2, h₂.2⟩)
    rwa [dist'_neg, dist'_neg, Q_neg, Q_neg, show -Q (r ^ 2) s₁ - -Q (r ^ 2) s₂ =
      -(Q (r ^ 2) s₁ - Q (r ^ 2) s₂) by ring, abs_neg, show -s₁ - -s₂ = -(s₁ - s₂) by ring,
      abs_neg] at this

/-- `|Q(s)| ≥ 2r³ - 3rw² - w³`. -/
theorem abs_Q_ge (r s : ℝ) :
    2 * r ^ 3 - 3 * r * dist' r s ^ 2 - dist' r s ^ 3 ≤ |Q (r ^ 2) s| := by
  have hQ : |Q (r ^ 2) s| = |Q (r ^ 2) (|s|)| := by
    rcases le_total 0 s with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Q_neg, abs_neg]
  rw [hQ, dist']
  set t := |s|
  have ht : 0 ≤ t := abs_nonneg s
  rcases le_total r t with h | h
  · rw [abs_of_nonneg (by linarith : 0 ≤ t - r)]
    refine le_trans (le_of_eq ?_) (le_abs_self _)
    simp only [Q]; ring
  · rw [abs_of_nonpos (by linarith : t - r ≤ 0)]
    refine le_trans ?_ (le_abs_self _)
    simp only [Q]
    nlinarith [mul_nonneg (by linarith : 0 ≤ r - t) (mul_nonneg (by linarith : 0 ≤ r - t)
      (by linarith : 0 ≤ r - t))]

/-- On `E`, `2r³(1 - |cos θ|) ≤ 3rw² + w³ + 27H`. -/
theorem away {H r θ s : ℝ} (hr : 0 ≤ r) (hs : s ∈ E H (r ^ 2) θ) :
    2 * r ^ 3 * (1 - |Real.cos θ|) ≤ 3 * r * dist' r s ^ 2 + dist' r s ^ 3 + 27 * H := by
  have h := hs.2.2
  have hsq : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr
  rw [hsq] at h
  have h1 := abs_Q_ge r s
  have h2 : |Q (r ^ 2) s| ≤ |2 * (r ^ 2 * r) * Real.cos θ| + 27 * H := by
    have := abs_sub_abs_le_abs_sub (Q (r ^ 2) s) (2 * (r ^ 2 * r) * Real.cos θ)
    linarith
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (r ^ 2 * r))] at h2
  nlinarith

theorem dist_le_of_mem {H r θ s : ℝ} (hr : 0 < r) (hs : s ∈ E H (r ^ 2) θ) :
    dist' r s ≤ 3 * H / r := by
  have h := hs.2.1
  rw [le_div_iff₀ hr, dist']
  have ht : 0 ≤ |s| := abs_nonneg s
  have e : |s| ^ 2 = s ^ 2 := sq_abs s
  rw [← e] at h
  have : |(|s| - r)| * (|s| + r) = |(|s| ^ 2 - r ^ 2)| := by
    rw [show |s| ^ 2 - r ^ 2 = (|s| - r) * (|s| + r) by ring, abs_mul,
      abs_of_pos (by linarith : 0 < |s| + r)]
  nlinarith [abs_nonneg (|s| - r)]


theorem Q_close {H r θ s₁ s₂ : ℝ} (h₁ : s₁ ∈ E H (r ^ 2) θ) (h₂ : s₂ ∈ E H (r ^ 2) θ) :
    |Q (r ^ 2) s₁ - Q (r ^ 2) s₂| ≤ 54 * H := by
  have a := h₁.2.2
  have b := h₂.2.2
  set J := 2 * (r ^ 2 * Real.sqrt (r ^ 2)) * Real.cos θ
  rw [show Q (r ^ 2) s₁ - Q (r ^ 2) s₂ = (Q (r ^ 2) s₁ - J) - (Q (r ^ 2) s₂ - J) by ring]
  exact (abs_sub _ _).trans (by linarith)

theorem volume_le_of_diam {S : Set ℝ} {d : ℝ} (h : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ d) :
    volume S ≤ ENNReal.ofReal d :=
  (Real.volume_le_diam S).trans (Metric.ediam_le fun x hx y hy => by
    rw [edist_dist, Real.dist_eq]; exact ENNReal.ofReal_le_ofReal (h x hx y hy))

theorem volume_le_sum (H r θ : ℝ) :
    volume (E H (r ^ 2) θ) ≤ ∑ k : Fin 4, volume (E H (r ^ 2) θ ∩ piece r k) := by
  refine le_trans (measure_mono fun s hs => ?_) (measure_iUnion_fintype_le _ _)
  obtain ⟨k, hk⟩ := mem_some_piece r s
  exact Set.mem_iUnion.mpr ⟨k, hs, hk⟩

/-- Each piece has diameter `≤ √(54H/r)`. -/
theorem piece_le_sqrt {H r θ : ℝ} (hr : 0 < r) (k : Fin 4) :
    volume (E H (r ^ 2) θ ∩ piece r k) ≤ ENNReal.ofReal (Real.sqrt (54 * H / r)) := by
  refine volume_le_of_diam fun x hx y hy => ?_
  obtain ⟨k1, k2⟩ := key hr.le hx.2 hy.2
  have hc := Q_close hx.1 hy.1
  apply Real.abs_le_sqrt
  rw [le_div_iff₀ hr]
  have h3 : r * |x - y| * |x - y| ≤ r * (dist' r x + dist' r y) * |x - y| :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left k2 hr.le) (abs_nonneg _)
  have h4 : (x - y) ^ 2 = |x - y| * |x - y| := by rw [← sq, sq_abs]
  nlinarith

/-- If `w ≥ ω > 0` on a piece, it has diameter `≤ 54H/(2rω)`. -/
theorem piece_le_away {H r θ ω : ℝ} (hr : 0 < r) (hω : 0 < ω) (k : Fin 4)
    (hw : ∀ s ∈ E H (r ^ 2) θ ∩ piece r k, ω ≤ dist' r s) :
    volume (E H (r ^ 2) θ ∩ piece r k) ≤ ENNReal.ofReal (54 * H / (2 * r * ω)) := by
  refine volume_le_of_diam fun x hx y hy => ?_
  obtain ⟨k1, -⟩ := key hr.le hx.2 hy.2
  have hc := Q_close hx.1 hy.1
  rw [le_div_iff₀ (by positivity)]
  have := hw x hx
  have := hw y hy
  have : r * (2 * ω) * |x - y| ≤ r * (dist' r x + dist' r y) * |x - y| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hr.le; linarith
  nlinarith

theorem W_nonneg (H n θ : ℝ) : 0 ≤ W H n θ := ENNReal.toReal_nonneg

theorem W_le_of_volume {H n θ d : ℝ} (hd : 0 ≤ d) (h : volume (E H n θ) ≤ ENNReal.ofReal d) :
    W H n θ ≤ d := ENNReal.toReal_le_of_le_ofReal hd h

theorem sum_four (f : Fin 4 → ENNReal) (d : ℝ) (h : ∀ k, f k ≤ ENNReal.ofReal d) :
    ∑ k, f k ≤ ENNReal.ofReal (4 * d) := by
  calc ∑ k, f k ≤ ∑ _k : Fin 4, ENNReal.ofReal d := Finset.sum_le_sum fun k _ => h k
    _ = ENNReal.ofReal (4 * d) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- `W ≤ 4√(54H/√n)`: the critical-point bound `W ≪ H^{1/2} n^{-1/4}`. -/
theorem W_le_sqrt {H n θ : ℝ} (hn : 0 < n) :
    W H n θ ≤ 4 * Real.sqrt (54 * H / Real.sqrt n) := by
  have hr : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have e : n = Real.sqrt n ^ 2 := (Real.sq_sqrt hn.le).symm
  refine W_le_of_volume (by positivity) ?_
  rw [e]
  refine (volume_le_sum H _ θ).trans (sum_four _ _ fun k => ?_)
  rw [← e]
  simpa [← e] using piece_le_sqrt (H := H) (θ := θ) hr k

/-- Away from `θ ∈ πℤ`: with `c = 1 - |cos θ| > 0` and `27H ≤ n^{3/2} c`,
`W ≤ 216 H/(n √c)`. -/
theorem W_le_away {H n θ : ℝ} (hn : 0 < n) (hH : 0 ≤ H) (hc : 0 < 1 - |Real.cos θ|)
    (hbig : 27 * H ≤ Real.sqrt n ^ 3 * (1 - |Real.cos θ|)) :
    W H n θ ≤ 216 * H / (n * Real.sqrt (1 - |Real.cos θ|)) := by
  set r := Real.sqrt n
  set c := 1 - |Real.cos θ|
  have hr : 0 < r := Real.sqrt_pos.mpr hn
  have e : n = r ^ 2 := (Real.sq_sqrt hn.le).symm
  have hc1 : c ≤ 1 := by simp only [c]; linarith [abs_nonneg (Real.cos θ)]
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsc1 : Real.sqrt c ≤ 1 := Real.sqrt_le_one.mpr hc1
  have hscsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  set ω := r * Real.sqrt c / 2
  have hω : 0 < ω := by positivity
  have hw : ∀ s ∈ E H (r ^ 2) θ, ω ≤ dist' r s := by
    intro s hs
    have ha := away hr.le hs
    have hd : 0 ≤ dist' r s := abs_nonneg _
    by_contra hlt
    push_neg at hlt
    have h1 : dist' r s ≤ r / 2 := by
      have : ω ≤ r / 2 := by
        simp only [ω]; nlinarith
      linarith
    have h2 : dist' r s ^ 2 < r ^ 2 * c / 4 := by
      have : dist' r s ^ 2 < ω ^ 2 := by nlinarith
      have : ω ^ 2 = r ^ 2 * c / 4 := by simp only [ω]; rw [div_pow, mul_pow, hscsq]; ring
      linarith
    have : dist' r s ^ 3 ≤ r / 2 * dist' r s ^ 2 := by nlinarith
    nlinarith
  refine W_le_of_volume (by positivity) ?_
  rw [e]
  refine (volume_le_sum H r θ).trans ?_
  have := sum_four (fun k => volume (E H (r ^ 2) θ ∩ piece r k)) (54 * H / (2 * r * ω))
    fun k => piece_le_away hr hω k fun s hs => hw s hs.1
  refine this.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  simp only [ω]
  field_simp
  ring

/-- `E` is empty once `n > H² + 3H`. -/
theorem E_eq_empty {H n θ : ℝ} (hn : H ^ 2 + 3 * H < n) : E H n θ = ∅ := by
  ext s
  simp only [E, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2, -⟩
  have : s ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg s) h1 2
  rw [abs_le] at h2
  linarith [h2.1]

theorem W_eq_zero {H n θ : ℝ} (hn : H ^ 2 + 3 * H < n) : W H n θ = 0 := by
  rw [W, E_eq_empty hn]; simp

/-- If `E ≠ ∅`, then `2r³(1 - |cos θ|) ≤ 27H + 27H²/r + 27H³/r³`. -/
theorem angle_of_nonempty {H n θ : ℝ} (hn : 0 < n) (hE : (E H n θ).Nonempty) :
    2 * Real.sqrt n ^ 3 * (1 - |Real.cos θ|) ≤
      27 * H + 27 * H ^ 2 / Real.sqrt n + 27 * H ^ 3 / Real.sqrt n ^ 3 := by
  set r := Real.sqrt n
  have hr : 0 < r := Real.sqrt_pos.mpr hn
  have e : n = r ^ 2 := (Real.sq_sqrt hn.le).symm
  obtain ⟨s, hs⟩ := hE
  rw [e] at hs
  have ha := away hr.le hs
  have hd := dist_le_of_mem hr hs
  have hd0 : 0 ≤ dist' r s := abs_nonneg _
  have h2 : dist' r s ^ 2 ≤ (3 * H / r) ^ 2 := pow_le_pow_left₀ hd0 hd 2
  have h3 : dist' r s ^ 3 ≤ (3 * H / r) ^ 3 := pow_le_pow_left₀ hd0 hd 3
  have : 3 * r * (3 * H / r) ^ 2 = 27 * H ^ 2 / r := by field_simp; ring
  have : (3 * H / r) ^ 3 = 27 * H ^ 3 / r ^ 3 := by field_simp; ring
  nlinarith

end Cubic.BoxAsymptotic.TraceWidth
