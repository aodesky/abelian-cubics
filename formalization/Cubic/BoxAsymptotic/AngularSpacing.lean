import Cubic.BoxAsymptotic.EisensteinCoordinates
import Cubic.Counting.CenteredEllipseCount
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Angular spacing of primitive lattice vectors

For primitive `v ≠ w` in `ℤ[ζ]` of norm at most `T`, the arguments differ by at least
`√3/(2T)` modulo `2π`: the determinant `v₂w₁ - v₁w₂` is a nonzero integer unless `w = ±v`,
and `‖v‖‖w‖ sin(arg v - arg w) = (√3/2)(v₂w₁ - v₁w₂)`. Hence an arc of length `2ℓ`
contains at most `4ℓT/√3 + 1` of them. Also: lattice-point counts `#{0 < N v ≤ R} ≪ R` and
`Σ_{0 < N v ≤ R} 1/N v ≪ 1 + log R`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularSpacing

open CubicTargets.BoxAsymptotic (eis)
open Cubic.BoxAsymptotic.EisensteinCoordinates
open Real

/-- `θ` lies within `Θ` of `θ₀` modulo `2π`. -/
def near (θ θ₀ Θ : ℝ) : Prop := ∃ k : ℤ, |θ - θ₀ - 2 * π * k| ≤ Θ

/-- A primitive vector. -/
def prim (p : ℤ × ℤ) : Prop := Int.gcd p.1 p.2 = 1

theorem prim_ne_zero {p : ℤ × ℤ} (hp : prim p) : p ≠ 0 := by
  rintro rfl; simp [prim] at hp

theorem one_le_nrm {p : ℤ × ℤ} (hp : p ≠ 0) : 1 ≤ nrm p := by
  have h0 := nrm_nonneg p
  have h1 : nrm p ≠ 0 := fun h => hp (nrm_eq_zero.mp h)
  omega

/-- Primitive vectors with vanishing determinant are equal up to sign. -/
theorem eq_or_eq_neg {v w : ℤ × ℤ} (hv : prim v) (hw : prim w)
    (hd : v.1 * w.2 = v.2 * w.1) : w = v ∨ w = -v := by
  have hb := Int.gcd_eq_gcd_ab v.1 v.2
  rw [show (Int.gcd v.1 v.2 : ℤ) = 1 by exact_mod_cast hv] at hb
  set x := Int.gcdA v.1 v.2
  set y := Int.gcdB v.1 v.2
  set l := w.1 * x + w.2 * y
  have h1 : w.1 = l * v.1 := by simp only [l]; linear_combination w.1 * hb - y * hd
  have h2 : w.2 = l * v.2 := by simp only [l]; linear_combination w.2 * hb + x * hd
  have hl : l.natAbs = 1 := by
    have := hw
    simp only [prim] at this hv
    rw [h1, h2, Int.gcd_mul_left, hv, mul_one] at this
    exact this
  rcases Int.natAbs_eq_iff.mp hl with h | h
  · left; ext
    · rw [h1, h]; simp
    · rw [h2, h]; simp
  · right; ext
    · rw [h1, h]; simp
    · rw [h2, h]; simp

theorem norm_mul_sin (v w : ℤ × ℤ) (hv : v ≠ 0) (hw : w ≠ 0) :
    ‖eis v‖ * ‖eis w‖ * Real.sin (Complex.arg (eis v) - Complex.arg (eis w)) =
      Real.sqrt 3 / 2 * (v.2 * w.1 - v.1 * w.2) := by
  have hv' := eis_ne_zero hv
  have hw' := eis_ne_zero hw
  have n1 : ‖eis v‖ ≠ 0 := norm_ne_zero_iff.mpr hv'
  have n2 : ‖eis w‖ ≠ 0 := norm_ne_zero_iff.mpr hw'
  rw [Real.sin_sub, Complex.sin_arg, Complex.sin_arg, Complex.cos_arg hv', Complex.cos_arg hw']
  field_simp
  simp only [eis]
  ring

theorem norm_mul_cos (v w : ℤ × ℤ) (hv : v ≠ 0) (hw : w ≠ 0) :
    ‖eis v‖ * ‖eis w‖ * Real.cos (Complex.arg (eis v) - Complex.arg (eis w)) =
      (eis v).re * (eis w).re + (eis v).im * (eis w).im := by
  have hv' := eis_ne_zero hv
  have hw' := eis_ne_zero hw
  have n1 : ‖eis v‖ ≠ 0 := norm_ne_zero_iff.mpr hv'
  have n2 : ‖eis w‖ ≠ 0 := norm_ne_zero_iff.mpr hw'
  rw [Real.cos_sub, Complex.sin_arg, Complex.sin_arg, Complex.cos_arg hv', Complex.cos_arg hw']
  field_simp

theorem norm_eis_le {v : ℤ × ℤ} {T : ℝ} (h : (nrm v : ℝ) ≤ T) : ‖eis v‖ ≤ Real.sqrt T := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_eis_sq]
  exact Real.sqrt_le_sqrt h

/-- Two distinct primitive vectors of norm `≤ T` have arguments at least `√3/(2T)` apart,
for any representatives modulo `2π`. -/
theorem spacing {v w : ℤ × ℤ} (hv : prim v) (hw : prim w) (hne : v ≠ w) {T : ℝ}
    (hvT : (nrm v : ℝ) ≤ T) (hwT : (nrm w : ℝ) ≤ T) (kv kw : ℤ) :
    Real.sqrt 3 / (2 * T) ≤
      |(Complex.arg (eis v) - 2 * π * kv) - (Complex.arg (eis w) - 2 * π * kw)| := by
  have hv0 := prim_ne_zero hv
  have hw0 := prim_ne_zero hw
  have hT : 1 ≤ T := le_trans (by exact_mod_cast one_le_nrm hv0) hvT
  have hT0 : 0 < T := by linarith
  set x := (Complex.arg (eis v) - 2 * π * kv) - (Complex.arg (eis w) - 2 * π * kw)
  have hx : x = Complex.arg (eis v) - Complex.arg (eis w) - (kv - kw : ℤ) * (2 * π) := by
    simp only [x]; push_cast; ring
  have hsin : Real.sin x = Real.sin (Complex.arg (eis v) - Complex.arg (eis w)) := by
    rw [hx, Real.sin_sub_int_mul_two_pi]
  have hcos : Real.cos x = Real.cos (Complex.arg (eis v) - Complex.arg (eis w)) := by
    rw [hx, Real.cos_sub_int_mul_two_pi]
  have hnn : ‖eis v‖ * ‖eis w‖ ≤ T := by
    calc ‖eis v‖ * ‖eis w‖ ≤ Real.sqrt T * Real.sqrt T :=
          mul_le_mul (norm_eis_le hvT) (norm_eis_le hwT) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = T := Real.mul_self_sqrt hT0.le
  have hpos : 0 < ‖eis v‖ * ‖eis w‖ :=
    mul_pos (norm_pos_iff.mpr (eis_ne_zero hv0)) (norm_pos_iff.mpr (eis_ne_zero hw0))
  have h3 : 0 < Real.sqrt 3 := by positivity
  by_cases hd : v.1 * w.2 = v.2 * w.1
  · -- `w = -v`: the arguments differ by `π`
    rcases eq_or_eq_neg hv hw hd with h | h
    · exact absurd h.symm hne
    have hc := norm_mul_cos v w hv0 hw0
    rw [← hcos] at hc
    have hneg : (eis v).re * (eis w).re + (eis v).im * (eis w).im < 0 := by
      have : eis w = -eis v := by
        rw [h]
        have := eis_smul (-1) v
        rw [neg_smul, one_smul] at this
        rw [this]; push_cast; ring
      rw [this, Complex.neg_re, Complex.neg_im]
      have := Complex.normSq_pos.mpr (eis_ne_zero hv0)
      rw [Complex.normSq_apply] at this
      linarith
    have hcx : Real.cos x < 0 := by
      by_contra hc0; push_neg at hc0
      have := mul_nonneg hpos.le hc0
      linarith
    by_contra hlt; push_neg at hlt
    have hδ : Real.sqrt 3 / (2 * T) < π / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have : Real.sqrt 3 < 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      nlinarith [Real.pi_gt_three]
    have := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp (hlt.trans hδ)).1],
      (abs_lt.mp (hlt.trans hδ)).2⟩
    linarith
  · -- nonzero determinant
    have hD : (1 : ℝ) ≤ |(v.2 * w.1 - v.1 * w.2 : ℤ)| := by
      have : (v.2 * w.1 - v.1 * w.2 : ℤ) ≠ 0 := fun h => hd (by linarith)
      exact_mod_cast Int.one_le_abs this
    have hs := norm_mul_sin v w hv0 hw0
    rw [← hsin] at hs
    have hsx : Real.sqrt 3 / 2 ≤ ‖eis v‖ * ‖eis w‖ * |Real.sin x| := by
      rw [← abs_of_pos hpos, ← abs_mul, hs, abs_mul, abs_of_pos (by positivity : 0 < √3 / 2)]
      push_cast at hD
      nlinarith
    have hsx' : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
    rw [div_le_iff₀ (by positivity)]
    have : ‖eis v‖ * ‖eis w‖ * |Real.sin x| ≤ T * |x| :=
      mul_le_mul hnn hsx' (abs_nonneg _) hT0.le
    nlinarith

/-- An arc of half-width `ℓ` contains at most `4ℓT/√3 + 1` primitive vectors of norm `≤ T`. -/
theorem card_le {S : Finset (ℤ × ℤ)} {T a ℓ : ℝ} (hT : 0 ≤ T) (hℓ : 0 ≤ ℓ)
    (hS : ∀ v ∈ S, prim v ∧ (nrm v : ℝ) ≤ T ∧ near (Complex.arg (eis v)) a ℓ) :
    (S.card : ℝ) ≤ 4 * ℓ * T / Real.sqrt 3 + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · simp; positivity
  have hT1 : 1 ≤ T := le_trans (by exact_mod_cast one_le_nrm (prim_ne_zero (hS v₀ hv₀).1))
    (hS v₀ hv₀).2.1
  have h3 : 0 < Real.sqrt 3 := by positivity
  set δ := Real.sqrt 3 / (2 * T) with hδ
  have hδ0 : 0 < δ := by positivity
  classical
  choose! k hk using fun v hv => (hS v hv).2.2
  set φ : ℤ × ℤ → ℝ := fun v => Complex.arg (eis v) - 2 * π * k v
  set b : ℤ × ℤ → ℕ := fun v => ⌊(φ v - a + ℓ) / δ⌋₊
  have hmaps : ∀ v ∈ S, b v ∈ Finset.range (⌊2 * ℓ / δ⌋₊ + 1) := by
    intro v hv
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    have := (abs_le.mp (hk v hv)).2
    apply div_le_div_of_nonneg_right _ hδ0.le
    simp only [φ]; linarith
  have hinj : Set.InjOn b S := by
    intro v hv w hw hb
    by_contra hne
    have hx0 : ∀ u ∈ S, 0 ≤ (φ u - a + ℓ) / δ := fun u hu =>
      div_nonneg (by have := (abs_le.mp (hk u hu)).1; simp only [φ]; linarith) hδ0.le
    have e1 := Nat.floor_le (hx0 v hv)
    have e2 := Nat.lt_floor_add_one ((φ v - a + ℓ) / δ)
    have e3 := Nat.floor_le (hx0 w hw)
    have e4 := Nat.lt_floor_add_one ((φ w - a + ℓ) / δ)
    simp only [b] at hb
    rw [hb] at e1 e2
    have hlt : |φ v - φ w| < δ := by
      have : |(φ v - a + ℓ) / δ - (φ w - a + ℓ) / δ| < 1 := by
        rw [abs_lt]; constructor <;> linarith
      rw [← sub_div, abs_div, abs_of_pos hδ0, div_lt_one hδ0] at this
      convert this using 2; ring
    have := spacing (hS v hv).1 (hS w hw).1 hne (hS v hv).2.1 (hS w hw).2.1 (k v) (k w)
    linarith
  have hcard := Finset.card_le_card_of_injOn (t := Finset.range (⌊2 * ℓ / δ⌋₊ + 1)) b (fun v hv => Finset.mem_coe.mpr (hmaps v hv)) hinj
  rw [Finset.card_range] at hcard
  calc (S.card : ℝ) ≤ ((⌊2 * ℓ / δ⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * ℓ / δ + 1 := by
        push_cast; linarith [Nat.floor_le (by positivity : 0 ≤ 2 * ℓ / δ)]
    _ = 4 * ℓ * T / Real.sqrt 3 + 1 := by
        rw [hδ]; field_simp; ring

end Cubic.BoxAsymptotic.AngularSpacing
