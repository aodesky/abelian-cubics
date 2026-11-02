import CubicTargets.BoxAsymptotic.Statement
import Cubic.Counting.GeneralHeightReduction

/-!
# The exact parametrization (`eq:disc`, `eq:cong`)

For `f = t³ - s t² + b t + c` put `n = s² - 3b` and `J = 3sn - s³ - 27c`. Then
`27 disc(f) = 4n³ - J²`. If `disc(f) = d²`, then `β = (J + 3d√-3)/2 = A + Bζ` with
`A = (J + 3d)/2`, `B = 3d` has `N β = n³`, and conversely `β = A + Bζ` of norm `n³` with an
integer `s` gives an integral cubic exactly under `eq:cong`. In mathlib's convention
`monicCubic a₂ a₁ a₀ = t³ + a₂t² + a₁t + a₀`, so `s = -a₂`, `b = a₁`, `c = a₀`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.Parametrization

open Cubic.Counting.GeneralMonicData

/-- The discriminant of `t³ + a₂t² + a₁t + a₀`. -/
def disc (a₂ a₁ a₀ : ℤ) : ℤ :=
  a₂ ^ 2 * a₁ ^ 2 - 4 * a₁ ^ 3 - 4 * a₂ ^ 3 * a₀ - 27 * a₀ ^ 2 + 18 * a₂ * a₁ * a₀

/-- `eq:disc`: `27 disc(f) = 4n³ - J²`, with `s = -a₂`, `b = a₁`, `c = a₀`. -/
theorem disc_eq (a₂ a₁ a₀ : ℤ) :
    27 * disc a₂ a₁ a₀ =
      4 * (a₂ ^ 2 - 3 * a₁) ^ 3 - (3 * (-a₂) * (a₂ ^ 2 - 3 * a₁) - (-a₂) ^ 3 - 27 * a₀) ^ 2 := by
  unfold disc; ring

/-- `4 N(A + Bζ) - (2A - B)² = 3 B²`. -/
theorem norm_identity (A B : ℤ) : 4 * (A ^ 2 - A * B + B ^ 2) - (2 * A - B) ^ 2 = 3 * B ^ 2 := by
  ring

/-- Admissible pairs `(s, n, A, B)` in the box with `B ≠ 0` (`eq:cong`, `eq:box`). -/
def pairs (H : ℝ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {x | 0 < x.2.1 ∧ x.2.2.1 ^ 2 - x.2.2.1 * x.2.2.2 + x.2.2.2 ^ 2 = x.2.1 ^ 3 ∧
    (3 : ℤ) ∣ x.2.2.2 ∧ x.2.2.2 ≠ 0 ∧ x.1 ^ 2 ≡ x.2.1 [ZMOD 3] ∧
    2 * x.2.2.1 - x.2.2.2 ≡ 3 * x.1 * x.2.1 - x.1 ^ 3 [ZMOD 27] ∧
    (|x.1| : ℝ) ≤ H ∧ (|x.1 ^ 2 - x.2.1| : ℝ) ≤ 3 * H ∧
    (|3 * x.1 * x.2.1 - x.1 ^ 3 - (2 * x.2.2.1 - x.2.2.2)| : ℝ) ≤ 27 * H}

/-- Coefficients `(a₂, a₁, a₀)` in the box with a chosen square root `d ≠ 0` of the
discriminant. -/
def boxSq (H : ℝ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {y | (|y.1| : ℝ) ≤ H ∧ (|y.2.1| : ℝ) ≤ H ∧ (|y.2.2.1| : ℝ) ≤ H ∧ y.2.2.2 ≠ 0 ∧
    disc y.1 y.2.1 y.2.2.1 = y.2.2.2 ^ 2}

/-- `(s, n, A, B) ↦ (-s, (s² - n)/3, (3sn - s³ - (2A - B))/27, B/3)`. -/
def toBox (x : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (-x.1, (x.1 ^ 2 - x.2.1) / 3, (3 * x.1 * x.2.1 - x.1 ^ 3 - (2 * x.2.2.1 - x.2.2.2)) / 27,
    x.2.2.2 / 3)

/-- `(a₂, a₁, a₀, d) ↦ (s, n, (J + 3d)/2, 3d)` with `s = -a₂`, `n = a₂² - 3a₁`,
`J = 3sn - s³ - 27a₀`. -/
def ofBox (y : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (-y.1, y.1 ^ 2 - 3 * y.2.1,
    (3 * (-y.1) * (y.1 ^ 2 - 3 * y.2.1) - (-y.1) ^ 3 - 27 * y.2.2.1 + 3 * y.2.2.2) / 2,
    3 * y.2.2.2)

/-- The parity in `eq:disc`: `J² + 27d² = 4n³` forces `J ≡ d (mod 2)`. -/
theorem two_dvd_of {J d n : ℤ} (h : J ^ 2 + 27 * d ^ 2 = 4 * n ^ 3) : 2 ∣ J + 3 * d := by
  have h2 : (2 : ℤ) ∣ J ^ 2 + 27 * d ^ 2 := ⟨2 * n ^ 3, by rw [h]; ring⟩
  rcases Int.even_or_odd J with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases Int.even_or_odd d with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact ⟨x + 3 * y, by ring⟩
  · obtain ⟨z, hz⟩ := h2
    have e : 2 * (2 * x ^ 2 + 54 * y ^ 2 + 54 * y + 13) + 1 = 2 * z := by linear_combination hz
    generalize 2 * x ^ 2 + 54 * y ^ 2 + 54 * y + 13 = t at e; omega
  · obtain ⟨z, hz⟩ := h2
    have e : 2 * (2 * x ^ 2 + 2 * x + 54 * y ^ 2) + 1 = 2 * z := by linear_combination hz
    generalize 2 * x ^ 2 + 2 * x + 54 * y ^ 2 = t at e; omega
  · exact ⟨x + 3 * y + 2, by ring⟩

theorem mapsTo_toBox (H : ℝ) : Set.MapsTo toBox (pairs H) (boxSq H) := by
  rintro ⟨s, n, A, B⟩ ⟨hn, hN, h3B, hB0, hsn, hJ, h1, h2, h3⟩
  dsimp only at hn hN h3B hB0 hsn hJ h1 h2 h3
  obtain ⟨b, hb⟩ : (3 : ℤ) ∣ s ^ 2 - n := (Int.ModEq.dvd hsn.symm)
  obtain ⟨c, hc⟩ : (27 : ℤ) ∣ 3 * s * n - s ^ 3 - (2 * A - B) := Int.ModEq.dvd hJ
  obtain ⟨d, rfl⟩ := h3B
  simp only [toBox]
  rw [hb, hc, Int.mul_ediv_cancel_left _ (by norm_num), Int.mul_ediv_cancel_left _ (by norm_num),
    Int.mul_ediv_cancel_left _ (by norm_num)]
  refine ⟨by push_cast; rwa [abs_neg], ?_, ?_, by rintro rfl; simp at hB0, ?_⟩
  · have : (|((3 * b : ℤ) : ℝ)|) ≤ 3 * H := by rw [← hb]; exact_mod_cast h2
    push_cast at this; rw [abs_mul] at this; norm_num at this; linarith
  · have : (|((27 * c : ℤ) : ℝ)|) ≤ 27 * H := by rw [← hc]; exact_mod_cast h3
    push_cast at this; rw [abs_mul] at this; norm_num at this; linarith
  · -- `27 disc = 4n³ - J² = 3 (3d)² = 27 d²`
    show disc (-s) b c = d ^ 2
    have hd := disc_eq (-s) b c
    have hn' : (-s) ^ 2 - 3 * b = n := by linarith
    rw [hn'] at hd
    have hJ' : 3 * (- -s) * n - (- -s) ^ 3 - 27 * c = 2 * A - 3 * d := by
      rw [neg_neg]; linarith
    rw [hJ'] at hd
    have hnorm := norm_identity A (3 * d)
    rw [hN] at hnorm
    linarith

theorem ofBox_facts {a₂ a₁ a₀ d : ℤ} (hd : disc a₂ a₁ a₀ = d ^ 2) :
    let n := a₂ ^ 2 - 3 * a₁
    let J := 3 * (-a₂) * n - (-a₂) ^ 3 - 27 * a₀
    J ^ 2 + 27 * d ^ 2 = 4 * n ^ 3 ∧ 2 * ((J + 3 * d) / 2) = J + 3 * d := by
  intro n J
  have h := disc_eq a₂ a₁ a₀
  rw [hd] at h
  have h1 : J ^ 2 + 27 * d ^ 2 = 4 * n ^ 3 := by simp only [J, n]; linarith
  exact ⟨h1, Int.mul_ediv_cancel' (two_dvd_of h1)⟩

theorem mapsTo_ofBox (H : ℝ) : Set.MapsTo ofBox (boxSq H) (pairs H) := by
  rintro ⟨a₂, a₁, a₀, d⟩ ⟨h1, h2, h3, hd0, hd⟩
  dsimp only at h1 h2 h3 hd0 hd
  obtain ⟨hJ, hA⟩ := ofBox_facts hd
  set n := a₂ ^ 2 - 3 * a₁
  set J := 3 * (-a₂) * n - (-a₂) ^ 3 - 27 * a₀
  set A := (J + 3 * d) / 2
  simp only [ofBox]
  have hn : 0 < n := by
    by_contra hn
    push_neg at hn
    have : n ^ 3 ≤ 0 := by nlinarith [sq_nonneg n]
    have : 0 < d ^ 2 := by positivity
    nlinarith [sq_nonneg J]
  refine ⟨hn, ?_, ⟨d, rfl⟩, mul_ne_zero (by norm_num) hd0, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (2 * A) ^ 2 - 6 * d * (2 * A) + 36 * d ^ 2 = J ^ 2 + 27 * d ^ 2 := by
      rw [hA]; ring
    have h4 : 4 * (A ^ 2 - A * (3 * d) + (3 * d) ^ 2) = 4 * n ^ 3 := by linear_combination e + hJ
    exact mul_left_cancel₀ (by norm_num) h4
  · exact Int.modEq_iff_dvd.mpr ⟨-a₁, by ring⟩
  · have : 2 * A - 3 * d = J := by linarith
    rw [this]
    exact Int.modEq_iff_dvd.mpr ⟨a₀, by simp only [J]; ring⟩
  · push_cast; rwa [abs_neg]
  · have hb : |(3 * (a₁ : ℝ))| ≤ 3 * H := by rw [abs_mul]; norm_num; linarith
    convert hb using 2
    push_cast; ring
  · have hAR : 2 * (A : ℝ) = (J : ℝ) + 3 * d := by exact_mod_cast hA
    have hc : |(27 * (a₀ : ℝ))| ≤ 27 * H := by rw [abs_mul]; norm_num; linarith
    convert hc using 2
    have hJR : (J : ℝ) = 3 * (-(a₂ : ℝ)) * ((a₂ : ℝ) ^ 2 - 3 * a₁) - (-(a₂ : ℝ)) ^ 3 - 27 * a₀ := by
      simp only [J, n]; push_cast; ring
    push_cast
    linear_combination (-1 : ℝ) * hAR - hJR

theorem toBox_ofBox {H : ℝ} {y : ℤ × ℤ × ℤ × ℤ} (hy : y ∈ boxSq H) : toBox (ofBox y) = y := by
  obtain ⟨a₂, a₁, a₀, d⟩ := y
  obtain ⟨-, -, -, -, hd⟩ := hy
  obtain ⟨-, hA⟩ := ofBox_facts hd
  simp only [toBox, ofBox, neg_neg, Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · rw [show (-a₂) ^ 2 - (a₂ ^ 2 - 3 * a₁) = 3 * a₁ by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  · dsimp only at hA
    generalize (3 * -a₂ * (a₂ ^ 2 - 3 * a₁) - (-a₂) ^ 3 - 27 * a₀ + 3 * d) / 2 = q at hA ⊢
    rw [show 3 * -a₂ * (a₂ ^ 2 - 3 * a₁) - (-a₂) ^ 3 - (2 * q - 3 * d) = 27 * a₀ by
      linear_combination (-1 : ℤ) * hA, Int.mul_ediv_cancel_left _ (by norm_num)]
  · exact Int.mul_ediv_cancel_left _ (by norm_num)

theorem ofBox_toBox {H : ℝ} {x : ℤ × ℤ × ℤ × ℤ} (hx : x ∈ pairs H) : ofBox (toBox x) = x := by
  obtain ⟨s, n, A, B⟩ := x
  obtain ⟨-, -, h3B, -, hsn, hJ, -⟩ := hx
  dsimp only at h3B hsn hJ
  obtain ⟨b, hb⟩ : (3 : ℤ) ∣ s ^ 2 - n := Int.ModEq.dvd hsn.symm
  obtain ⟨c, hc⟩ : (27 : ℤ) ∣ 3 * s * n - s ^ 3 - (2 * A - B) := Int.ModEq.dvd hJ
  obtain ⟨d, rfl⟩ := h3B
  simp only [toBox, ofBox]
  rw [hb, hc, Int.mul_ediv_cancel_left _ (by norm_num), Int.mul_ediv_cancel_left _ (by norm_num),
    Int.mul_ediv_cancel_left _ (by norm_num)]
  have hn : (-s) ^ 2 - 3 * b = n := by linarith
  simp only [neg_neg, hn, Prod.mk.injEq]
  refine ⟨trivial, trivial, ?_, trivial⟩
  rw [show 3 * s * n - s ^ 3 - 27 * c + 3 * d = 2 * A by linarith]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

theorem bijOn_toBox (H : ℝ) : Set.BijOn toBox (pairs H) (boxSq H) :=
  Set.InvOn.bijOn ⟨fun _ hx => ofBox_toBox hx, fun _ hy => toBox_ofBox hy⟩
    (mapsTo_toBox H) (mapsTo_ofBox H)

theorem card_pairs (H : ℝ) : Nat.card (pairs H) = Nat.card (boxSq H) :=
  Nat.card_congr (bijOn_toBox H).equiv

end Cubic.BoxAsymptotic.Parametrization
