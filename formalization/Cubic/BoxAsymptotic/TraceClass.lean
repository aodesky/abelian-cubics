import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The admissible traces form one class modulo `3` (`lem:local3`, last assertion)

If `s₀` satisfies `eq:cong` for `β = A + Bζ` (`s₀² ≡ n (mod 3)`,
`2A - B ≡ 3s₀n - s₀³ (mod 27)`), then an integer `s` satisfies `eq:cong` exactly when
`s ≡ s₀ (mod 3)`. The draft: "replacing `s` by `s + 3` changes `3sn - s³` by
`9(n - s²) - 27s - 27`, divisible by `27` whenever `s² ≡ n (mod 3)`". For the converse,
`s² ≡ s₀² (mod 3)` gives `s ≡ ±s₀`; if `s ≡ -s₀` then `3s₀n - s₀³ ≡ -(3s₀n - s₀³)`, so
`27 ∣ 3s₀n - s₀³`, `3 ∣ s₀`, and again `s ≡ s₀`.
-/

namespace Cubic.BoxAsymptotic.TraceClass

theorem shift {n s t : ℤ} (hst : s ≡ t [ZMOD 3]) (ht : t ^ 2 ≡ n [ZMOD 3]) :
    3 * s * n - s ^ 3 ≡ 3 * t * n - t ^ 3 [ZMOD 27] := by
  obtain ⟨k, hk⟩ := hst.dvd
  obtain ⟨m, hm⟩ := ht.dvd
  have hs : s = t - 3 * k := by linarith
  have hn : n = t ^ 2 + 3 * m := by linarith
  apply Int.modEq_of_dvd
  exact ⟨k * m + t * k ^ 2 - k ^ 3, by rw [hs, hn]; ring⟩

/-- **The admissible traces form the class of `s₀` modulo `3`.** -/
theorem cong_iff {n A B s₀ s : ℤ} (h₀ : s₀ ^ 2 ≡ n [ZMOD 3])
    (h₁ : 2 * A - B ≡ 3 * s₀ * n - s₀ ^ 3 [ZMOD 27]) :
    (s ^ 2 ≡ n [ZMOD 3] ∧ 2 * A - B ≡ 3 * s * n - s ^ 3 [ZMOD 27]) ↔ s ≡ s₀ [ZMOD 3] := by
  constructor
  · rintro ⟨h2, h3⟩
    have hd : (3 : ℤ) ∣ (s - s₀) * (s + s₀) := by
      have := (h2.trans h₀.symm).dvd
      exact ⟨-(this.choose), by linear_combination -this.choose_spec⟩
    rcases (Int.prime_three.dvd_mul).mp hd with h | h
    · exact (Int.modEq_iff_dvd.mpr ⟨-(h.choose), by linear_combination -h.choose_spec⟩)
    · -- `s ≡ -s₀`
      have hneg : s ≡ -s₀ [ZMOD 3] := Int.modEq_iff_dvd.mpr ⟨-h.choose, by
        linear_combination -h.choose_spec⟩
      have hsq : (-s₀) ^ 2 ≡ n [ZMOD 3] := by rwa [neg_sq]
      have e := shift hneg hsq
      have h27 : (27 : ℤ) ∣ 2 * (3 * s₀ * n - s₀ ^ 3) := by
        have := (h₁.symm.trans (h3.trans e)).dvd
        exact ⟨-this.choose, by linear_combination -this.choose_spec⟩
      have h27' : (27 : ℤ) ∣ 3 * s₀ * n - s₀ ^ 3 := by omega
      have h3s : (3 : ℤ) ∣ s₀ ^ 3 := by
        have : (3 : ℤ) ∣ 3 * s₀ * n - s₀ ^ 3 := (dvd_trans ⟨9, by norm_num⟩ h27')
        have h' : (3 : ℤ) ∣ 3 * s₀ * n := ⟨s₀ * n, by ring⟩
        have := Int.dvd_sub h' this
        rwa [show 3 * s₀ * n - (3 * s₀ * n - s₀ ^ 3) = s₀ ^ 3 by ring] at this
      have hs₀ := Int.prime_three.dvd_of_dvd_pow h3s
      apply Int.modEq_iff_dvd.mpr
      obtain ⟨a, ha⟩ := h
      obtain ⟨b, hb⟩ := hs₀
      exact ⟨2 * b - a, by linarith⟩
  · intro h
    refine ⟨(Int.ModEq.pow 2 h).trans h₀, h₁.trans (shift h h₀).symm⟩

end Cubic.BoxAsymptotic.TraceClass
