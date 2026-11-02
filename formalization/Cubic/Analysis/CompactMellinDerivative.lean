import Cubic.Analysis.CompactMellin
import Cubic.Counting.QuadraticLIncrementBound
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Integration by parts for the radial operator `x d/dx` in the actual Mellin
integral. Compact support away from zero removes both boundary terms. -/

noncomputable section

namespace Cubic.Analysis.CompactMellin

open Set MeasureTheory Complex

variable {f : ℝ → ℂ} {a b A B : ℝ}

theorem eq_interval (ha : 0 < a) (hs : Function.support f ⊆ Icc a b)
    (hA : A < a) (hB : b ≤ B) (s : ℂ) :
    mellin f s = ∫ x in A..B, (x : ℂ) ^ (s - 1) * f x := by
  have hi : Function.support (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x) ⊆ Ioi 0 := by
    intro x hx
    have hn : f x ≠ 0 := fun h => hx (by simp [h])
    exact ha.trans_le (hs hn).1
  have hs' : Function.support (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x) ⊆ Ioc A B := by
    intro x hx
    have hn : f x ≠ 0 := fun h => hx (by simp [h])
    exact ⟨hA.trans_le (hs hn).1, (hs hn).2.trans hB⟩
  rw [mellin]
  simp only [smul_eq_mul]
  rw [← integral_indicator measurableSet_Ioi, indicator_eq_self.mpr hi,
    intervalIntegral.integral_eq_integral_of_support_subset hs']

theorem deriv_support (hs : Function.support f ⊆ Icc a b) :
    Function.support (deriv f) ⊆ Icc a b :=
  support_deriv_subset.trans (closure_minimal hs isClosed_Icc)

theorem radial_support (hs : Function.support f ⊆ Icc a b) :
    Function.support (fun x : ℝ => (x : ℂ) * deriv f x) ⊆ Icc a b := by
  intro x hx
  apply deriv_support hs
  intro hn
  exact hx (by simp [hn])

theorem radial_identity (hf : Differentiable ℝ f) (hdf : Continuous (deriv f))
    (ha : 0 < a) (hab : a ≤ b) (hs : Function.support f ⊆ Icc a b) (s : ℂ) :
    mellin (fun x : ℝ => (x : ℂ) * deriv f x) s = -s * mellin f s := by
  let A := a / 2
  let B := b + 1
  have hAa : A < a := by dsimp [A]; linarith
  have hbB : b < B := by dsimp [B]; linarith
  have hAB : A ≤ B := by linarith
  have hpos : ∀ x ∈ Set.uIcc A B, 0 < x := by
    intro x hx
    rw [uIcc_of_le hAB] at hx
    dsimp [A] at hx
    linarith [hx.1]
  have hpow (z : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ) ^ z) (Set.uIcc A B) := by
    intro x hx
    exact (Cubic.Counting.QuadraticLIncrementBound.power_derivative z x
      (hpos x hx)).continuousAt.continuousWithinAt
  have h := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ => (hf x).hasDerivAt)
    (fun x hx => Cubic.Counting.QuadraticLIncrementBound.power_derivative s x (hpos x hx))
    (hdf.intervalIntegrable A B)
    ((continuousOn_const.mul (hpow (s - 1))).intervalIntegrable)
  have hfa : f A = 0 := zero_outside hs (fun h => not_lt_of_ge h.1 hAa)
  have hfb : f B = 0 := zero_outside hs (fun h => not_lt_of_ge h.2 hbB)
  rw [hfa, hfb, zero_mul, zero_mul, sub_self] at h
  have hI₁ : IntervalIntegrable (fun x : ℝ => deriv f x * (x : ℂ) ^ s) volume A B :=
    (hdf.continuousOn.mul (hpow s)).intervalIntegrable
  have hI₂ : IntervalIntegrable (fun x : ℝ => f x * (s * (x : ℂ) ^ (s - 1))) volume A B :=
    (hf.continuous.continuousOn.mul (continuousOn_const.mul (hpow (s - 1)))).intervalIntegrable
  rw [intervalIntegral.integral_add hI₁ hI₂] at h
  have hsecond : (∫ x in A..B, f x * (s * (x : ℂ) ^ (s - 1))) = s * mellin f s := by
    rw [eq_interval ha hs hAa hbB.le, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hsecond] at h
  have hfirst : mellin (fun x : ℝ => (x : ℂ) * deriv f x) s =
      ∫ x in A..B, deriv f x * (x : ℂ) ^ s := by
    rw [eq_interval ha (radial_support hs) hAa hbB.le]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hpos x hx).ne'
    have he : (x : ℂ) ^ (s - 1) * (x : ℂ) = (x : ℂ) ^ s := by
      calc
        _ = (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (1 : ℂ) := by rw [cpow_one]
        _ = (x : ℂ) ^ (s - 1 + 1) := (cpow_add _ _ hx0).symm
        _ = _ := by rw [sub_add_cancel]
    dsimp only
    rw [← mul_assoc, he, mul_comm]
  rw [hfirst]
  have he := eq_neg_of_add_eq_zero_left h
  simpa only [neg_mul] using he

end Cubic.Analysis.CompactMellin
