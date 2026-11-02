import Cubic.BoxAsymptotic.WeightedAngularSieve
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! From pointwise approximate-functional-equation weight estimates to the
endpoint-plus-total-variation bounds in Abel summation.  These are proved
inequalities; they are not included in a literature hypothesis.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeWeightVariation

open MeasureTheory

theorem small_derivative {w : ℝ → ℂ} {x Q C : ℝ} (hx : 0 < x) (hQ : 0 < Q)
    (h : x * ‖deriv w x‖ ≤ C * (x / Q) ^ (1 / 4 : ℝ)) :
    ‖deriv w x‖ ≤ C * Q ^ (-(1 / 4 : ℝ)) * x ^ (-(3 / 4 : ℝ)) := by
  have hd := (le_div_iff₀ hx).mpr (by simpa only [mul_comm x] using h)
  convert hd using 1
  rw [Real.div_rpow hx.le hQ.le, Real.rpow_neg hQ.le,
    show -(3 / 4 : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub_one hx.ne']
  ring

theorem integral_small_power {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ x in Set.Ioc 1 Y, x ^ (-(3 / 4 : ℝ))) = 4 * (Y ^ (1 / 4 : ℝ) - 1) := by
  rw [← intervalIntegral.integral_of_le hY,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ)))]
  norm_num
  ring

theorem initial_variation {w : ℝ → ℂ} {Y Q C : ℝ}
    (hY : 1 ≤ Y) (hYQ : Y ≤ Q) (hC : 0 ≤ C)
    (hwi : IntegrableOn (deriv w) (Set.Icc 1 Y))
    (hw : ‖w Y - 1‖ ≤ C * (Y / Q) ^ (1 / 4 : ℝ))
    (hd : ∀ x ∈ Set.Ioc 1 Y, x * ‖deriv w x‖ ≤ C * (x / Q) ^ (1 / 4 : ℝ)) :
    ‖w Y‖ + ∫ x in Set.Ioc 1 Y, ‖deriv w x‖ ≤ 1 + 5 * C := by
  have hQ : 0 < Q := by linarith
  have hY0 : 0 < Y := by linarith
  have hep : ‖w Y‖ ≤ 1 + C := by
    have hratio : (Y / Q) ^ (1 / 4 : ℝ) ≤ 1 := by
      exact Real.rpow_le_one (div_nonneg hY0.le hQ.le)
        ((div_le_one hQ).mpr hYQ) (by norm_num)
    have hn := norm_add_le (w Y - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at hn
    nlinarith [mul_le_mul_of_nonneg_left hratio hC]
  have hpow : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Set.Ioc 1 Y) :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))).1
  have hi : (∫ x in Set.Ioc 1 Y, ‖deriv w x‖) ≤
      C * Q ^ (-(1 / 4 : ℝ)) * (4 * (Y ^ (1 / 4 : ℝ) - 1)) := by
    calc
      _ ≤ ∫ x in Set.Ioc 1 Y, C * Q ^ (-(1 / 4 : ℝ)) * x ^ (-(3 / 4 : ℝ)) := by
        apply setIntegral_mono_on (hwi.mono_set Set.Ioc_subset_Icc_self).norm
          (hpow.const_mul _) measurableSet_Ioc
        intro x hx
        exact small_derivative (by linarith [hx.1]) hQ (hd x hx)
      _ = _ := by rw [integral_const_mul, integral_small_power hY]
  have hp : Q ^ (-(1 / 4 : ℝ)) * Y ^ (1 / 4 : ℝ) ≤ 1 := by
    calc
      _ ≤ Q ^ (-(1 / 4 : ℝ)) * Q ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY0.le hYQ (by norm_num)) (by positivity)
      _ = 1 := by rw [← Real.rpow_add hQ]; norm_num
  have hn : 0 ≤ Q ^ (-(1 / 4 : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hp hC, mul_nonneg hC hn]

theorem interval_variation {w : ℝ → ℂ} {X V : ℝ} (hX : 0 < X)
    (hwi : IntegrableOn (deriv w) (Set.Icc X (2 * X)))
    (hw : ∀ x ∈ Set.Icc X (2 * X), ‖w x‖ ≤ V)
    (hd : ∀ x ∈ Set.Icc X (2 * X), x * ‖deriv w x‖ ≤ V) :
    ‖w (2 * X)‖ + ‖w X‖ + ∫ x in Set.Ioc X (2 * X), ‖deriv w x‖ ≤ 3 * V := by
  have hXX : X ≤ 2 * X := by linarith
  have hi : (∫ x in Set.Ioc X (2 * X), ‖deriv w x‖) ≤ V := by
    calc
      _ ≤ ∫ _x in Set.Ioc X (2 * X), V / X := by
        apply setIntegral_mono_on (hwi.mono_set Set.Ioc_subset_Icc_self).norm
          (integrableOn_const (measure_Ioc_lt_top.ne)) measurableSet_Ioc
        intro x hx
        have hxc : x ∈ Set.Icc X (2 * X) := Set.Ioc_subset_Icc_self hx
        apply (le_div_iff₀ hX).mpr
        calc
          ‖deriv w x‖ * X ≤ ‖deriv w x‖ * x :=
            mul_le_mul_of_nonneg_left hxc.1 (norm_nonneg _)
          _ ≤ V := by simpa only [mul_comm x] using hd x hxc
      _ = V := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hXX, smul_eq_mul]
        field_simp
        ring
  linarith [hw (2 * X) ⟨hXX, le_rfl⟩, hw X ⟨le_rfl, hXX⟩]

theorem dyadic_decay {Q Y x : ℝ} (j : ℕ) (hY : 0 < Y) (hQ : 0 ≤ Q)
    (hQY : Q ≤ 3 * Y) (hx : (2 : ℝ) ^ j * Y / 2 ≤ x) :
    (Q / x) ^ 3 ≤ 216 * (1 / 8 : ℝ) ^ j := by
  have htwo : (0 : ℝ) < 2 ^ j := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hr : Q / x ≤ 6 / (2 : ℝ) ^ j := by
    apply (div_le_div_iff₀ hx0 htwo).mpr
    nlinarith [mul_le_mul_of_nonneg_right hQY htwo.le]
  have hc := pow_le_pow_left₀ (div_nonneg hQ hx0.le) hr 3
  have hp : ((2 : ℝ) ^ j) ^ 3 = (8 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm j 3, pow_mul]
    norm_num
  conv_rhs at hc => rw [div_pow, hp]
  norm_num only [show (6 : ℝ) ^ 3 = 216 by norm_num] at hc
  simpa only [one_div, div_eq_mul_inv, one_mul, inv_pow] using hc

theorem dyadic_variation {w : ℝ → ℂ} {Q Y C : ℝ} (j : ℕ)
    (hY : 0 < Y) (hQ : 0 ≤ Q) (hQY : Q ≤ 3 * Y) (hC : 0 ≤ C)
    (hwi : IntegrableOn (deriv w) (Set.Icc ((2 : ℝ) ^ j * Y / 2) ((2 : ℝ) ^ j * Y)))
    (hw : ∀ x > 0, ‖w x‖ ≤ C * (Q / x) ^ 3)
    (hd : ∀ x > 0, x * ‖deriv w x‖ ≤ C * (Q / x) ^ 3) :
    ‖w ((2 : ℝ) ^ j * Y)‖ + ‖w ((2 : ℝ) ^ j * Y / 2)‖ +
        ∫ x in Set.Ioc ((2 : ℝ) ^ j * Y / 2) ((2 : ℝ) ^ j * Y), ‖deriv w x‖ ≤
      648 * C * (1 / 8 : ℝ) ^ j := by
  have hX : 0 < (2 : ℝ) ^ j * Y / 2 := by positivity
  have he : 2 * ((2 : ℝ) ^ j * Y / 2) = (2 : ℝ) ^ j * Y := by ring
  have hb (x : ℝ) (hx : (2 : ℝ) ^ j * Y / 2 ≤ x) :
      C * (Q / x) ^ 3 ≤ C * (216 * (1 / 8 : ℝ) ^ j) :=
    mul_le_mul_of_nonneg_left (dyadic_decay j hY hQ hQY hx) hC
  have h := interval_variation hX (by simpa only [he] using hwi)
    (fun x hx => (hw x (hX.trans_le hx.1)).trans (hb x hx.1))
    (fun x hx => (hd x (hX.trans_le hx.1)).trans (hb x hx.1))
  rw [he] at h
  convert h using 1
  ring

end Cubic.BoxAsymptotic.HeckeWeightVariation
