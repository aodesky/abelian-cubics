import CubicTargets.BoxAsymptotic.Main
import Cubic.Counting.AsymptoticConstantIdentities

/-! The remaining explicit assertions in the main theorem: the Euler-product
formula for `A₃`, its positivity, and the two-sided bound implied by the error
term. These do not add analytic inputs to the asymptotic. -/

noncomputable section

namespace Cubic.BoxAsymptotic.MainConsequences

open Filter
open CubicTargets.BoxAsymptotic
open Cubic.Counting Cubic.PoissonSummation
open scoped Topology

theorem leading_positive : 0 < A3 := by
  unfold A3 GeneralMonicData.Cconst
  exact div_pos (mul_pos (by norm_num) AsymptoticConstantIdentities.original_leading_positive)
    (by positivity)

theorem leading_formula :
    A3 = 484 * Real.pi / (2187 * Real.sqrt 3) * (HeightZetaCorrectionProduct.value 1).re := by
  have hcorr : LeadingTermsData.correction 2 = (4 / 9 : ℂ) * HeightZetaCorrectionProduct.value 1 := by
    unfold LeadingTermsData.correction
    norm_num [Complex.cpow_neg_one]
  have he := AsymptoticConstantIdentities.original_leading_correction
  rw [hcorr] at he
  have hr := congrArg Complex.re he
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  unfold A3 GeneralMonicData.Cconst
  rw [hr]
  field_simp
  ring

theorem complete (h : MainClaim) : FullMainClaim := by
  refine ⟨h, leading_formula, leading_positive, ?_⟩
  obtain ⟨K, H₀, hb⟩ := h
  let C := |K| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hA := leading_positive
  have he := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).bound
    (show 0 < A3 / (2 * C) by positivity)
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.mp he
  refine ⟨A3 / 2, 3 * A3 / 2, max H₀ (max H₁ (Real.exp 1)), by positivity, by positivity, ?_⟩
  intro H hH
  have hH0 := (le_max_left H₀ _).trans hH
  have hH1 := (le_max_left H₁ (Real.exp 1)).trans ((le_max_right H₀ _).trans hH)
  have hHe := (le_max_right H₁ (Real.exp 1)).trans ((le_max_right H₀ _).trans hH)
  have hHpos : 0 < H := (Real.exp_pos _).trans_le hHe
  have hL : 1 ≤ Real.log H := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hHe
  have hLL : 0 ≤ Real.log (Real.log H) := Real.log_nonneg hL
  have hh := hH₁ H hH1
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs,
    abs_of_nonneg hLL, abs_of_nonneg (by linarith : 0 ≤ Real.log H)] at hh
  have hsmall : C * Real.log (Real.log H) ≤ A3 / 2 * Real.log H := by
    have hm := mul_le_mul_of_nonneg_left hh hC.le
    convert hm using 1
    field_simp
  have hK : K ≤ C := by dsimp [C]; linarith [le_abs_self K]
  have herr : K * H * Real.log H ^ 2 * Real.log (Real.log H) ≤
      A3 / 2 * H * Real.log H ^ 3 := by
    calc
      _ ≤ C * H * Real.log H ^ 2 * Real.log (Real.log H) := by gcongr
      _ = (H * Real.log H ^ 2) * (C * Real.log (Real.log H)) := by ring
      _ ≤ (H * Real.log H ^ 2) * (A3 / 2 * Real.log H) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by ring
  have hh := abs_le.mp ((hb H hH0).trans herr)
  constructor <;> linarith

end Cubic.BoxAsymptotic.MainConsequences
