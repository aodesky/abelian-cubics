import Cubic.BoxAsymptotic.AngularStripGrowth
import Cubic.BoxAsymptotic.ZeroModeData

/-! Holomorphy and polynomial growth of the zero angular mode away from its
double pole. The correction product is the frequency-zero instance of the
same product used in the nonzero modes, retaining the uniform `η⁻⁴` bound. -/

noncomputable section

namespace Cubic.BoxAsymptotic.ZeroModeStripGrowth

open Complex
open Cubic.PoissonSummation
open Cubic.BoxAsymptotic.ZeroModeData

theorem splitPhase_zero (p : FiniteEulerProduct.SplitPrimes) :
    AngularCorrectionProduct.splitPhase 0 p = 1 := by
  have hp : ¬ 3 ∣ Ideal.absNorm (AngularCorrectionProduct.splitPrime p) := by
    rw [AngularCorrectionProduct.norm_splitPrime]
    intro h
    have := Nat.mod_eq_zero_of_dvd h
    have := p.2
    omega
  simp [AngularCorrectionProduct.splitPhase, AngularIdealData.psi, hp,
    AngularSeriesData.phase]

theorem correction_zero (s : ℂ) :
    AngularCorrectionProduct.value 0 s = HeightZetaCorrectionProduct.value s := by
  unfold AngularCorrectionProduct.value HeightZetaCorrectionProduct.value
  congr 1
  apply tprod_congr
  intro p
  norm_num [AngularCorrectionProduct.split, AngularCorrectionProduct.quadraticCoefficient,
    AngularCorrectionProduct.cubicCoefficient, splitPhase_zero, HeightZetaCorrectionProduct.split]

theorem local_entire : Differentiable ℂ localFactor := by
  have h (c : ℂ) : Differentiable ℂ (fun s : ℂ => (3 : ℂ) ^ (-(c * s))) :=
    (((differentiable_const c).mul differentiable_id).neg.const_cpow
      (Or.inl (by norm_num : (3 : ℂ) ≠ 0)))
  have h1 : Differentiable ℂ (fun s : ℂ => (3 : ℂ) ^ (-s)) := by simpa using h 1
  exact ((differentiable_const _).mul
    ((differentiable_const _).add ((differentiable_const _).mul (h 2)))).mul
      ((differentiable_const _).sub h1)

theorem holomorphic : DifferentiableOn ℂ continuation
    ({s : ℂ | 1 / 2 < s.re} \ {1}) := by
  refine (local_entire.differentiableOn.mul (DifferentiableOn.pow ?_ 2)).mul
    (HeightZetaCorrectionProduct.differentiableOn_value.mono (fun _ h => h.1))
  intro s hs
  exact (QuadraticZetaRegularization.differentiableAt_value s hs.2).differentiableWithinAt

theorem local_bound {s : ℂ} (hs : 0 ≤ s.re) : ‖localFactor s‖ ≤ 2 := by
  have hp : ‖(3 : ℂ) ^ (-s)‖ ≤ 1 :=
    Cubic.Analysis.ZetaStripGrowth.norm_real_cpow_neg_le_one hs 3 (by norm_num)
  have hp2 : ‖(3 : ℂ) ^ (-(2 * s))‖ ≤ 1 :=
    Cubic.Analysis.ZetaStripGrowth.norm_real_cpow_neg_le_one
      (by simpa using mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hs) 3 (by norm_num)
  have hsub : ‖1 - (3 : ℂ) ^ (-s)‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) ((3 : ℂ) ^ (-s))
    rw [norm_one] at h
    linarith
  have hadd : ‖1 + 2 * (3 : ℂ) ^ (-(2 * s))‖ ≤ 3 := by
    have h := norm_add_le (1 : ℂ) (2 * (3 : ℂ) ^ (-(2 * s)))
    norm_num only [norm_one, norm_mul, Complex.norm_ofNat] at h
    linarith
  rw [localFactor, norm_mul, norm_mul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  calc
    _ ≤ (1 / 3 : ℝ) * 3 * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hadd (by norm_num)) hsub (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem growth : ∃ C : ℝ, 0 < C ∧ ∀ (η : ℝ), 0 < η → η ≤ 1 / 4 →
    ∀ s : ℂ, 1 / 2 + η ≤ s.re → s.re ≤ 2 → 1 / 4 ≤ ‖s - 1‖ →
      ‖continuation s‖ ≤ C * η⁻¹ ^ 4 * (1 + |s.im|) ^ 8 := by
  obtain ⟨B, hB⟩ := Cubic.Analysis.ZetaStripGrowth.zetaE_growth
  let D := |B| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hBD : B ≤ D := (le_abs_self B).trans (by dsimp [D]; linarith)
  refine ⟨32 * D ^ 2 * AngularCorrectionBounds.absoluteConstant,
    by positivity [AngularCorrectionBounds.absoluteConstant_pos], ?_⟩
  intro η hη hη' s hlo hhi hdist
  have hz : ‖(s - 1) * QuadraticZetaRegularization.value s‖ ≤
      D * (1 + |s.im|) ^ 4 :=
    (hB s (by linarith) (by linarith)).trans
      (mul_le_mul_of_nonneg_right hBD (by positivity))
  rw [norm_mul] at hz
  have hz' : ‖QuadraticZetaRegularization.value s‖ ≤ 4 * D * (1 + |s.im|) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hdist (norm_nonneg (QuadraticZetaRegularization.value s))]
  have hR := AngularStripGrowth.correction_bound hη hη' 0 hlo
  rw [correction_zero] at hR
  rw [continuation, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ (2 * (4 * D * (1 + |s.im|) ^ 4) ^ 2) *
        (AngularCorrectionBounds.absoluteConstant * η⁻¹ ^ 4) :=
      mul_le_mul
        (mul_le_mul (local_bound (by linarith)) (pow_le_pow_left₀ (norm_nonneg _) hz' 2)
          (by positivity) (by norm_num)) hR (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Cubic.BoxAsymptotic.ZeroModeStripGrowth
