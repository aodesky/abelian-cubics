import Cubic.BoxAsymptotic.SmoothModeBounds
import Cubic.BoxAsymptotic.SmoothFiniteModeBound
import Cubic.BoxAsymptotic.SmoothFrequencySum

/-! Summing the shifted mode integrals. The constants and derivative order are
chosen before the weight, radial scale, angular scale, center, and contour. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothUniformEstimate

open Complex MeasureTheory Set
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothShiftedExpansion Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothWeightData Cubic.BoxAsymptotic.AngularMomentData
open Cubic.Analysis.MellinDirichletPairing
open scoped ContDiff

theorem estimate (hHecke : PrimitiveHecke.BlackBox)
    (hmoment : AngularMomentClaim) :
    ∃ A J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (X Θ θ₀ M η D : ℝ) (w : ℝ × ℝ → ℝ),
        1 ≤ X → 0 < Θ → Θ ≤ 1 → 0 ≤ M → 0 < η → η ≤ 1 / 4 →
        1 ≤ D → 1 ≤ D * Θ → 1 ≤ Real.log (2 * D) →
        ContDiff ℝ ∞ w →
        (∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ)) →
        Function.support w ⊆
          {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ} →
        normalizedDerivativeBound w Θ M J →
        |(∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (fun θ => w (n, θ))) -
          ∫ n in Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi,
            w (n, θ) * (aStar * Real.log n + ZeroModeData.b₀) / (2 * Real.pi)| ≤
          C * M * X ^ (1 / 2 + η) * η⁻¹ ^ 4 * Real.log (2 * D) ^ A := by
  obtain ⟨A, Cm, hCm, hm⟩ := SmoothModeBounds.first_moment hHecke hmoment
  obtain ⟨Cs, hCs, N, hg⟩ := SmoothModeBounds.small_growth hHecke
  let j := 2 * A + N + 2
  let B : ℝ := (60 / Real.pi) * 4 ^ j
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A, 2 * j, B * (Cs + 2 * Cm), by positivity, ?_⟩
  intro X Θ θ₀ M η D w hX hΘ hΘ' hM hη hη' hD hDΘ hL hw hp hs hb
  let g : ℤ → ℂ := fun k => pairing (1 / 2 + η) (mode hHecke k) (transform w k)
  let W := B * M * X ^ (1 / 2 + η)
  let Q := W * Cm * η⁻¹ ^ 4 * Real.log (2 * D) ^ A
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsmall : (∑ k ∈ Finset.Icc (-2 : ℤ) 2, ‖g k‖) ≤ W * Cs * η⁻¹ ^ 4 :=
    SmoothFiniteModeBound.pairing_bound _ hw (by linarith) hΘ hΘ' hM hη hη' hCs.le
      hp hs hb (by dsimp [j]; omega)
      (fun k _ => SmoothModeBounds.continuous_on_left hHecke k hη hη') (hg η hη hη')
  have hband (r : ℕ) :
      (∑ k ∈ signedModes ((2 : ℝ) ^ (r + 1)), ‖g k‖) ≤
        Q * SmoothDyadicKernel.term (2 * Θ) r := by
    have hK : (2 : ℝ) ≤ 2 ^ (r + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (show 1 ≤ r + 1 by omega)
    have h := SmoothMomentBound.block_pairing hw (by linarith) hΘ hM hK hη hη' hCm.le
      hD hDΘ hL hp hs hb (by dsimp [j]; omega)
      (fun k _ => SmoothModeBounds.continuous_on_left hHecke k hη hη')
      (fun t => hm _ t η hK hη hη')
    refine h.trans_eq ?_
    dsimp [Q, W, B, SmoothDyadicKernel.term]
    rw [pow_succ]
    congr 1
    congr 1 <;> ring
  have htotal := SmoothFrequencySum.total_bound (fun k => norm_nonneg (g k))
    hQ (by positivity : 0 ≤ 2 * Θ) hband
  have hpow : 1 ≤ Real.log (2 * D) ^ A := one_le_pow₀ hL
  have hsum : (∑' k : ℤ, ‖g k‖) ≤
      (B * (Cs + 2 * Cm)) * M * X ^ (1 / 2 + η) * η⁻¹ ^ 4 * Real.log (2 * D) ^ A := by
    calc
      _ ≤ (∑ k ∈ Finset.Icc (-2 : ℤ) 2, ‖g k‖) + 2 * Q := by
        simpa only [SmoothFrequencySum.cutoff, Nat.zero_add, pow_one] using htotal
      _ ≤ W * Cs * η⁻¹ ^ 4 + 2 * Q := by linarith
      _ ≤ W * Cs * η⁻¹ ^ 4 * Real.log (2 * D) ^ A + 2 * Q := by
        have hh := le_mul_of_one_le_right (by positivity : 0 ≤ W * Cs * η⁻¹ ^ 4) hpow
        linarith
      _ = _ := by dsimp [Q, W]; ring
  have hexp := shifted_expansion hHecke hw hX hΘ hM hη hη' hp hs
    (hb.mono (by dsimp [j]; omega))
  have heq := hexp.tsum_eq
  have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  rw [SmoothZeroResidue.residue, SmoothZeroResidue.residue_integral hw.continuous
    (by linarith : 0 < X / 2) hrad] at heq
  have hnorm := norm_tsum_le_tsum_norm hexp.summable.norm
  rw [heq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact hnorm.trans hsum

end Cubic.BoxAsymptotic.SmoothUniformEstimate
