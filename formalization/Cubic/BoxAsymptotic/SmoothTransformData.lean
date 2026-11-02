import Cubic.BoxAsymptotic.AngularSeriesData
import Cubic.Analysis.CompactMellin

/-! The Fourier--Mellin transform used in `lem:smooth`. Angular coefficients
use the negative character, so Fourier reconstruction pairs them with the
paper's positive-character series `F_k`. The Mellin measure is `x^(s-1) dx`. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothTransformData

open MeasureTheory Set Complex
open Cubic.BoxAsymptotic.AngularSeriesData

/-- The angular Fourier coefficient with normalized angular measure. -/
def angularCoefficient (w : ℝ × ℝ → ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ *
    ∫ θ in (0 : ℝ)..2 * Real.pi, (w (x, θ) : ℂ) * character (-k) θ

/-- The actual integral defining the test-weight transform. -/
def transform (w : ℝ × ℝ → ℝ) (k : ℤ) (s : ℂ) : ℂ :=
  mellin (angularCoefficient w k) s

theorem continuous_character (k : ℤ) : Continuous (character k) := by
  change Continuous (fun θ => character k θ)
  simp_rw [character_eq_exp]
  fun_prop

theorem angularCoefficient_continuous {w : ℝ × ℝ → ℝ} (hw : Continuous w) (k : ℤ) :
    Continuous (angularCoefficient w k) := by
  have hc : Continuous (fun p : ℝ × ℝ => (w p : ℂ) * character (-k) p.2) :=
    (Complex.continuous_ofReal.comp hw).mul ((continuous_character _).comp continuous_snd)
  have h : Continuous (fun x : ℝ =>
      ∫ θ in Icc (0 : ℝ) (2 * Real.pi), (w (x, θ) : ℂ) * character (-k) θ) :=
    continuous_parametric_integral_of_continuous
      (f := fun x θ => (w (x, θ) : ℂ) * character (-k) θ) hc isCompact_Icc
  have he : ∀ x : ℝ,
      (∫ θ in (0 : ℝ)..2 * Real.pi, (w (x, θ) : ℂ) * character (-k) θ) =
      ∫ θ in Icc (0 : ℝ) (2 * Real.pi), (w (x, θ) : ℂ) * character (-k) θ := by
    intro x
    rw [intervalIntegral.integral_of_le (by positivity), integral_Icc_eq_integral_Ioc]
  change Continuous (fun x => (2 * Real.pi : ℂ)⁻¹ *
    ∫ θ in (0 : ℝ)..2 * Real.pi, (w (x, θ) : ℂ) * character (-k) θ)
  simp_rw [he]
  exact continuous_const.mul h

theorem angularCoefficient_support {w : ℝ × ℝ → ℝ} {a b : ℝ}
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b}) (k : ℤ) :
    Function.support (angularCoefficient w k) ⊆ Icc a b := by
  intro x hx
  by_contra hn
  have hw : ∀ θ, w (x, θ) = 0 := by
    intro θ
    by_contra h
    exact hn (hs h)
  exact hx (by simp [angularCoefficient, hw])

theorem transform_convergent {w : ℝ × ℝ → ℝ} {a b : ℝ}
    (hw : Continuous w) (ha : 0 < a)
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b}) (k : ℤ) (s : ℂ) :
    MellinConvergent (angularCoefficient w k) s :=
  Cubic.Analysis.CompactMellin.convergent (angularCoefficient_continuous hw k)
    ha (angularCoefficient_support hs k) s

theorem transform_entire {w : ℝ × ℝ → ℝ} {a b : ℝ}
    (hw : Continuous w) (ha : 0 < a)
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b}) (k : ℤ) :
    Differentiable ℂ (transform w k) :=
  Cubic.Analysis.CompactMellin.entire (angularCoefficient_continuous hw k)
    ha (angularCoefficient_support hs k)

theorem transform_hasDerivAt {w : ℝ × ℝ → ℝ} {a b : ℝ}
    (hw : Continuous w) (ha : 0 < a)
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b}) (k : ℤ) (s : ℂ) :
    HasDerivAt (transform w k)
      (mellin (fun x => Real.log x • angularCoefficient w k x) s) s :=
  Cubic.Analysis.CompactMellin.hasDerivAt (angularCoefficient_continuous hw k)
    ha (angularCoefficient_support hs k) s

end Cubic.BoxAsymptotic.SmoothTransformData
