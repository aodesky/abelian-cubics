import Cubic.BoxAsymptotic.SmoothContourDecay
import Cubic.BoxAsymptotic.ZeroModeStripGrowth
import Cubic.BoxAsymptotic.SmoothZeroResidue

/-! Shifting the actual weighted modes from `Re s = 2` to `Re s = 1/2+η`.
Each integral is absolutely convergent. Only the zero mode has a residue. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothContourShift

open Complex MeasureTheory Set Filter
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.Analysis.MellinDirichletPairing
open Cubic.Analysis.VerticalContourShift
open Cubic.PoissonSummation.RectangleResidue
open scoped ContDiff Topology Interval

theorem shift_of_rectangles {w : ℝ × ℝ → ℝ} {X Θ θ₀ β C : ℝ}
    {F : ℂ → ℂ} {N : ℕ} {R : ℂ}
    (hw : ContDiff ℝ ∞ w) (hX : 1 ≤ X) (hΘ : 0 < Θ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 2) (hC : 0 ≤ C)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hF : ∀ s : ℂ, β ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖F s‖ ≤ C * (1 + |s.im|) ^ N)
    (hleft : Continuous (fun t : ℝ => F (β + t * I)))
    (hright : Continuous (fun t : ℝ => F (2 + t * I)))
    (k : ℤ)
    (hrect : ∀ T : ℝ, 0 < T →
      RectangleIntegral (fun s => F s * transform w k s)
        ((β : ℂ) - T * I) ((2 : ℂ) + T * I) = 2 * Real.pi * I * R) :
    pairing 2 F (transform w k) = R + pairing β F (transform w k) := by
  obtain ⟨B, hB, hb⟩ := SmoothContourDecay.product_decay hw hX hΘ hβ hC hp hs hF k
  have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  have hT := (transform_entire hw.continuous (by linarith : 0 < X / 2) hrad k).continuous
  have hline (σ : ℝ) (hσ : β ≤ σ) (hσ' : σ ≤ 2)
      (hcont : Continuous (fun t : ℝ => F (σ + t * I))) :
      VerticalIntegrable (fun s => F s * transform w k s) σ := by
    apply SmoothContourDecay.integrable_of_tall_decay
      (hcont.mul (hT.comp (by fun_prop))) hB
    intro t ht
    simpa using hb (σ + t * I) (by simpa using hσ) (by simpa using hσ') (by simpa using ht)
  have hhor (ε : ℝ) (hε : |ε| = 1) := horizontal_vanishes (C := B) hβ'
    (f := fun s => F s * transform w k s)
    (fun x hx t ht => by
      simpa using hb (x + t * I) (by simpa using hx.1)
        (by simpa using hx.2) (by simpa using ht)) ε hε
  apply normalized_shift
  apply Cubic.Analysis.VerticalContourShift.shift_of_rectangles
    (hline β le_rfl hβ' hleft) (hline 2 hβ' le_rfl hright) _ _ hrect
  · simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul]
      using hhor (-1) (by norm_num)
  · simpa only [Complex.ofReal_one, one_mul] using hhor 1 (by norm_num)

theorem rectangle_subset {β : ℝ} (hβ : 1 / 2 < β) (hβ' : β ≤ 2) (T : ℝ) :
    Rectangle ((β : ℂ) - T * I) ((2 : ℂ) + T * I) ⊆ {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hre : s.re ∈ Icc β 2 := by simpa [uIcc_of_le hβ'] using hs.1
  exact hβ.trans_le hre.1

theorem nonzero
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    {w : ℝ × ℝ → ℝ} {X Θ θ₀ η : ℝ}
    (hw : ContDiff ℝ ∞ w) (hX : 1 ≤ X) (hΘ : 0 < Θ)
    (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (k : ℤ) (hk : k ≠ 0) :
    pairing 2 (HeckeAnalyticRealization.angularF hHecke k) (transform w k) =
      pairing (1 / 2 + η) (HeckeAnalyticRealization.angularF hHecke k) (transform w k) := by
  have hF := HeckeAnalyticRealization.angular_holomorphic hHecke hk
  have hline (σ : ℝ) (hσ : 1 / 2 < σ) :
      Continuous (fun t : ℝ => HeckeAnalyticRealization.angularF hHecke k (σ + t * I)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (by intro t; simpa using hσ)
  obtain ⟨C, hC, N, hN⟩ := AngularStripGrowth.angular_growth hHecke k hk
  have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  have hT := transform_entire hw.continuous (by linarith : 0 < X / 2) hrad k
  have hh := shift_of_rectangles (R := 0) hw hX hΘ (by linarith) (by linarith)
    (show 0 ≤ C * η⁻¹ ^ 4 by positivity) hp hs
    (fun s hlo hhi _ => hN η hη hη' s hlo hhi)
    (hline (1 / 2 + η) (by linarith)) (hline 2 (by norm_num)) k (fun T _ => by
      rw [mul_zero]
      exact HolomorphicOn.vanishesOnRectangle (hF.mul hT.differentiableOn)
        (rectangle_subset (by linarith) (by linarith) T))
  simpa only [zero_add] using hh

theorem zero
    {w : ℝ × ℝ → ℝ} {X Θ θ₀ η : ℝ}
    (hw : ContDiff ℝ ∞ w) (hX : 1 ≤ X) (hΘ : 0 < Θ)
    (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ}) :
    pairing 2 ZeroModeData.continuation (transform w 0) = SmoothZeroResidue.residue w +
      pairing (1 / 2 + η) ZeroModeData.continuation (transform w 0) := by
  have hF := ZeroModeStripGrowth.holomorphic
  have hline (σ : ℝ) (hσ : 1 / 2 < σ) (hσ' : σ ≠ 1) :
      Continuous (fun t : ℝ => ZeroModeData.continuation (σ + t * I)) := by
    apply hF.continuousOn.comp_continuous (by fun_prop)
    intro t
    refine ⟨by simpa using hσ, ?_⟩
    intro he
    apply hσ'
    have hre := congrArg Complex.re he
    simpa using hre
  obtain ⟨C, hC, hB⟩ := ZeroModeStripGrowth.growth
  have hg : ∀ s : ℂ, 1 / 2 + η ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖ZeroModeData.continuation s‖ ≤ (C * η⁻¹ ^ 4) * (1 + |s.im|) ^ 8 := by
    intro s hlo hhi ht
    apply hB η hη hη' s hlo hhi
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
    linarith
  have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  have hT := transform_entire hw.continuous (by linarith : 0 < X / 2) hrad 0
  apply shift_of_rectangles hw hX hΘ (by linarith) (by linarith)
    (show 0 ≤ C * η⁻¹ ^ 4 by positivity) hp hs hg
    (hline (1 / 2 + η) (by linarith) (by linarith)) (hline 2 (by norm_num) (by norm_num)) 0
  intro T hTp
  exact rectangle_of_laurent (by linarith) (by norm_num) hTp
    (rectangle_subset (by linarith) (by linarith) T) (hF.mul hT.differentiableOn)
    (SmoothZeroResidue.weighted_laurent hw.continuous (by linarith : 0 < X / 2) hrad)

end Cubic.BoxAsymptotic.SmoothContourShift
