import Cubic.Analysis.MellinDirichletPairing
import Cubic.BoxAsymptotic.SmoothFourierCount
import Cubic.BoxAsymptotic.SmoothMellinInversion
import Cubic.BoxAsymptotic.AngularSeriesConvergence

/-! The initial Fourier--Mellin identity for the original smoothed count. The
sum over norms is exchanged with the integral on `Re s = 2` by absolute
convergence of the original Dirichlet series. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothMellinCount

open Complex MeasureTheory Set
open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.AngularSeriesData
open Cubic.BoxAsymptotic.SmoothTransformData
open Cubic.BoxAsymptotic.SmoothWeightData
open Cubic.Analysis.MellinDirichletPairing
open scoped ContDiff

theorem pairing_eq_modeSum
    {w : ℝ × ℝ → ℝ} {X Θ θ₀ M : ℝ}
    (hw : ContDiff ℝ ∞ w) (hX : 0 < X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M 4) (k : ℤ) :
    pairing 2 (series k) (transform w k) =
      SmoothFourierCount.modeSum w (⌊4 * X⌋₊ + 1) k := by
  have hrad : Function.support w ⊆ {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X} :=
    fun p h => ⟨(hs h).1, (hs h).2.1⟩
  have hsup := angularCoefficient_support hrad k
  have hzero : angularCoefficient w k 0 = 0 :=
    Cubic.Analysis.CompactMellin.zero_outside hsup (by
      intro h
      have := h.1
      linarith)
  have hi (n : ℕ) :
      (if n = 0 then 0 else coefficient k n * mellinInv 2 (transform w k) n) =
        coefficient k n * angularCoefficient w k n := by
    by_cases hn : n = 0
    · simp [hn, hzero]
    · rw [if_neg hn, SmoothMellinInversion.inversion hw hX hΘ hM hp hs hb k
        (by norm_num) (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  have hpair := hasSum_pairing (σ := (2 : ℝ))
    (AngularSeriesConvergence.summable k 2 (by norm_num))
    (SmoothMellinInversion.vertical_integrable hw hX hΘ hM hp hs hb k
      (by norm_num) (by norm_num))
  simp only [hi] at hpair
  apply hpair.unique
  unfold SmoothFourierCount.modeSum
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have hnn : ⌊4 * X⌋₊ + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
  have hn' : 4 * X < (n : ℝ) := Nat.lt_of_floor_lt (by omega)
  rw [Cubic.Analysis.CompactMellin.zero_outside hsup (by
    intro h
    exact (not_le_of_gt hn') h.2), mul_zero]

/-- Absolutely convergent Fourier--Mellin expansion on the initial line. -/
theorem initial_expansion
    {w : ℝ × ℝ → ℝ} {X Θ θ₀ M : ℝ}
    (hw : ContDiff ℝ ∞ w) (hX : 0 < X) (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hp : ∀ n θ, w (n, θ + 2 * Real.pi) = w (n, θ))
    (hs : Function.support w ⊆
      {p | X / 2 ≤ p.1 ∧ p.1 ≤ 4 * X ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ})
    (hb : normalizedDerivativeBound w Θ M 4) :
    HasSum (fun k : ℤ => pairing 2 (series k) (transform w k))
      ((∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (fun θ => w (n, θ)) : ℝ) : ℂ) := by
  simp_rw [pairing_eq_modeSum hw hX hΘ hM hp hs hb]
  exact SmoothFourierCount.reconstruction hw hΘ hp (hb.mono (by omega)) _

end Cubic.BoxAsymptotic.SmoothMellinCount
