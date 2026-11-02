import Cubic.BoxAsymptotic.HeckeNormWeights
import Cubic.BoxAsymptotic.HeckeSeriesConvergence
import Mathlib.Order.Filter.AtTopBot.Finset

/-! Absolute convergence and norm-cutoff limits for the weighted ideal sums.
This supplies the justification for replacing the AFE's norm-fiber series by
dyadic sums over the actual ideals, without inferring absolute ideal convergence
from convergence after cancellation inside each norm fiber. -/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeWeightedSeries

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.BoxAsymptotic.IdealAngularData Cubic.BoxAsymptotic.HeckeSeriesConvergence
open Cubic.BoxAsymptotic.WeightedIdealSums
open Filter
open scoped Topology

local instance : DecidableEq (Ideal Integers) := Classical.decEq _

def term (χ : Ideal Integers → ℂ) (u : ℂ) (w : ℝ → ℂ) (I : Ideal Integers) : ℂ :=
  HeckeSeriesConvergence.idealTerm χ u I * w (Ideal.absNorm I)

theorem term_bot (χ : Ideal Integers → ℂ) (u : ℂ) (w : ℝ → ℂ) : term χ u w ⊥ = 0 := by
  simp [term, HeckeSeriesConvergence.idealTerm, Cubic.PoissonSummation.DedekindZetaSeries.idealTerm]

theorem norm_bound (χ : Ideal Integers → ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1)
    (u : ℂ) (w : ℝ → ℂ) {C W : ℝ}
    (hw : ∀ x > 0, ‖w x‖ ≤ C * (W / x) ^ 3) (I : Ideal Integers) :
    ‖term χ u w I‖ ≤ C * W ^ 3 *
      ‖Cubic.PoissonSummation.DedekindZetaSeries.idealTerm E (u + 3) I‖ := by
  by_cases hI : I = ⊥
  · simp [hI, term_bot, Cubic.PoissonSummation.DedekindZetaSeries.idealTerm]
  have hN : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
  have hN0 : (0 : ℝ) < Ideal.absNorm I := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hwm := hw (Ideal.absNorm I) hN0
  rw [term, norm_mul, HeckeSeriesConvergence.idealTerm, norm_mul]
  have hb : ‖χ I‖ * ‖Cubic.PoissonSummation.DedekindZetaSeries.idealTerm E u I‖ ≤
      ‖Cubic.PoissonSummation.DedekindZetaSeries.idealTerm E u I‖ :=
    mul_le_of_le_one_left (norm_nonneg _) (hχ I)
  calc
    _ ≤ ‖Cubic.PoissonSummation.DedekindZetaSeries.idealTerm E u I‖ * (C * (W / Ideal.absNorm I) ^ 3) :=
      mul_le_mul hb hwm (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [Cubic.PoissonSummation.DedekindZetaSeries.idealTerm,
        LSeries.norm_term_eq, if_neg hN, norm_one, Complex.add_re, show (3 : ℂ).re = (3 : ℝ) by norm_num]
      rw [Real.rpow_add hN0, Real.rpow_ofNat]
      field_simp

theorem absolute (χ : Ideal Integers → ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1)
    (u : ℂ) (hu : -2 < u.re) (w : ℝ → ℂ) {C W : ℝ}
    (hw : ∀ x > 0, ‖w x‖ ≤ C * (W / x) ^ 3) :
    Summable (fun I => ‖term χ u w I‖) := by
  have hz := Cubic.PoissonSummation.DedekindZetaSeries.ideal_series_absolute E (u + 3)
    (by simp; linarith)
  exact (hz.mul_left (C * W ^ 3)).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_bound χ hχ u w hw)

theorem fiber_sum (χ : Ideal Integers → ℂ) (u : ℂ) (w : ℝ → ℂ) (n : ℕ) :
    (∑' I : {I : Ideal Integers // Ideal.absNorm I = n}, term χ u w I.val) =
      LSeries.term (HeckeSeriesConvergence.coefficient χ) u n * w n := by
  have he : (fun I : {I : Ideal Integers // Ideal.absNorm I = n} => term χ u w I.val) =
      fun I : {I : Ideal Integers // Ideal.absNorm I = n} =>
        HeckeSeriesConvergence.idealTerm χ u I.val * w n := by
    funext I
    simp only [term, I.property]
  rw [he, tsum_mul_right, HeckeSeriesConvergence.fiber_sum]

theorem sum_eq (χ : Ideal Integers → ℂ) (u : ℂ) (w : ℝ → ℂ)
    (h : Summable (fun I => ‖term χ u w I‖)) :
    (∑' I, term χ u w I) =
      ∑' n, LSeries.term (HeckeSeriesConvergence.coefficient χ) u n * w n := by
  have hh := h.of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  have he : (fun n : ℕ => ∑' I : Ideal.absNorm ⁻¹' {n}, term χ u w I.val) =
      fun n : ℕ => LSeries.term (HeckeSeriesConvergence.coefficient χ) u n * w n := by
    funext n
    exact fiber_sum χ u w n
  rw [he] at hh
  exact hh.tsum_eq.symm

theorem coefficient_conjugate (χ : Ideal Integers → ℂ) (n : ℕ) :
    HeckeSeriesConvergence.coefficient (fun I => star (χ I)) n =
      star (HeckeSeriesConvergence.coefficient χ n) := by
  classical
  simp only [HeckeSeriesConvergence.coefficient,
    finsum_mem_eq_finite_toFinset_sum _ (Ideal.finite_setOf_absNorm_eq n), star_sum]

theorem balls_cofinal : Tendsto (fun Y : ℝ => insert ⊥ (idealBall Y)) atTop atTop := by
  classical
  apply Monotone.tendsto_atTop_finset
  · intro X Y hXY I hI
    rcases Finset.mem_insert.mp hI with rfl | hI
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (mem_idealBall.mpr
        ⟨(mem_idealBall.mp hI).1, (mem_idealBall.mp hI).2.trans hXY⟩)
  · intro I
    refine ⟨Ideal.absNorm I, ?_⟩
    by_cases hI : I = ⊥
    · simp [hI]
    · exact Finset.mem_insert_of_mem (mem_idealBall.mpr ⟨hI, le_rfl⟩)

theorem initial_limit (χ : Ideal Integers → ℂ) (u : ℂ) (w : ℝ → ℂ)
    (h : Summable (fun I => ‖term χ u w I‖)) :
    Tendsto (fun Y : ℝ => initialWeighted χ (HeckeNormWeights.coefficient u) Y w)
      atTop (𝓝 (∑' I, term χ u w I)) := by
  classical
  have hh := h.of_norm.hasSum.comp balls_cofinal
  apply hh.congr
  intro Y
  have hbot : (⊥ : Ideal Integers) ∉ idealBall Y := fun h => (mem_idealBall.mp h).1 rfl
  dsimp only [Function.comp_apply]
  rw [Finset.sum_insert hbot, term_bot, zero_add]
  apply Finset.sum_congr rfl
  intro I _
  dsimp [term, HeckeSeriesConvergence.idealTerm, HeckeNormWeights.coefficient]
  ring

end Cubic.BoxAsymptotic.HeckeWeightedSeries
