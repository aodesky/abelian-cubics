import Cubic.Counting.QuadraticLApproximationConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Identification with the quadratic L-function

In the absolutely convergent half-plane the paired series is the difference
of two Hurwitz zeta series. Analytic uniqueness then identifies the locally
uniform limit on `Re(s) > -1` with mathlib's entire quadratic L-function.
-/

noncomputable section

namespace Cubic.Counting.QuadraticLApproximationIdentification

open Filter Set QuadraticLDerivativeApproximation QuadraticLApproximationConvergence
open Cubic.PoissonSummation.QuadraticDirichletCharacter
open scoped Topology

theorem L_eq_hurwitz (s : ℂ) : DirichletCharacter.LFunction character s =
    (3 : ℂ) ^ (-s) * (HurwitzZeta.hurwitzZeta ((1 / 3 : ℝ) : UnitAddCircle) s -
      HurwitzZeta.hurwitzZeta ((2 / 3 : ℝ) : UnitAddCircle) s) := by
  rw [DirichletCharacter.LFunction, ZMod.LFunction]
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [hu]
  rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
    Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3))),
    Finset.sum_singleton]
  simp only [character_zero, character_one, character_two, zero_mul, one_mul,
    neg_one_mul, zero_add, Nat.cast_ofNat]
  have h₁ := ZMod.toAddCircle_natCast (N := 3) 1
  have h₂ := ZMod.toAddCircle_natCast (N := 3) 2
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h₁ h₂
  rw [h₁, h₂]
  ring

theorem scaled_term (k : ℕ) (a : ℝ) (ha : 0 ≤ a) (s : ℂ) :
    (3 : ℂ) ^ (-s) * (1 / ((k : ℂ) + (a : ℂ) / 3) ^ s) =
      (3 * (k : ℂ) + a) ^ (-s) := by
  have h := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    (show 0 ≤ (k : ℝ) + a / 3 by positivity) (-s)
  push_cast at h
  rw [show (3 : ℂ) * ((k : ℂ) + (a : ℂ) / 3) = 3 * (k : ℂ) + a by ring] at h
  simpa only [Complex.cpow_neg, one_div] using h.symm

theorem paired_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => (3 * (k : ℂ) + 1) ^ (-s) - (3 * (k : ℂ) + 2) ^ (-s))
      (DirichletCharacter.LFunction character s) := by
  have h₁ := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (by norm_num : (1 / 3 : ℝ) ∈ Icc 0 1) hs
  have h₂ := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (by norm_num : (2 / 3 : ℝ) ∈ Icc 0 1) hs
  have h := (h₁.sub h₂).mul_left ((3 : ℂ) ^ (-s))
  rw [L_eq_hurwitz]
  convert h using 1
  ext k
  rw [mul_sub]
  push_cast
  simpa only [Complex.ofReal_one, Complex.ofReal_ofNat] using
    congrArg₂ (fun x y : ℂ => x - y) (scaled_term k 1 (by norm_num) s).symm
      (scaled_term k 2 (by norm_num) s).symm

theorem tail_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => (3 * ((n : ℂ) + 1)) ^ (-s) / 3) atTop (𝓝 0) := by
  suffices h : Tendsto (fun n : ℕ => (3 * ((n : ℂ) + 1)) ^ (-s)) atTop (𝓝 0) by
    simpa using h.div_const 3
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun n : ℕ => 3 * ((n : ℝ) + 1)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num)
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have h := (tendsto_rpow_neg_atTop hs).comp ht
  convert h using 1
  ext n
  have he : 3 * ((n : ℂ) + 1) = ((3 * ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

theorem approximation_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n => approximation n s) atTop
      (𝓝 (DirichletCharacter.LFunction character s)) := by
  have hsum := (paired_hasSum hs).tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
  simpa only [Function.comp_apply, approximation, add_zero] using
    hsum.add (tail_tendsto_zero (by linarith))

theorem limit_eq_L {s : ℂ} (hs : -1 < s.re) :
    limit s = DirichletCharacter.LFunction character s := by
  have hopen : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconvex : Convex ℝ {s : ℂ | -1 < s.re} :=
    convex_halfSpace_gt Complex.reLm.isLinear (-1)
  have he : limit =ᶠ[𝓝 (2 : ℂ)] DirichletCharacter.LFunction character := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact tendsto_nhds_unique (locally_uniform.tendsto_at (by linarith : -1 < z.re))
      (approximation_tendsto hz)
  exact (limit_differentiableOn.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (differentiable_LFunction.differentiableOn.analyticOnNhd hopen)
    hconvex.isPreconnected (by norm_num : (2 : ℂ) ∈ {s : ℂ | -1 < s.re}) he hs

theorem locally_uniform_L : TendstoLocallyUniformlyOn approximation
    (DirichletCharacter.LFunction character) atTop {s : ℂ | -1 < s.re} :=
  locally_uniform.congr_right (fun _ hs => limit_eq_L hs)

theorem zero_derivative : CubicTargets.Counting.QuadraticLZeroDerivative.Claim :=
  zero_derivative_of_locally_uniform locally_uniform_L

end Cubic.Counting.QuadraticLApproximationIdentification
