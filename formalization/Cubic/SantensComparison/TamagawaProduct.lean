import Cubic.SantensComparison.UnramifiedGaugeVolume
import Cubic.SantensComparison.RamifiedGaugeVolume
import Cubic.SantensComparison.ConeIntegral
import Cubic.Counting.AsymptoticConstantIdentities
import Cubic.Counting.IntegralPointCountData

/-! Evaluation and convergence of the product of the computed local volume
representatives. This does not yet identify the product with the constant in
Santens's counting theorem: that requires the general theorem and its geometric
and measure-theoretic specialization. -/

noncomputable section

namespace Cubic.SantensComparison.TamagawaProduct

open MeasureTheory UnramifiedGaugeVolume
open Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.Counting.AsymptoticConstantsData
open Cubic.Counting.IntegralPointCountData (alpha)
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open scoped LogDifferentials

def unramifiedProduct : ℝ :=
  (∏' p : SplitPrimes, splitVolume p) * ∏' p : InertPrimes, inertVolume p

def tau : ℝ :=
  2 * NumberField.dedekindZeta_residue E * unramifiedProduct *
    RamifiedGaugeVolume.normalizedVolume * LogDifferentials.boundaryResidueMeasure.real Set.univ

def peyreExpression : ℝ := FanData.theta / (2 * (Nat.factorial (2-1) : ℝ)) * tau

theorem split_absolute : Summable (fun p : SplitPrimes => ‖splitVolume p-1‖) := by
  simp_rw [split_volume]
  exact Cubic.Counting.AsymptoticConstantsConvergence.split_product_absolute

theorem inert_absolute : Summable (fun p : InertPrimes => ‖inertVolume p-1‖) := by
  simp_rw [inert_volume]
  exact Cubic.Counting.AsymptoticConstantsConvergence.inert_product_absolute

theorem unramified_product : unramifiedProduct = 27*alpha/(4*Real.pi^2) := by
  unfold unramifiedProduct
  simp_rw [split_volume, inert_volume]
  have h := Cubic.Counting.AsymptoticConstantIdentities.leading_formulas
  change 4*Real.pi^2/81 * (∏' q : InertPrimes, originalInertFactor q) *
    (∏' p : SplitPrimes, originalSplitFactor p) = (1/3)*alpha at h
  have hp := Real.pi_ne_zero
  field_simp at h ⊢
  nlinarith

theorem tau_value : tau = 2*alpha/9 := by
  rw [tau, Cubic.PoissonSummation.QuadraticDedekindResidue.residue_value,
    unramified_product, RamifiedGaugeVolume.normalized_volume,
    LogDifferentials.boundary_residue_mass]
  have hp := Real.pi_ne_zero
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs₂ : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [hs₂]
  ring

theorem peyre_expression : peyreExpression = tau ∧ tau = 2*alpha/9 := by
  refine ⟨?_,tau_value⟩
  simp [peyreExpression, ConeIntegral.cone_constant]

theorem positive : 0 < tau := by
  rw [tau_value]
  have h := Cubic.Counting.AsymptoticConstantIdentities.original_leading_positive
  rw [Cubic.Counting.AsymptoticConstantIdentities.leading_formulas] at h
  change 0 < (1/3:ℝ)*alpha at h
  linarith

end Cubic.SantensComparison.TamagawaProduct
