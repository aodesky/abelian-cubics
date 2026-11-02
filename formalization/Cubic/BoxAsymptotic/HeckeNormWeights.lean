import Cubic.BoxAsymptotic.WeightedIdealSums
import Cubic.PoissonSummation.DedekindZetaSeries

/-! Norm estimates for the forward and dual Dirichlet coefficients in the
approximate functional equation. The dual prefactor cancels the growing power
of the common norm scale; no power of `K` is lost.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeNormWeights

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.BoxAsymptotic.IdealAngularData Cubic.BoxAsymptotic.IdealLargeSieve

def coefficient (s : ℂ) (I : Ideal Integers) : ℂ :=
  Cubic.PoissonSummation.DedekindZetaSeries.idealTerm E s I

theorem norm_coefficient {Y : ℝ} {I : Ideal Integers} (hI : I ∈ idealBall Y) (s : ℂ) :
    ‖coefficient s I‖ = 1 / (Ideal.absNorm I : ℝ) ^ s.re := by
  have h0 : Ideal.absNorm I ≠ 0 := by have := norm_pos hI; omega
  simp only [coefficient, Cubic.PoissonSummation.DedekindZetaSeries.idealTerm,
    LSeries.norm_term_eq, if_neg h0, norm_one]

theorem forward_bound {Y : ℝ} {I : Ideal Integers} (hI : I ∈ idealBall Y)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖coefficient s I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I) := by
  rw [norm_coefficient hI, Real.sqrt_eq_rpow]
  have h1 : (1 : ℝ) ≤ Ideal.absNorm I := by exact_mod_cast norm_pos hI
  exact one_div_le_one_div_of_le (by positivity)
    (Real.rpow_le_rpow_of_exponent_le h1 hs)

theorem dual_bound {Y : ℝ} {I : Ideal Integers} (hI : I ∈ idealBall Y)
    {η : ℝ} (hη : 0 ≤ η) (t : ℝ) :
    ‖coefficient ((1 / 2 - η : ℝ) + t * Complex.I) I‖ ≤
      Y ^ η / Real.sqrt (Ideal.absNorm I) := by
  have hN : (0 : ℝ) < Ideal.absNorm I := by exact_mod_cast norm_pos hI
  rw [norm_coefficient hI]
  have hre : (((1 / 2 - η : ℝ) : ℂ) + t * Complex.I).re = 1 / 2 - η := by simp
  rw [hre, one_div, ← Real.rpow_neg hN.le, show -(1 / 2 - η) = η + -(1 / 2) by ring,
    Real.rpow_add hN, Real.rpow_neg hN.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Real.rpow_le_rpow hN.le (mem_idealBall.mp hI).2 hη

/-- A slightly coarser dyadic estimate than `2^(j/4)` is enough when the
weights decay as `2^(-3j)`. Crucially its constant is independent of `Y`. -/
theorem dual_prefactor {Y η : ℝ} (hY : 1 ≤ Y) (hη : 0 ≤ η) (hη' : η ≤ 1) (j : ℕ) :
    Y ^ (-2 * η) * ((2 : ℝ) ^ j * Y) ^ η ≤ (2 : ℝ) ^ j := by
  have hY0 : 0 < Y := by linarith
  have htwo : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hfirst : Y ^ (-η) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hY (neg_nonpos.mpr hη)
  have hsecond : ((2 : ℝ) ^ j) ^ η ≤ (2 : ℝ) ^ j := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le htwo hη'
  rw [Real.mul_rpow (by positivity) hY0.le]
  calc
    _ = (Y ^ (-2 * η) * Y ^ η) * ((2 : ℝ) ^ j) ^ η := by ring
    _ = Y ^ (-η) * ((2 : ℝ) ^ j) ^ η := by
      rw [← Real.rpow_add hY0]
      congr 2
      ring
    _ ≤ 1 * (2 : ℝ) ^ j := mul_le_mul hfirst hsecond (by positivity) (by norm_num)
    _ = _ := one_mul _

end Cubic.BoxAsymptotic.HeckeNormWeights
