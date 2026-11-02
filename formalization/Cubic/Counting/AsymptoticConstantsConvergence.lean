import Cubic.Counting.AsymptoticConstantsData
import Cubic.PoissonSummation.LeadingTermsCorrection
import Cubic.PoissonSummation.LeadingTermsPrimeSums
import Cubic.PoissonSummation.LeadingTermsSplitProduct

/-!
# Convergence of the real products and sums in `thm:asymptoticPolynomialCount`

Transport the proved local estimates to the literal real expressions printed
in the introduction. These results justify the products and rearrangements in
the subsequent constant calculations, independently of the counting asymptotic.
-/

noncomputable section

namespace Cubic.Counting.AsymptoticConstantsConvergence

open Cubic.PoissonSummation Cubic.PoissonSummation.FiniteEulerProduct
open AsymptoticConstantsData

theorem inert_factor_eq (q : InertPrimes) :
    originalInertFactor q = LeadingTermsCorrection.inertReal q := by
  simp [originalInertFactor, LeadingTermsCorrection.inertReal, inv_pow]

theorem split_factor_eq (p : SplitPrimes) :
    originalSplitFactor p = LeadingTermsCorrection.splitReal p := by
  dsimp [originalSplitFactor, LeadingTermsCorrection.splitReal]
  simp only [div_eq_mul_inv]
  ring

theorem inert_product_absolute :
    Summable (fun q : InertPrimes => ‖originalInertFactor q - 1‖) := by
  simpa only [inert_factor_eq] using LeadingTermsCorrection.inertReal_absolute

theorem split_product_absolute :
    Summable (fun p : SplitPrimes => ‖originalSplitFactor p - 1‖) := by
  simpa only [split_factor_eq] using LeadingTermsCorrection.splitReal_absolute

theorem simplified_factor_cast (p : SplitPrimes) :
    (simplifiedSplitFactor p : ℂ) =
      1 - 2 / ((p.1 : ℂ) * ((p.1 : ℂ) + 1)) := by
  simp [simplifiedSplitFactor]

theorem simplified_product_absolute :
    Summable (fun p : SplitPrimes => ‖simplifiedSplitFactor p - 1‖) := by
  have h := LeadingTermsSplitProduct.absolute_at_two
  simp_rw [← simplified_factor_cast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real] at h
  exact h

theorem inert_log_cast (q : InertPrimes) :
    (inertLogTerm q : ℂ) = (Real.log (q.1 : ℝ) : ℂ) / ((q.1 : ℂ) ^ 2 - 1) := by
  simp [inertLogTerm]

theorem original_split_log_cast (p : SplitPrimes) :
    (3 : ℂ) * (originalSplitLogTerm p : ℂ) =
      3 * ((p.1 : ℂ) - 1) * (Real.log (p.1 : ℝ) : ℂ) /
        ((p.1 : ℂ) ^ 3 - 3 * (p.1 : ℂ) + 2) := by
  simp [originalSplitLogTerm]
  ring

theorem simplified_log_cast (p : SplitPrimes) :
    (simplifiedSplitLogTerm p : ℂ) = LeadingTermsData.splitLogTerm p := by
  simp [simplifiedSplitLogTerm, LeadingTermsData.splitLogTerm]

theorem inert_sum_absolute : Summable (fun q : InertPrimes => ‖inertLogTerm q‖) := by
  have h := LeadingTermsPrimeSums.summable_inert_log
  simpa only [← inert_log_cast, Complex.norm_real] using h

theorem split_sum_absolute : Summable (fun p : SplitPrimes => ‖originalSplitLogTerm p‖) := by
  have h := LeadingTermsPrimeSums.summable_original_split_log
  simp_rw [← original_split_log_cast, norm_mul, Complex.norm_ofNat, Complex.norm_real] at h
  exact (summable_mul_left_iff (by norm_num : (3 : ℝ) ≠ 0)).mp h

theorem simplified_sum_absolute :
    Summable (fun p : SplitPrimes => ‖simplifiedSplitLogTerm p‖) := by
  have h := LeadingTermsPrimeSums.summable_split_log
  simpa only [← simplified_log_cast, Complex.norm_real] using h

/-- The complex cast of an absolutely convergent real product is the product of the casts. -/
theorem product_cast {ι : Type*} (f : ι → ℝ)
    (h : Summable (fun i => ‖f i - 1‖)) :
    ((∏' i, f i : ℝ) : ℂ) = ∏' i, (f i : ℂ) := by
  have hm : Multipliable f := by simpa using multipliable_one_add_of_summable h
  exact hm.map_tprod Complex.ofRealHom.toMonoidHom Complex.continuous_ofReal

theorem simplified_product_cast :
    ((∏' p : SplitPrimes, simplifiedSplitFactor p : ℝ) : ℂ) =
      LeadingTermsData.splitProductAtTwo := by
  rw [product_cast _ simplified_product_absolute]
  simp only [simplified_factor_cast, LeadingTermsData.splitProductAtTwo]

end Cubic.Counting.AsymptoticConstantsConvergence
