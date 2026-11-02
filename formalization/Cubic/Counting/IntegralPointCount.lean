import Cubic.Counting.WeightedCount
import Cubic.Counting.DSummatory
import Cubic.ToricHeights.AffinePointComparison
import CubicTargets.Counting.IntegralPointCount

/-! Proof of `cor:integralPointCount`: identify the original bounded integral point
set with the coefficient sum, substitute `X = H²`, and use the Laurent constants.
The exponent in the coefficient estimate is taken to be `ε/2`. -/

noncomputable section

namespace Cubic.Counting.IntegralPointCount

open Filter Asymptotics IntegralPointCountData AsymptoticConstantsData GeneralMonicData
open Cubic.PoissonSummation

theorem boundedPoints_eq (H : ℝ) (hH : 0 ≤ H) :
    boundedPoints H = WeightedCount.IP H := by
  ext P
  simp only [boundedPoints, WeightedCount.IP, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hle⟩
    rw [(Cubic.ToricHeights.CanonicalHeight.«prop:canonicalHeight»).2 P hP,
      Complex.ofReal_re] at hle
    exact ⟨hP, (Real.sqrt_le_left hH).mp hle⟩
  · rintro ⟨hP, hle⟩
    refine ⟨hP, ?_⟩
    rw [(Cubic.ToricHeights.CanonicalHeight.«prop:canonicalHeight»).2 P hP,
      Complex.ofReal_re]
    exact (Real.sqrt_le_left hH).mpr hle

theorem finite_counts (H : ℝ) : (boundedPoints H).Finite := by
  by_cases hH : 0 ≤ H
  · rw [boundedPoints_eq H hH]
    exact WeightedCount.IP_finite H
  · have he : boundedPoints H = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro P ⟨hP, hle⟩
      rw [(Cubic.ToricHeights.CanonicalHeight.«prop:canonicalHeight»).2 P hP,
        Complex.ofReal_re] at hle
      exact hH ((Real.sqrt_nonneg _).trans hle)
    rw [he]
    exact Set.finite_empty

theorem count_eq_sum (H : ℝ) (hH : 0 ≤ H) :
    (count H : ℝ) = ∑ n ∈ Finset.Icc 1 ⌊H ^ 2⌋₊, (d n : ℝ) := by
  rw [count, boundedPoints_eq H hH, ← WeightedCount.sum_count_eq H]
  simp [d]

/-- Restriction preserves every invariant function and the original height. -/
def boundedPointsEquiv (H : ℝ) : boundedPoints H ≃ boundedAffinePoints H :=
  Equiv.ofBijective
    (fun Q => ⟨Cubic.ToricHeights.AffinePointComparison.restrictPoint Q.val,
      (show Cubic.ToricHeights.AffineChartInvariants.IsD0Integral
        (Cubic.ToricHeights.AffinePointComparison.restrictPoint Q.val) from Q.property.1),
      Q.val, rfl, Q.property.2⟩) (by
    constructor
    · intro P Q he
      apply Subtype.ext
      exact Cubic.ToricHeights.AffinePointComparison.restrict_injective
        (congrArg Subtype.val he)
    · rintro ⟨P, hP, Q, hQ, hheight⟩
      have hint : Cubic.ToricHeights.AffineInvariantRing.IntegralPoint Q := by
        change Cubic.ToricHeights.AffineChartInvariants.IsD0Integral
          (Cubic.ToricHeights.AffinePointComparison.restrictPoint Q)
        change Cubic.ToricHeights.AffinePointComparison.restrictPoint Q = P at hQ
        rw [hQ]
        exact hP
      exact ⟨⟨Q, hint, hheight⟩, Subtype.ext hQ⟩)

theorem affineCount_eq (H : ℝ) : affineCount H = count H :=
  (Nat.card_congr (boundedPointsEquiv H)).symm

theorem affine_finite_counts (H : ℝ) : (boundedAffinePoints H).Finite := by
  haveI := (finite_counts H).to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (boundedPointsEquiv H))

theorem main_term (H : ℝ) :
    Cconst / 3 * (H ^ 2) * Real.log (H ^ 2) + 2 * Dconst / 3 * (H ^ 2) =
      H ^ 2 * Q EulerKroneckerCalculation.value (Real.log H) := by
  have hc := AsymptoticConstantsAssembly.constants
  have hC : Cconst = alpha / 3 := by
    simpa [Cconst, simplifiedLeading, alpha, div_eq_mul_inv, mul_comm] using
      hc.simplified_leading
  have hr : Dconst / Cconst =
      EulerKroneckerCalculation.value.re - (deriv riemannZeta 2 / riemannZeta 2).re +
        beta + 3 / 8 * Real.log 3 - 1 / 2 := by
    have hs : ((Dconst / Cconst : ℝ) : ℂ) =
        simplifiedSecondaryRatio EulerKroneckerCalculation.value := by
      simpa only [Cconst, Dconst, Complex.ofReal_div] using hc.simplified_secondary
    have h := congrArg Complex.re hs
    have he : (simplifiedSecondaryRatio EulerKroneckerCalculation.value).re =
        EulerKroneckerCalculation.value.re - (deriv riemannZeta 2 / riemannZeta 2).re +
          beta + 3 / 8 * Real.log 3 - 1 / 2 := by
      unfold simplifiedSecondaryRatio beta
      rw [← Complex.ofReal_tsum]
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
      norm_num only [Complex.mul_re, Complex.div_re, Complex.re_ofNat, Complex.im_ofNat,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.normSq_ofNat]
      ring
    rw [Complex.ofReal_re, he] at h
    exact h
  have hD : Dconst = Cconst *
      (EulerKroneckerCalculation.value.re - (deriv riemannZeta 2 / riemannZeta 2).re +
        beta + 3 / 8 * Real.log 3 - 1 / 2) := by
    have hn : Cconst ≠ 0 := hc.positive.ne'
    rw [div_eq_iff hn] at hr
    simpa [Cconst, Dconst, mul_comm] using hr
  rw [Real.log_pow, hD, hC, Q]
  ring

theorem estimate (ε : ℝ) (hε : 0 < ε)
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    (fun H : ℝ => (count H : ℝ) - H ^ 2 * Q EulerKroneckerCalculation.value (Real.log H))
      =O[atTop] (fun H : ℝ => H ^ (1 + ε)) := by
  obtain ⟨K, X₀, hK⟩ := DSummatory.coefficient_estimate hPoisson hCN
    (ε / 2) (by linarith)
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (max 1 X₀)] with H hH
  have hH1 : 1 ≤ H := (le_max_left _ _).trans hH
  have hH0 : 0 ≤ H := by linarith
  have hX : X₀ ≤ H ^ 2 := (le_max_right _ _).trans hH |>.trans (by nlinarith)
  have hpow : (H ^ 2) ^ (1 / 2 + ε / 2) = H ^ (1 + ε) := by
    rw [← Real.rpow_natCast H 2, ← Real.rpow_mul hH0]
    congr 1
    ring
  have h := hK (H ^ 2) hX
  dsimp only at h
  rw [← count_eq_sum H hH0, main_term H, hpow] at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hH0 _)] using h

theorem «cor:integralPointCount»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.IntegralPointCount.Claim := by
  have hc := AsymptoticConstantsAssembly.constants
  refine ⟨QuadraticZetaRegularization.value, EulerKroneckerCalculation.value,
    EulerKroneckerCalculation.genuine_constant, hc.simplified_product_absolute,
    hc.simplified_sum_absolute, ?_,
      ⟨Cubic.ToricHeights.AffinePointComparison.exists_unique_integral_extension,
        affine_finite_counts, fun ε hε => ?_⟩⟩
  · have hC : originalLeading = alpha / 3 := by
      simpa [simplifiedLeading, alpha, div_eq_mul_inv, mul_comm] using hc.simplified_leading
    rw [hC] at hc
    exact ((div_pos_iff.mp hc.positive).resolve_right (by norm_num)).1
  · simpa only [affineCount_eq] using estimate ε hε hPoisson hCN

end Cubic.Counting.IntegralPointCount
