import Cubic.Counting.WeightedCount
import Cubic.Counting.AsymptoticConstantsAssembly
import Cubic.Counting.AsymptoticHeightShift
import Cubic.Counting.PolynomialCountFiniteness
import Cubic.ToricHeights.RootVsToric
import CubicTargets.Counting.AsymptoticPolynomialCount
import Cubic.Counting.IrrPolys

/-!
# Proof of `thm:asymptoticPolynomialCount` from `eqn:dSummatoryForGeneralTrace`

The paper: "Apply `eqn:weightedPolynomialCount` and `eqn:ellipseLatticeCount` with
`H = √X`. Equation `eqn:dSummatoryForGeneralTrace` then gives `eqn:irrPolys` … By Lemma
`lemma:rootVsToric`, the condition `h(f) ≤ H` is equivalent to `H(f) ≤ √X` with
`X = 3H²+1`. For this choice, `X log X = 6H² log H + 3H² log 3 + O(log H)`.
Substituting …"

The main-term algebra and the constants are in `AsymptoticConstantScaling`,
`AsymptoticHeightShift` and `AsymptoticConstantsAssembly`.
-/

noncomputable section

namespace Cubic.Counting.AsymptoticPolynomialCount

open Polynomial Filter Asymptotics
open Cubic.Counting.PolynomialCountData Cubic.Counting.WeightedCount
open Cubic.QuadraticCorrespondence.DescendedCoefficients
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open CubicTargets.Counting.WeightedPolynomialCount (countSet toricHeight)

/-- Each `f ∈ F` is the polynomial of an integral point (two of them, by
`CyclicFibre.fibre_card`). -/
theorem exists_point (a b : ℤ) (hc : HasCyclicCubicGaloisGroup (cubic a b)) :
    ∃ Q : Cubic.ToricHeights.IntegralPolynomialData.Points,
      Cubic.ToricHeights.IntegralPolynomialData.polynomial Q = traceOneCubic a b ∧
        Q.val linearCoefficient = a := by
  have hpos : 0 < Nat.card {P : Pts // characteristicPolynomial P = cubic a b} := by
    rw [CyclicFibre.fibre_card _ _ hc]; norm_num
  obtain ⟨⟨P, hP⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  have ha : P linearCoefficient = a := by
    have := congrArg (fun f : ℚ[X] => f.coeff 1) hP
    simpa only [characteristicPolynomial, cubic_coeff_one] using this
  have hb : P constantCoefficient = b := by
    have := congrArg (fun f : ℚ[X] => f.coeff 0) hP
    simpa only [characteristicPolynomial, cubic_coeff_zero] using this
  have hint : Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P :=
    (Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion P).mpr
      ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨⟨P, hint⟩, ?_, ha⟩
  change traceOneCubic (P linearCoefficient).num (P constantCoefficient).num = _
  rw [ha, hb, Rat.num_intCast, Rat.num_intCast]

/-- `lemma:rootVsToric`: for `f ∈ F`, `h(f) ≤ H` iff `H(f) ≤ √(1 + 3H²)`. -/
theorem rootHeight_le_iff {f : ℤ[X]} (hf : f ∈ cyclicPolynomials) (H : ℝ) (hH : 0 ≤ H) :
    rootHeight f ≤ H ↔ toricHeight f ≤ Real.sqrt (1 + 3 * H ^ 2) := by
  obtain ⟨⟨a, b, rfl⟩, hc⟩ := hf
  rw [traceOneCubic_map] at hc
  obtain ⟨Q, hQ, ha⟩ := exists_point a b hc
  have hQs := Cubic.ToricHeights.«lemma:rootVsToric» Q
  have hroot : Cubic.ToricHeights.IntegralPolynomialData.rootHeight Q =
      rootHeight (traceOneCubic a b) := by
    rw [Cubic.ToricHeights.IntegralPolynomialData.rootHeight, hQ]
  have htoric : Cubic.ToricHeights.IntegralPolynomialData.toricHeight Q =
      toricHeight (traceOneCubic a b) := by
    have h1 := hQs.height_real
    rw [(Cubic.ToricHeights.CanonicalHeight.«prop:canonicalHeight»).2 Q.val Q.property,
      Complex.ofReal_inj, ha] at h1
    rw [← h1, toricHeight, traceOneCubic_coeff_one]
    push_cast
    rfl
  rw [← hroot, ← htoric]
  exact hQs.bounds H hH

theorem bounded_eq (H : ℝ) (hH : 0 ≤ H) :
    boundedPolynomials H = countSet (Real.sqrt (1 + 3 * H ^ 2)) := by
  ext f
  constructor
  · rintro ⟨hf, hle⟩
    exact ⟨hf, (rootHeight_le_iff hf H hH).mp hle⟩
  · rintro ⟨hf, hle⟩
    exact ⟨hf, (rootHeight_le_iff hf H hH).mpr hle⟩

open Cubic.Counting.AsymptoticConstantsData Cubic.Counting.AsymptoticConstantScaling in
/-- `thm:asymptoticPolynomialCount` from `eqn:irrPolys`. The paper: "By Lemma
`lemma:rootVsToric`, the condition `h(f) ≤ H` is equivalent to `H(f) ≤ √X` with
`X = 3H²+1`. For this choice, `X log X = 6H² log H + 3H² log 3 + O(log H)`.
Substituting in `eqn:irrPolys`, with `ε/2` in place of `ε`, gives …" -/
theorem of_irrPolys
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hIrr : CubicTargets.Counting.IrrPolys.CoefficientClaim) :
    CubicTargets.Counting.AsymptoticPolynomialCount.Claim := by
  obtain ⟨Z, F, γ, c₂, c₁, hE⟩ := Cubic.PoissonSummation.leadingTerms_expansion hPoisson
  refine ⟨Z, γ, originalLeading, originalLeading * originalSecondaryRatio,
    AsymptoticConstants.eulerKronecker hE,
    AsymptoticConstantsAssembly.constants_of_continuation (AsymptoticConstants.eulerKronecker hE),
    ⟨PolynomialCountFiniteness.boundedPolynomials_finite, fun ε hε => ?_⟩⟩
  obtain ⟨K, X₀, hK⟩ := hIrr Z F γ c₂ c₁ hE (ε / 2) (by linarith)
  obtain ⟨K₃, hK₃⟩ := (AsymptoticHeightShift.main_term_height_shift c₂ c₁).bound
  set E : ℝ := 1 + ε with hEdef
  apply IsBigO.of_bound (|K| * 4 ^ (1 / 2 + ε / 2) + |K₃|)
  filter_upwards [hK₃, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.sqrt |X₀|)]
    with H hshift hH1 hHX
  have hH0 : 0 ≤ H := by linarith
  set X : ℝ := 1 + 3 * H ^ 2 with hX
  have hX4 : X ≤ 4 * H ^ 2 := by nlinarith
  have hXX₀ : X₀ ≤ X := by
    have h1 : |X₀| ≤ H ^ 2 := by
      calc |X₀| = Real.sqrt |X₀| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
        _ ≤ H ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hHX 2
    have := le_abs_self X₀
    nlinarith
  obtain ⟨-, e1⟩ := hK X hXX₀
  have hmain := AsymptoticConstantsAssembly.root_main_term hE H
  -- `lemma:rootVsToric`: the root-height count is the toric count at `√X`
  have hcount : (polynomialCount H : ℂ) =
      (Nat.card (countSet (Real.sqrt X)) : ℂ) := by
    rw [polynomialCount, bounded_eq H hH0]
  set M : ℂ := c₂ / 8 * X * Real.log X +
    (c₁ / 4 - c₂ / 8 - ((Real.pi / (9 * Real.sqrt 3) : ℝ) : ℂ)) * X with hM
  have hMt : M = toricPolynomialMainTerm c₂ c₁ (3 * H ^ 2 + 1) := by
    rw [hM, toricPolynomialMainTerm, show 3 * H ^ 2 + 1 = X by rw [hX]; ring]
    push_cast
    ring
  have hid : (((polynomialCount H : ℝ) -
      (originalLeading * H ^ 2 * Real.log H +
        (originalLeading * Real.log (Real.sqrt 3) + originalLeading * originalSecondaryRatio -
          Real.pi / (3 * Real.sqrt 3)) * H ^ 2) : ℝ) : ℂ) =
      ((Nat.card (countSet (Real.sqrt X)) : ℂ) - M) +
        (toricPolynomialMainTerm c₂ c₁ (3 * H ^ 2 + 1) - rootPolynomialMainTerm c₂ c₁ H) := by
    rw [Complex.ofReal_sub, ← hmain, Complex.ofReal_natCast, hcount, hMt]
    ring
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hH0 _), ← Complex.norm_real, hid]
  have b1 : ‖(Nat.card (countSet (Real.sqrt X)) : ℂ) - M‖ ≤ |K| * 4 ^ (1 / 2 + ε / 2) * H ^ E := by
    have hXe : X ^ (1 / 2 + ε / 2) ≤ 4 ^ (1 / 2 + ε / 2) * H ^ E := by
      calc X ^ (1 / 2 + ε / 2) ≤ (4 * H ^ 2) ^ (1 / 2 + ε / 2) :=
            Real.rpow_le_rpow (by positivity) hX4 (by linarith)
        _ = 4 ^ (1 / 2 + ε / 2) * H ^ E := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul hH0, hEdef]
            congr 2; push_cast; ring
    calc _ ≤ K * X ^ (1 / 2 + ε / 2) := e1
      _ ≤ |K| * (4 ^ (1 / 2 + ε / 2) * H ^ E) :=
          mul_le_mul (le_abs_self K) hXe (by positivity) (abs_nonneg K)
      _ = _ := by ring
  have b3 : ‖toricPolynomialMainTerm c₂ c₁ (3 * H ^ 2 + 1) - rootPolynomialMainTerm c₂ c₁ H‖ ≤
      |K₃| * H ^ E := by
    refine hshift.trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hH1)]
    have hHle : H ≤ H ^ E := by
      calc H = H ^ (1 : ℝ) := (Real.rpow_one H).symm
        _ ≤ H ^ E := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    have hlog : Real.log H ≤ H ^ E :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact mul_le_mul (le_abs_self K₃) hlog (Real.log_nonneg hH1) (abs_nonneg _)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ |K| * 4 ^ (1 / 2 + ε / 2) * H ^ E + |K₃| * H ^ E := add_le_add b1 b3
    _ = (|K| * 4 ^ (1 / 2 + ε / 2) + |K₃|) * H ^ E := by ring

/-- `thm:asymptoticPolynomialCount`, relative to the two black-box hypotheses:
the Poisson summation input `PoissonWithDualMeasure.BlackBox` and
[Chandrasekharan–Narasimhan, Math. Ann. 152 (1963), Theorem 4]. -/
theorem «thm:asymptoticPolynomialCount»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.AsymptoticPolynomialCount.Claim :=
  of_irrPolys hPoisson (Cubic.Counting.IrrPolys.coefficient_estimate hPoisson hCN)

end Cubic.Counting.AsymptoticPolynomialCount
