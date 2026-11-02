import Cubic.Counting.IntegralPointCountData
import Cubic.Counting.EulerKroneckerCalculation
import Cubic.Counting.GeneralMonicData
import Cubic.Counting.MonicConstantsData
import CubicTargets.Counting.AsymptoticPolynomialCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Targets for the count of all monic abelian cubics

The labels are those of the section on all monic cubics and of the main theorem
`thm:generalMonicCount` in the paper. The objects are defined in
`Cubic.Counting.GeneralMonicData` and `Cubic.Counting.MonicConstantsData`. Every count comes with a finiteness statement, so that
`Nat.card` is never applied to an infinite set.
-/

noncomputable section

namespace CubicTargets.Counting.GeneralMonic

open Polynomial Filter Asymptotics Cubic.Counting.PolynomialCountData
open Cubic.Counting.GeneralMonicData
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials

/-- The asymptotic shape `main + O_ε(X^{1/2+ε})` used by the equations below. -/
def HasExpansion (F : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    |F X - (a * X * Real.log X + b * X)| ≤ K * X ^ (1 / 2 + ε)

/-- `eqn:dSummatoryForGeneralTrace`:
`Σ_{n ≤ X} d_n = (C/3) X log X + (2D/3) X + O_ε(X^{1/2+ε})`. -/
def DSummatoryCoefficients : Prop :=
  HasExpansion (fun X => ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (d n : ℝ)) (Cconst / 3) (2 * Dconst / 3)

/-- `eqn:A1asymptotic`:
`A₁(X) = (C/6) X log X + (D/3 − π/(9√3)) X + O_ε(X^{1/2+ε})`. -/
def A1Coefficients : Prop :=
  (∀ X : ℝ, (traceOneSet X).Finite) ∧
    HasExpansion (fun X => (A₁ X : ℝ)) (Cconst / 6)
      (Dconst / 3 - Real.pi / (9 * Real.sqrt 3))

open scoped Classical in
/-- `lemma:traceZeroCoefficients`: for `N = 3^e M ≥ 1` with `3 ∤ M`, `r(N) = d_M` if `e = 0`,
and `r(N) = 3 d_M + 1_{N = 3u² for some u > 0}` if `e ≥ 1`. -/
def TraceZeroCoefficientsClaim : Prop :=
  ∀ (e M : ℕ), 0 < M → ¬ 3 ∣ M →
    (squareSet ((3 ^ e * M : ℕ) : ℤ)).Finite ∧
      (r ((3 ^ e * M : ℕ) : ℤ) : ℤ) =
        if e = 0 then (d M : ℤ)
        else 3 * (d M : ℤ) +
          if ∃ u : ℤ, 0 < u ∧ ((3 ^ e * M : ℕ) : ℤ) = 3 * u ^ 2 then 1 else 0

/-- `prop:traceZeroAsymptotic`:
`A₀(X) = (5C/6) X log X + (5D/3 − (3C/4) log 3 − π/(3√3)) X + O_ε(X^{1/2+ε})`. -/
def TraceZeroAsymptoticCoefficients : Prop :=
  (∀ X : ℝ, (traceZeroSet X).Finite) ∧
    HasExpansion (fun X => (A₀ X : ℝ)) (5 * Cconst / 6)
      (5 * Dconst / 3 - 3 * Cconst / 4 * Real.log 3 - Real.pi / (3 * Real.sqrt 3))

/-- The substitution `x ↦ εx − m` on roots, as a map of monic cubics: the characteristic
polynomial of `εx − m` is `ε³ f(ε(t + m)) = ε f(ε(t + m))` for `ε = ±1`. -/
def signTranslate (ε m : ℤ) (f : ℤ[X]) : ℤ[X] := C ε * f.comp (C ε * (X + C m))

/-- `lemma:generalHeightReduction`. -/
def GeneralHeightReductionClaim : Prop :=
  (∀ f ∈ monicCyclic, 0 < invariant f ∧
    ∀ H : ℝ, weightedHeight f ≤ H ↔
      |(trace f : ℝ)| ≤ H ∧ (invariant f : ℝ) ≤ (trace f : ℝ) ^ 2 + 3 * H ^ 2) ∧
  -- (1) traces not divisible by 3: translation and, if necessary, `t ↦ -t`
  (∀ s n ε : ℤ, ¬ 3 ∣ s → (ε = 1 ∨ ε = -1) → ε * s ≡ 1 [ZMOD 3] →
    Set.BijOn (signTranslate ε ((ε * s - 1) / 3))
      {f | f ∈ monicCyclic ∧ trace f = s ∧ invariant f = n}
      {g | g ∈ cyclicPolynomials ∧ 1 - 3 * g.coeff 1 = n}) ∧
  -- (2) traces divisible by 3: translation to trace zero, with `n = 3N` and `N ∈ ℤ`
  (∀ s n : ℤ, 3 ∣ s →
    Set.BijOn (signTranslate 1 (s / 3))
      {f | f ∈ monicCyclic ∧ trace f = s ∧ invariant f = n}
      {g | ∃ N c : ℤ, n = 3 * N ∧ g = monicCubic 0 (-N) c ∧
        HasCyclicCubicGaloisGroup (g.map (Int.castRingHom ℚ))})

/-- `eqn:generalTraceDecomposition`: the count splits over the trace `s`. -/
def GeneralTraceDecompositionClaim : Prop :=
  ∀ H : ℝ, (generalSet H).Finite ∧
    Nat.card (generalSet H) =
      (∑ s ∈ (Finset.Icc (-⌊H⌋) ⌊H⌋).filter (fun s => ¬ 3 ∣ s),
          A₁ (3 * H ^ 2 + (s : ℝ) ^ 2)) +
        ∑ s ∈ (Finset.Icc (-⌊H⌋) ⌊H⌋).filter (fun s => 3 ∣ s),
          A₀ (H ^ 2 + (s : ℝ) ^ 2 / 3)

open Cubic.Counting.MonicConstantsData Cubic.PoissonSummation.LeadingTermsData
open Cubic.PoissonSummation.FiniteEulerProduct
open CubicTargets.Counting.AsymptoticPolynomialCount (EulerKronecker)
open scoped Topology

/-- `eqn:monicArchimedeanFactor` in the companion constants note:
`V(z) = ∫_{-1}^{1} (3+u²)^z du` is defined for every
`z ∈ ℂ`, i.e. the integrand is integrable on `[-1, 1]`. -/
def MonicArchimedeanFactorClaim : Prop :=
  ∀ z : ℂ, IntervalIntegrable (fun u : ℝ => (((3 + u ^ 2 : ℝ)) : ℂ) ^ z)
    MeasureTheory.volume (-1) 1

/-- `eqn:monicArchimedeanMoments`: the two definite integrals used when summing
over the trace. -/
def MonicArchimedeanMomentsClaim : Prop :=
  (∫ u in (-1 : ℝ)..1, (3 + u ^ 2)) = 20 / 3 ∧
    ∫ u in (-1 : ℝ)..1, (3 + u ^ 2) * Real.log (3 + u ^ 2) =
      40 / 3 * Real.log 2 + 4 * Real.pi * Real.sqrt 3 / 3 - 76 / 9

/-- The trace-count coefficients in the proof of `thm:generalMonicCount`, before
`eqn:monicArchimedeanMoments` is used: `C_mon = 2V(1)((2/3)(C/6) + (1/9)(5C/6))`. -/
def traceCountLeading : ℂ :=
  2 * archimedeanFactor 1 * (2 / 3 * ((Cconst : ℂ) / 6) + 1 / 9 * (5 * (Cconst : ℂ) / 6))

/-- `D_mon = (2/3)[(C/6)V'(1) + (D/3 − π/(9√3))V(1)]
  + (1/9)[(5C/6)(V'(1) − V(1) log 3) + (5D/3 − (3C/4) log 3 − π/(3√3))V(1)]`. -/
def traceCountSecondary : ℂ :=
  2 / 3 * ((Cconst : ℂ) / 6 * deriv archimedeanFactor 1 +
      ((Dconst : ℂ) / 3 - (Real.pi : ℂ) / (9 * (Real.sqrt 3 : ℂ))) * archimedeanFactor 1) +
    1 / 9 * (5 * (Cconst : ℂ) / 6 *
        (deriv archimedeanFactor 1 - archimedeanFactor 1 * (Real.log 3 : ℂ)) +
      (5 * (Dconst : ℂ) / 3 - 3 * (Cconst : ℂ) / 4 * (Real.log 3 : ℂ) -
        (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ))) * archimedeanFactor 1)

/-- `eqn:monicConstantsFromTraceCounts`: the trace-count coefficients are `C_mon = (220/81)C`
and `D_mon = C_mon(D/C + log 2 − (19/44) log 3 − 19/30 + π√3/10) − 20π√3/81`. -/
def TraceCountCoefficientsClaim : Prop :=
  traceCountLeading = 220 / 81 * (Cconst : ℂ) ∧
    traceCountSecondary = traceCountLeading *
      ((Dconst : ℂ) / (Cconst : ℂ) + (Real.log 2 : ℂ) - 19 / 44 * (Real.log 3 : ℂ) - 19 / 30 +
        (Real.pi : ℂ) * (Real.sqrt 3 : ℂ) / 10) -
      20 * (Real.pi : ℂ) * (Real.sqrt 3 : ℂ) / 81

/-- `C_mon = (220/243) ∏_{p≡1 (3)} (1 − 2/(p(p+1)))`, as displayed in `thm:generalMonicCount`. -/
def monicLeading : ℂ := 220 / 243 * splitProductAtTwo

/-- `D_mon`, as displayed in `thm:generalMonicCount`, in terms of `γ_E`. -/
def monicSecondary (γ : ℂ) : ℂ :=
  monicLeading * (γ - deriv riemannZeta 2 / riemannZeta 2 + ∑' p : SplitPrimes, splitLogTerm p +
      (Real.log 2 : ℂ) - 5 / 88 * (Real.log 3 : ℂ) +
      (Real.pi : ℂ) * (Real.sqrt 3 : ℂ) / 10 - 17 / 15) -
    20 * (Real.pi : ℂ) * (Real.sqrt 3 : ℂ) / 81

/-- `thm:generalMonicCount`. `Z` is a continuation of `ζ_E` and `γ` its Euler–Kronecker
constant, as in the paper's definition of `γ_E`. -/
def GeneralMonicCountClaim : Prop :=
  ∃ (Z : ℂ → ℂ) (γ : ℂ) (Cm Dm : ℝ), EulerKronecker Z γ ∧
    (Cm : ℂ) = monicLeading ∧ (Dm : ℂ) = monicSecondary γ ∧
    (∀ H : ℝ, (generalSet H).Finite) ∧
    ∀ ε : ℝ, 0 < ε →
      (fun H : ℝ => (Nat.card (generalSet H) : ℝ) -
        (Cm * H ^ 3 * Real.log H + Dm * H ^ 3)) =O[atTop] (fun H : ℝ => H ^ (2 + ε))

/-- `eqn:monicEulerFactor`: for `Re z > 1/2` the product converges absolutely and the
prefactor is defined (`ζ(2z) ≠ 0`, `1 + 3^{-z} ≠ 0`); `𝓔_mon(1)` is real and positive. -/
def MonicEulerFactorClaim : Prop :=
  (∀ z : ℂ, (1 / 2 : ℝ) < z.re →
    riemannZeta (2 * z) ≠ 0 ∧ 1 + (3 : ℂ) ^ (-z) ≠ 0 ∧
      Summable (fun p : SplitPrimes => ‖monicSplitFactor p z - 1‖)) ∧
  (monicEulerFactor 1).im = 0 ∧ 0 < (monicEulerFactor 1).re

/-- `eqn:monicAveragedSeries`, on the region `Re z > 1` where `Z₀(z)` and `ζ_E(z)` are
given by their series. -/
def MonicAveragedSeriesClaim : Prop :=
  ∀ z : ℂ, 1 < z.re →
    (1 / 3 + (3 : ℂ) ^ (-z) * (1 + 2 * (3 : ℂ) ^ (-z)) / (3 * (1 - (3 : ℂ) ^ (-z)))) *
        heightZeta (2 * z) =
      (1 + 2 * (3 : ℂ) ^ (-(2 * z))) / (3 * (1 - (3 : ℂ) ^ (-z))) * heightZeta (2 * z) ∧
    (1 + 2 * (3 : ℂ) ^ (-(2 * z))) / (3 * (1 - (3 : ℂ) ^ (-z))) * heightZeta (2 * z) =
      NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E z ^ 2 *
        monicEulerFactor z

/-- `eqn:monicConceptualConstants`, with `ρ_E = Res_{z=1} ζ_E(z)` (mathlib's
class-number-formula residue, which the claim also evaluates as `π/(3√3)`). -/
def MonicConceptualConstantsClaim : Prop :=
  ((NumberField.dedekindZeta_residue Cubic.QuadraticCorrespondence.CyclotomicField.E : ℝ) : ℂ) =
      (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ)) ∧
  monicLeading = 2 * ((NumberField.dedekindZeta_residue
      Cubic.QuadraticCorrespondence.CyclotomicField.E : ℝ) : ℂ) ^ 2 *
      monicEulerFactor 1 * archimedeanFactor 1 ∧
  ∀ (Z : ℂ → ℂ) (γ : ℂ), EulerKronecker Z γ →
    monicSecondary γ = monicLeading / 2 * (2 * γ - 1 +
        deriv monicEulerFactor 1 / monicEulerFactor 1 +
        deriv archimedeanFactor 1 / archimedeanFactor 1) -
      (Real.pi : ℂ) / (9 * (Real.sqrt 3 : ℂ)) * archimedeanFactor 1

open Cubic.Counting.IntegralPointCountData

/-- The error estimate with the main term written as a function. -/
def HasMainTerm (F M : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    |F X - M X| ≤ K * X ^ (1 / 2 + ε)

/-- `eqn:dSummatoryForGeneralTrace`, with the manuscript's `Q`. -/
def DSummatoryClaim : Prop :=
  HasMainTerm (fun X => ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (d n : ℝ))
    (fun X => X * Q Cubic.Counting.EulerKroneckerCalculation.value (1 / 2 * Real.log X))

/-- `eqn:A1asymptotic`, with the manuscript's `Q`. -/
def A1Claim : Prop :=
  (∀ X : ℝ, (traceOneSet X).Finite) ∧
    HasMainTerm (fun X => (A₁ X : ℝ))
      (fun X => 1 / 2 * X * Q Cubic.Counting.EulerKroneckerCalculation.value
        (1 / 2 * Real.log X) - Real.pi / (9 * Real.sqrt 3) * X)

/-- `prop:traceZeroAsymptotic`, including the correction `α log 3 / 4`. -/
def TraceZeroAsymptoticClaim : Prop :=
  (∀ X : ℝ, (traceZeroSet X).Finite) ∧
    HasMainTerm (fun X => (A₀ X : ℝ))
      (fun X => 5 / 2 * X * Q Cubic.Counting.EulerKroneckerCalculation.value
        (1 / 2 * Real.log X) - (alpha / 4 * Real.log 3 + Real.pi / (3 * Real.sqrt 3)) * X)

/-- `eqn:monicConstantsFromTraceCounts`, relating the actual polynomials `P` and `Q`. -/
def MonicConstantsFromTraceCountsClaim : Prop :=
  ∀ (Z : ℂ → ℂ) (μ : ℂ), EulerKronecker Z μ → ∀ X : ℝ,
    monicLeading * (X : ℂ) + monicSecondary μ =
      ((110 / 27 * Q μ X + 220 * alpha / 243 *
        (Real.log 2 - 19 / 44 * Real.log 3 - 19 / 30 + Real.pi * Real.sqrt 3 / 10) -
          20 * Real.pi * Real.sqrt 3 / 81 : ℝ) : ℂ)

end CubicTargets.Counting.GeneralMonic
