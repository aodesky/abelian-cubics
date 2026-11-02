import Cubic.PoissonSummation.LeadingTermsData
import Cubic.QuadraticCorrespondence.CyclotomicField
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Analysis.Meromorphic.Order

/-!
# Full concrete target for `prop:leadingTerms`

`Claim` has no data parameters or extra assumptions. It asserts the existence
of continuations of the height series and of mathlib's ideal-counting
Dedekind zeta function of the field `E = ℚ(√(-3))`.
The coefficient `γ` is characterized by the paper's punctured complex limit
of the logarithmic derivative of that continuation, not by the coefficient
ratio or by the factorization `ζ_E = ζ L(·, χ₋₃)`.

The predicate `Expansion` records all assertions of the proposition and the
arithmetic identifications used in its proof. Its parameters are existentially
quantified in `Claim`.
Convergence fields give meaning to the infinite product and prime sum even
though Lean's `tprod` and `tsum` are totalized.
-/

namespace CubicTargets.PoissonSummation.LeadingTerms

open Filter Asymptotics Cubic.PoissonSummation
open LeadingTermsData FiniteEulerProduct
open scoped Topology

structure Expansion (D F : ℂ → ℂ) (γ c₂ c₁ : ℂ) : Prop where
  /-- The continued function agrees with the ideal-counting series where it converges. -/
  dedekind_agrees : ∀ u : ℂ, 1 < u.re →
    D u = NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E u
  dedekind_meromorphic : MeromorphicOn D {u : ℂ | (1 / 2 : ℝ) < u.re}
  dedekind_analytic : ∀ u : ℂ, (1 / 2 : ℝ) < u.re → u ≠ 1 → AnalyticAt ℂ D u
  /-- The paper's definition of `γ_E`, using the continuation. -/
  euler_kronecker : Tendsto (fun u : ℂ => deriv D u / D u + 1 / (u - 1))
    (𝓝[≠] (1 : ℂ)) (𝓝 γ)
  /-- Comparison to mathlib's class-number-formula residue. -/
  dedekind_residue : Tendsto (fun u : ℂ => (u - 1) * D u)
    (𝓝[≠] (1 : ℂ))
    (𝓝 (NumberField.dedekindZeta_residue
      Cubic.QuadraticCorrespondence.CyclotomicField.E : ℂ))
  residue_value : (NumberField.dedekindZeta_residue
      Cubic.QuadraticCorrespondence.CyclotomicField.E : ℂ) =
    (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ))
  residue_L_value : DirichletCharacter.LFunction QuadraticDirichletCharacter.character 1 =
    (NumberField.dedekindZeta_residue
      Cubic.QuadraticCorrespondence.CyclotomicField.E : ℂ)
  continuation_agrees : ∀ s : ℂ, 2 < s.re → F s = heightZeta s
  meromorphic : MeromorphicOn F {s : ℂ | 1 < s.re}
  analytic_away_two : ∀ s : ℂ, 1 < s.re → s ≠ 2 → AnalyticAt ℂ F s
  pole_order : meromorphicOrderAt F 2 = (-2 : ℤ)
  /-- The paper factors the continuation by the Dedekind zeta function. -/
  factorization : ∀ s : ℂ, 1 < s.re → s ≠ 2 → F s = D (s / 2) ^ 2 * correction s
  correction_analytic : DifferentiableOn ℂ correction {s : ℂ | 1 < s.re}
  correction_real : (correction 2).im = 0
  correction_positive : 0 < (correction 2).re
  inert_absolute : ∀ s : ℂ, 1 < s.re →
    Summable (fun q : InertPrimes => ‖HeightZetaCorrectionProduct.inert q (s / 2) - 1‖)
  split_absolute : ∀ s : ℂ, 1 < s.re →
    Summable (fun p : SplitPrimes => ‖HeightZetaCorrectionProduct.split p (s / 2) - 1‖)
  laurent : (fun s : ℂ => F s - c₂ / (s - 2) ^ 2 - c₁ / (s - 2))
    =O[𝓝[≠] (2 : ℂ)] (fun _ => (1 : ℂ))
  leading_ne_zero : c₂ ≠ 0
  leading : c₂ = 4 *
    DirichletCharacter.LFunction QuadraticDirichletCharacter.character 1 ^ 2 * correction 2
  subleading : c₁ / c₂ = γ + deriv correction 2 / correction 2
  explicit_product_absolute : Summable (fun p : SplitPrimes =>
    ‖(1 - 2 / ((p.1 : ℂ) * ((p.1 : ℂ) + 1))) - 1‖)
  explicit_leading : c₂ = (4 / 9 : ℂ) * splitProductAtTwo
  explicit_sum_absolute : Summable (fun p : SplitPrimes => ‖splitLogTerm p‖)
  explicit_subleading : c₁ / c₂ = γ - deriv riemannZeta 2 / riemannZeta 2 +
    (3 / 8 : ℂ) * (Real.log 3 : ℂ) + ∑' p : SplitPrimes, splitLogTerm p

/-- `prop:leadingTerms`: the continuations and constants exist with all the properties
recorded in `Expansion`. -/
def Claim : Prop := ∃ (D F : ℂ → ℂ) (γ c₂ c₁ : ℂ), Expansion D F γ c₂ c₁

/-- The arithmetic comparison in the paper's proof. This closed statement is
proved by `QuadraticDedekindFactorization.factorization`. -/
def DedekindFactorization : Prop := ∀ u : ℂ, 1 < u.re →
  NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E u =
    riemannZeta u * DirichletCharacter.LFunction QuadraticDirichletCharacter.character u

end CubicTargets.PoissonSummation.LeadingTerms
