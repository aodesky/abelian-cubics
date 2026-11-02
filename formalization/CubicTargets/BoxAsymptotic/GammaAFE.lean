import Cubic.Analysis.GammaAFEData

/-! Explicit literature inputs from Iwaniec--Kowalski, Theorem 5.3,
Proposition 5.4, and Appendix 5.A.4. These are generic Gamma-factor statements,
not the paper's AFE or moment bound. The cosine auxiliary function is fixed
in the mathematical definition and is the one used in the manuscript
proof of `lem:angularAFE`. See `targets/boxAnalyticInputs.md` for normalizations.
-/

namespace CubicTargets.BoxAsymptotic.GammaAFE

open Cubic.Analysis.GammaAFEData

/-- Theorem 5.3 with `X=1` and no polar term. The sums still have the original
Dirichlet coefficients and the dual coefficients are complex conjugates. -/
def Identity : Prop :=
  ∀ (a : ℕ → ℂ) (Q κ : ℝ) (L Λ : ℂ → ℂ) (ε : ℂ),
    0 < Q → 1 ≤ κ → AnalyticData a Q κ L Λ ε →
    ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 4 →
      Summable (fun n => ‖weightedTerm a Q κ s n‖) ∧
      Summable (fun n => ‖weightedTerm (fun n => star (a n)) Q κ (1 - s) n‖) ∧
      L s = (∑' n, weightedTerm a Q κ s n) + dualFactor Q κ ε s *
        ∑' n, weightedTerm (fun n => star (a n)) Q κ (1 - s) n

/-- Proposition 5.4 with derivative orders zero and one, `α=1/4`, `A=3`,
and degree two. The scale is the actual textbook analytic conductor. -/
def Weights : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Q κ : ℝ) (u : ℂ),
    0 < Q → 1 ≤ κ → 1 / 4 ≤ u.re → u.re ≤ 3 / 4 →
      DifferentiableOn ℝ (weight Q κ u) (Set.Ioi 0) ∧
      ContinuousOn (deriv (weight Q κ u)) (Set.Ioi 0) ∧
      (∀ x > 0, ‖weight Q κ u x - 1‖ ≤ C * (x / length Q κ u) ^ (1 / 4 : ℝ)) ∧
      (∀ x > 0, x * ‖deriv (weight Q κ u) x‖ ≤ C * (x / length Q κ u) ^ (1 / 4 : ℝ)) ∧
      (∀ x > 0, ‖weight Q κ u x‖ ≤ C * (1 + x / length Q κ u) ^ (-(3 : ℝ))) ∧
      (∀ x > 0, x * ‖deriv (weight Q κ u) x‖ ≤ C * (1 + x / length Q κ u) ^ (-(3 : ℝ)))

/-- The uniform horizontal Gamma-quotient bound supplied by Stirling's formula
in the right half-plane, Appendix 5.A.4, (5.112)--(5.116). There is no finite
conductor or Hecke family in this statement. -/
def GammaRatio : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (κ : ℝ) (s : ℂ),
    1 ≤ κ → 1 / 2 ≤ s.re → s.re ≤ 3 / 4 →
      ‖Complex.Gamma (1 - s + κ) / Complex.Gamma (s + κ)‖ ≤
        C * (1 + κ + |s.im|) ^ (1 - 2 * s.re)

end CubicTargets.BoxAsymptotic.GammaAFE
