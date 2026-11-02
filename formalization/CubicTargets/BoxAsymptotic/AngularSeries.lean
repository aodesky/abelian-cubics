import Cubic.BoxAsymptotic.AngularLocalData
import Cubic.BoxAsymptotic.AngularIdealData

/-! Concrete angular-series targets. The Fourier coefficients are independently
defined from lattice points, and `D_k` from primary generators of actual ideals.
The intermediate element formulation is stated separately. The Euler product
`eq:Dk` and analytic continuation are not assumed in these definitions. -/

noncomputable section

namespace CubicTargets.BoxAsymptotic

open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularLocalData

/-- Complete local angular coefficient table underlying `eq:Fk`. -/
def AngularCoefficientClaim : Prop :=
  ∀ (k : ℤ), Even k → ∀ (e M : ℕ), 0 < M → ¬ 3 ∣ M →
    coefficient k (3 ^ e * M) = localWeight k e * awayCoefficient k M

/-- Intermediate form of `eq:Fk`, on its original half-plane of convergence,
in primary-element coordinates. -/
def AngularLocalSeriesClaim : Prop :=
  (∀ (k : ℤ) (s : ℂ), 1 < s.re → LSeriesSummable (coefficient k) s) ∧
  (∀ (k : ℤ), Odd k → ∀ s : ℂ, series k s = 0) ∧
  ∀ (k : ℤ), Even k → ∀ s : ℂ, 1 < s.re →
    LSeriesSummable (awayCoefficient k) s ∧
    let y := (-1 : ℂ) ^ (k / 2) * (3 : ℂ) ^ (-s)
    series k s = (1 / 3 : ℂ) *
      (1 + y + 3 * (if 6 ∣ k then 1 else 0) * y ^ 2 / (1 - y)) * awaySeries k s

/-- `eq:Fk` for the actual ideal series `D_k`, on `Re s > 1`. The analytic
continuation supplied by `eq:Dk` is a separate assertion of `prop:angular`. -/
def AngularSeriesClaim : Prop :=
  (∀ (k : ℤ) (s : ℂ), 1 < s.re → LSeriesSummable (coefficient k) s) ∧
  (∀ (k : ℤ), Odd k → ∀ s : ℂ, series k s = 0) ∧
  ∀ (k : ℤ), Even k → ∀ s : ℂ, 1 < s.re →
    LSeriesSummable (Cubic.BoxAsymptotic.AngularIdealData.idealCoefficient k) s ∧
    let y := (-1 : ℂ) ^ (k / 2) * (3 : ℂ) ^ (-s)
    series k s = (1 / 3 : ℂ) *
      (1 + y + 3 * (if 6 ∣ k then 1 else 0) * y ^ 2 / (1 - y)) *
        Cubic.BoxAsymptotic.AngularIdealData.idealSeries k s

end CubicTargets.BoxAsymptotic
