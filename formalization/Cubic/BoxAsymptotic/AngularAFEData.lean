import Cubic.BoxAsymptotic.HeckeCosineWeights
import Cubic.BoxAsymptotic.HeckeWeightedSeries
import Cubic.BoxAsymptotic.WeightedBlockBound

/-! The properties of the AFE used in the moment argument.  The weight family
is a variable here; no choice of auxiliary function is part of these properties.
The primitive functions are tied to their actual ideal Dirichlet series. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularAFEData

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.HeckePrimitiveCharacters Cubic.BoxAsymptotic.HeckeSeriesConvergence
open Cubic.BoxAsymptotic.HeckeCosineAFE Cubic.BoxAsymptotic.HeckeCosineWeights
open Cubic.BoxAsymptotic.WeightedBlockBound Cubic.BoxAsymptotic.HeckeWeightedSeries
open Cubic.BoxAsymptotic.IdealAngularData
open Cubic.Analysis.GammaAFEData

def Continuation (L : ℤ → ℂ → ℂ) : Prop :=
  ∀ k : ℤ, Even k → 2 ≤ k → Differentiable ℂ (L k) ∧
    ∀ s : ℂ, 1 < s.re → L k s = LSeries (coefficient (primitiveHom k)) s

/-- The coefficients in the AFE are the root numbers of the same primitive
Hecke functions, with the completion normalized as in the manuscript. -/
def RootNumbers (L : ℤ → ℂ → ℂ) (ε : ℤ → ℂ) : Prop :=
  ∀ k : ℤ, Even k → 2 ≤ k → ∃ Λ : ℂ → ℂ,
    Differentiable ℂ Λ ∧
    (∀ s : ℂ, 0 < s.re →
      Λ s = completedFactor (conductorScale k) (gammaShift k) s * L k s) ∧
    (∀ s : ℂ, Λ s = ε k * star (Λ (1 - star s)))

/-- The separate bounds in `Control` are equivalent to the two displayed sum
bounds in the manuscript: add them in one direction, or discard a nonnegative
summand in the other. All constants are uniform in the same parameters. -/
def WeightBounds (V : ℤ → ℂ → ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ), Even k → 2 ≤ k → ∀ u : ℂ,
    1 / 4 ≤ u.re → u.re ≤ 3 / 4 → Control (V k u) (modeLength k u) C

def Equations (L : ℤ → ℂ → ℂ) (V : ℤ → ℂ → ℝ → ℂ) (ε : ℤ → ℂ) : Prop :=
  ∀ k : ℤ, Even k → 2 ≤ k → ‖ε k‖ = 1 ∧
    ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 4 →
      Summable (fun I : Ideal Integers => ‖term (primitivePsi k) s (V k s) I‖) ∧
      Summable (fun I : Ideal Integers => ‖term (fun I => star (primitivePsi k I))
        (1 - s) (V k (1 - s)) I‖) ∧
      L k s = (∑' I : Ideal Integers, term (primitivePsi k) s (V k s) I) +
        dualFactor (conductorScale k) (gammaShift k) (ε k) s *
          ∑' I : Ideal Integers, term (fun I => star (primitivePsi k I)) (1 - s) (V k (1 - s)) I

def PrefactorBounds (ε : ℤ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ, Even k → 2 ≤ k → ∀ s : ℂ,
    1 / 2 ≤ s.re → s.re ≤ 3 / 4 →
      ‖dualFactor (conductorScale k) (gammaShift k) (ε k) s‖ ≤
        C * modeLength k s ^ (1 - 2 * s.re)

end Cubic.BoxAsymptotic.AngularAFEData
