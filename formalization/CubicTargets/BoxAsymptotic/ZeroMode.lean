import Cubic.BoxAsymptotic.ZeroModeData
import Mathlib.Analysis.Asymptotics.Defs

/-! Faithful target for `eq:F0`, including agreement with the actual angular mass series
and the Laurent expansion of its continuation. -/

noncomputable section

namespace CubicTargets.BoxAsymptotic

open Cubic.BoxAsymptotic.ZeroModeData Filter Asymptotics
open scoped Topology

def ZeroModeClaim : Prop :=
  (∀ s : ℂ, 1 < s.re →
    LSeriesSummable (fun n => (mass n : ℂ)) s ∧ series s = continuation s) ∧
  numerator 1 = (aStar : ℂ) ∧ deriv numerator 1 = (b₀ : ℂ) ∧
  (fun s : ℂ => continuation s - (aStar : ℂ) / (s - 1) ^ 2 - (b₀ : ℂ) / (s - 1))
    =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ))

end CubicTargets.BoxAsymptotic
