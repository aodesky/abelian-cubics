import Cubic.BoxAsymptotic.AngularSieveData

/-! The full concrete target `lem:angularLargeSieve`, including conjugate
characters and inclusion of ideals over three in the unramified residue class.
Constants are uniform in the coefficients, cutoff and frequency parameters. -/

noncomputable section

namespace CubicTargets.BoxAsymptotic

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.IdealAngularData
open Cubic.BoxAsymptotic.AngularSieveData

def AngularLargeSieveClaim : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (K Y : ℝ), 2 ≤ K → 2 ≤ Y →
    ∀ (r : ℤ), r ∈ ({0, 2, 4} : Finset ℤ) →
    ∀ (a : Ideal Integers → ℂ),
      (∀ I ∈ idealBall Y, ‖a I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) →
    ((∑ k ∈ residueModes K r, maximal (psi k) a Y ^ 2) ≤
      C * (K + Y) * Real.log (2 * Y) ^ 5) ∧
    ((∑ k ∈ residueModes K r, maximal (conjugate (psi k)) a Y ^ 2) ≤
      C * (K + Y) * Real.log (2 * Y) ^ 5) ∧
    (r = 0 →
      ((∑ k ∈ residueModes K r, maximal (primitivePsi k) a Y ^ 2) ≤
        C * (K + Y) * Real.log (2 * Y) ^ 5) ∧
      ((∑ k ∈ residueModes K r, maximal (conjugate (primitivePsi k)) a Y ^ 2) ≤
        C * (K + Y) * Real.log (2 * Y) ^ 5))

end CubicTargets.BoxAsymptotic
