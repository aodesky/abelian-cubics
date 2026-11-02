import Cubic.BoxAsymptotic.PrimitiveHeckeMoment
import Cubic.BoxAsymptotic.AngularMomentAssembly

/-! `lem:moment`: both angular moment estimates for the original arithmetic
series and their analytic continuations. All remaining assumptions are the
explicitly cited general analytic inputs; no moment estimate is assumed.

The primitive moment invokes `lem:angularAFE` and uses only the resulting
weight estimates and exact identity, as does the manuscript. The angular
series converge by the direct divisor majorant and Euler-product argument.
-/

namespace Cubic.BoxAsymptotic.AngularMoment

/-- The full `lem:moment`, including the even Hecke second moment, both signs
and all angular modes in the first moment, and constants uniform in every
displayed parameter. The constructed estimate allows the absolute exponent 6. -/
theorem «lem:moment»
    (hLS : CubicTargets.BoxAsymptotic.AdditiveLargeSieve.BlackBox)
    (hRM : CubicTargets.BoxAsymptotic.BinaryDecomposition.BlackBox)
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    (hAFE : CubicTargets.BoxAsymptotic.GammaAFE.Identity)
    (hWeights : CubicTargets.BoxAsymptotic.GammaAFE.Weights)
    (hGamma : CubicTargets.BoxAsymptotic.GammaAFE.GammaRatio) :
    CubicTargets.BoxAsymptotic.AngularMomentClaim := by
  obtain ⟨C, hC, hsecond⟩ := PrimitiveHeckeMoment.bound hHecke hLS hRM hAFE hWeights hGamma
  exact AngularMomentAssembly.of_primitive_second hHecke hC hsecond

end Cubic.BoxAsymptotic.AngularMoment
