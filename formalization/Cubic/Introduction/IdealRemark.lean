import Cubic.Introduction.IdealSharpCount

/-! The introductory series identity and the separately cited sharper
counting argument. The main toric proofs have no dependency on this input. -/

namespace Cubic.Introduction.IdealRemark

theorem «rem:idealParametrization»
    (hKN : CubicTargets.Introduction.KuehleitnerNowakCubeIdealSum.BlackBox) :
    CubicTargets.Introduction.IdealRemark.Claim := by
  have h := IdealParametrization.arithmetic_claim
  exact ⟨{
    fullAffine := h.fullAffine
    idealCondition := h.idealCondition
    pointSeries_absolute := h.pointSeries_absolute
    idealSeries_absolute := h.idealSeries_absolute
    series := h.series }, IdealSharpCount.claim hKN⟩

end Cubic.Introduction.IdealRemark
