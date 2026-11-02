import CubicTargets.PoissonSummation.KprimeGroup
import Cubic.PoissonSummation.AdelicLevelQuotient

/-!
# `lemma:KprimeGroup`: the logarithm coordinate on the actual double quotient

The exact sequence and six-unit reduction identify the kernel with the level
image. The radial section gives the continuous inverse, and the existing
counting-normalized quotient measure pushes to `du/6`.
-/

namespace Cubic.PoissonSummation

theorem «lemma:KprimeGroup» : CubicTargets.PoissonSummation.KprimeGroup.Claim :=
  ⟨⟨AdelicLevelQuotient.logarithmEquiv, fun _ => rfl, fun _ => rfl⟩,
    AdelicData.logarithm_radialSection, AdelicLevelQuotient.map_measure_realCoordinate⟩

end Cubic.PoissonSummation
