import Cubic.PoissonSummation.PrimePrincipalization
import Cubic.PoissonSummation.AdelicPrincipalizationConsequences

/-!
# `prop:Lmap`: the adelic logarithm exact sequence

The original rational product formula defines the quotient logarithm. The
class-number-one calculation principalizes every finite valuation, so a
norm-one class has a compact representative. The infinite radial section
supplies surjectivity. The compact subgroup is quotiented by its actual
rational intersection, which supplies injectivity on the left.
-/

namespace Cubic.PoissonSummation

theorem «prop:Lmap» : CubicTargets.PoissonSummation.LogarithmExactSequence.Claim :=
  AdelicPrincipalizationConsequences.logarithmExactSequence_of_finitePrincipalization
    PrimePrincipalization.finitePrincipalization

end Cubic.PoissonSummation
