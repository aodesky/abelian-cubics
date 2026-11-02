import Cubic.PoissonSummation.AdelicCompactQuotient

/-!
# Concrete full statement of `prop:Lmap`

Exactness of the specified maps, with every group fixed to the original adelic
torus. The real invariant cocharacter line uses `u v₀`; `Multiplicative` only
allows the additive codomain to use the same group-homomorphism API.
-/

namespace CubicTargets.PoissonSummation.LogarithmExactSequence

open Cubic.PoissonSummation.AdelicCompactQuotient
open scoped Cubic.QuadraticCorrespondence.RationalQuotientGroup

structure Claim : Prop where
  injective : Function.Injective compactMap
  exact : compactMap.range = quotientCoordinate.ker
  surjective : Function.Surjective quotientCoordinate

/-- The class-number-one step in the paper's proof: every finite
adele can be made a unit at every place by one global rational torus point.
Proved in `PrimePrincipalization`, separately from the statement. -/
def FinitePrincipalization : Prop :=
  ∀ x : Cubic.PoissonSummation.FiniteAdelicData.Points,
    ∃ P : Cubic.PoissonSummation.RationalAdelicEmbedding.Points,
      (Cubic.PoissonSummation.RationalAdelicEmbedding.finiteDiagonal P)⁻¹ * x ∈ finiteCompact

/-- Local generator formulation of the same arithmetic task: prescribe the
valuation at one rational prime while keeping every other component compact.
At a split prime this includes both field places above it. -/
def PrimePrincipalization : Prop :=
  ∀ (p : Nat.Primes) (x : (Cubic.PoissonSummation.QuotientFiniteFourierProduct.family p).Carrier),
    ∃ P : Cubic.PoissonSummation.RationalAdelicEmbedding.Points,
      (Cubic.PoissonSummation.RationalAdelicEmbedding.localPoint p P)⁻¹ * x ∈
        (Cubic.PoissonSummation.QuotientFiniteFourierProduct.family p).maxCompact ∧
      ∀ q : Nat.Primes, q ≠ p →
        Cubic.PoissonSummation.RationalAdelicEmbedding.localPoint q P ∈
          (Cubic.PoissonSummation.QuotientFiniteFourierProduct.family q).maxCompact

end CubicTargets.PoissonSummation.LogarithmExactSequence
