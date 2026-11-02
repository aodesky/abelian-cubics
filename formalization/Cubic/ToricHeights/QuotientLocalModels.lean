import Cubic.QuadraticCorrespondence.QuotientLocalTopology
import Cubic.ToricHeights.SplitQuotientLogarithm
import Cubic.ToricHeights.InertQuotientLogarithm
import Cubic.ToricHeights.RamifiedQuotientLogarithm

/-!
# Topological comparisons with the finite Fourier groups

The original quotient-point parametrizations used for the local logarithms and
integrality formulas are topological group isomorphisms. The source topology
is defined by regular-function evaluation. The targets carry the local-field
topologies of the split, inert and ramified models, also used for their Haar
measures.
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientLocalModels

open Cubic.QuadraticCorrespondence
open CyclotomicTorusGalois
open scoped RegularFunctionTopology RationalQuotientGroup CyclotomicBaseChange
  CyclotomicTensorTopology

variable (p : ℕ) [Fact p.Prime]

/-- The original quotient at a split prime is the product of the two local unit groups. -/
def splitEquiv [Fact (p % 3 = 1)] :
    (quotientFixedRing →ₐ[ℚ] ℚ_[p]) ≃ₜ* SplitLocalModel.Points p :=
  ((QuotientLocalTopology.quotientRestrictionScalarsContinuousMulEquiv ℚ_[p]).trans
    (CyclotomicTensorTopology.commUnitsEquiv ℚ_[p])).trans
      (CyclotomicBaseChange.padicUnitsEquiv p Fact.out)

@[simp]
theorem splitEquiv_apply [Fact (p % 3 = 1)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    splitEquiv p P = SplitQuotientLogarithm.localPoint p P := by
  apply Prod.ext <;> apply Units.ext <;> rfl

/-- The original quotient at an inert prime is the quadratic local unit group. -/
def inertEquiv [Fact (p % 3 = 2)] :
    (quotientFixedRing →ₐ[ℚ] ℚ_[p]) ≃ₜ* InertLocalModel.Points p :=
  ((QuotientLocalTopology.quotientRestrictionScalarsContinuousMulEquiv ℚ_[p]).trans
    (CyclotomicTensorTopology.commUnitsEquiv ℚ_[p])).trans
      (CyclotomicInertField.tensorUnitsEquiv p)

@[simp]
theorem inertEquiv_apply [Fact (p % 3 = 2)] (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    inertEquiv p P = InertQuotientLogarithm.localPoint p P := by
  apply Units.ext
  rfl

/-- The original quotient at three is the ramified cyclotomic unit group. -/
def ramifiedEquiv :
    (quotientFixedRing →ₐ[ℚ] ℚ_[3]) ≃ₜ* RamifiedLocalModel.Points :=
  ((QuotientLocalTopology.quotientRestrictionScalarsContinuousMulEquiv ℚ_[3]).trans
    (CyclotomicTensorTopology.commUnitsEquiv ℚ_[3])).trans
      CyclotomicRamifiedField.tensorUnitsEquiv

@[simp]
theorem ramifiedEquiv_apply (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ramifiedEquiv P = RamifiedQuotientLogarithm.localPoint P := by
  apply Units.ext
  rfl

end Cubic.ToricHeights.QuotientLocalModels
