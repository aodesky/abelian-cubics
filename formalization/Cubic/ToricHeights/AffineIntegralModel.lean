import Cubic.ToricHeights.DescendedCyclicInvariant
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Integer polynomial restrictions on the original affine cover

The original universal cover has trace-one coordinates `X/ε`, `Y/ε`, `Z/ε`.
Their integral polynomial algebra gives the restrictions of functions on the
affine trace-one chart. Its intersection with the rational cyclic fixed ring
is an auxiliary algebra of invariant polynomial restrictions. Taking invariants
is not assumed to commute with restriction: `AffineInvariantRing` defines the
invariant polynomials before restricting, and compares their values.

Integrality of a rational point means that every such function is integer
valued.
-/

noncomputable section

namespace Cubic.ToricHeights.AffineIntegralModel

open Cubic.QuadraticCorrespondence
open CyclotomicTorusGalois DescendedCoefficients DescendedCyclicInvariant

/-- All integer polynomial functions in the original trace-one cover coordinates. -/
def affineCoverFunctions : Subalgebra ℤ CoverRing :=
  Algebra.adjoin ℤ (Set.range coverCoordinate)

theorem coverCoordinate_mem (i : ZMod 3) : coverCoordinate i ∈ affineCoverFunctions :=
  Algebra.subset_adjoin ⟨i, rfl⟩

/-- Integral polynomial functions fixed by the original cyclic and rational descent actions. -/
def affineFunctions : Subalgebra ℤ quotientFixedRing :=
  affineCoverFunctions.comap (quotientFixedRing.val.restrictScalars ℤ)

theorem mem_affineFunctions (f : quotientFixedRing) :
    f ∈ affineFunctions ↔ (f : CoverRing) ∈ affineCoverFunctions := Iff.rfl

theorem linearCoefficient_mem : linearCoefficient ∈ affineFunctions := by
  change coverLinearCoefficient ∈ affineCoverFunctions
  unfold coverLinearCoefficient Cubic.OrbitParametrization.secondCoeff
  exact affineCoverFunctions.add_mem
    (affineCoverFunctions.add_mem (affineCoverFunctions.mul_mem (coverCoordinate_mem 0)
      (coverCoordinate_mem 1)) (affineCoverFunctions.mul_mem (coverCoordinate_mem 1)
      (coverCoordinate_mem 2)))
    (affineCoverFunctions.mul_mem (coverCoordinate_mem 2) (coverCoordinate_mem 0))

theorem constantCoefficient_mem : constantCoefficient ∈ affineFunctions := by
  change coverConstantCoefficient ∈ affineCoverFunctions
  unfold coverConstantCoefficient Cubic.OrbitParametrization.constantCoeff
  exact affineCoverFunctions.neg_mem (affineCoverFunctions.mul_mem
    (affineCoverFunctions.mul_mem (coverCoordinate_mem 0) (coverCoordinate_mem 1))
    (coverCoordinate_mem 2))

theorem delta_mem : delta ∈ affineFunctions := by
  change coverDelta ∈ affineCoverFunctions
  unfold coverDelta
  exact affineCoverFunctions.add_mem
    (affineCoverFunctions.add_mem
      (affineCoverFunctions.mul_mem (affineCoverFunctions.pow_mem (coverCoordinate_mem 0) 2)
        (coverCoordinate_mem 1))
      (affineCoverFunctions.mul_mem (affineCoverFunctions.pow_mem (coverCoordinate_mem 1) 2)
        (coverCoordinate_mem 2)))
    (affineCoverFunctions.mul_mem (affineCoverFunctions.pow_mem (coverCoordinate_mem 2) 2)
      (coverCoordinate_mem 0))

/-- Integrality on the auxiliary algebra of invariant polynomial restrictions. -/
def IntegralPoint (P : quotientFixedRing →ₐ[ℚ] ℚ) : Prop :=
  ∀ f : affineFunctions, ∃ z : ℤ, P f.val = (z : ℚ)

theorem coefficients_of_integralPoint (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (hP : IntegralPoint P) :
    (∃ a : ℤ, P linearCoefficient = (a : ℚ)) ∧
      (∃ b : ℤ, P constantCoefficient = (b : ℚ)) :=
  ⟨hP ⟨_, linearCoefficient_mem⟩, hP ⟨_, constantCoefficient_mem⟩⟩

end Cubic.ToricHeights.AffineIntegralModel
