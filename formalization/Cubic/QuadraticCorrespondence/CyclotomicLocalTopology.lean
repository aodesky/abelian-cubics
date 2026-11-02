import Cubic.QuadraticCorrespondence.CyclotomicLocalAlgebra
import Cubic.QuadraticCorrespondence.CyclotomicBaseChange
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Group.Units

/-!
# The topology of the cyclotomic splitting

Equip the quotient algebra with its finite-dimensional module topology, before
choosing a splitting root. The splitting isomorphism is continuous in both
directions, and induces the required topological isomorphism on unit groups.
The base-change presentation gives the same conclusions for the tensor
product with the global cyclotomic field, with explicit formulas on `a + bζ`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicLocalAlgebra

section Topology

variable {K : Type*} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K]

/-- The natural finite-dimensional topology, independent of a root choice. -/
scoped instance : TopologicalSpace (Model K) := moduleTopology K (Model K)

scoped instance : IsModuleTopology K (Model K) := ⟨rfl⟩

scoped instance : IsTopologicalRing (Model K) := IsModuleTopology.isTopologicalRing K (Model K)

/-- The algebraic splitting respects the natural topology on the local algebra. -/
def splittingContinuousEquiv (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) : Model K ≃A[K] K × K where
  __ := splittingEquiv ζ hζ
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (splittingEquiv ζ hζ).toLinearMap
  continuous_invFun :=
    IsModuleTopology.continuous_of_linearMap (splittingEquiv ζ hζ).symm.toLinearMap

/-- On units, the quotient algebra's topology agrees with the product topology
used for the split local Fourier integral. -/
def splittingUnitsEquiv (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (Model K)ˣ ≃ₜ* Kˣ × Kˣ :=
  (Units.mapContinuousMulEquiv {
    __ := (splittingContinuousEquiv ζ hζ).toAlgEquiv.toMulEquiv
    __ := (splittingContinuousEquiv ζ hζ).toHomeomorph }).trans {
      __ := MulEquiv.prodUnits
      __ := Homeomorph.prodUnits }

end Topology

/-- The arithmetic split-prime criterion gives a topological unit-group
isomorphism with the concrete p-adic product model. -/
def padicUnitsEquiv (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    (Model ℚ_[p])ˣ ≃ₜ* ℚ_[p]ˣ × ℚ_[p]ˣ :=
  splittingUnitsEquiv (Classical.choose (CyclotomicLocalRoots.field_root p hp))
    (Classical.choose_spec (CyclotomicLocalRoots.field_root p hp))

end Cubic.QuadraticCorrespondence.CyclotomicLocalAlgebra

namespace Cubic.QuadraticCorrespondence.CyclotomicBaseChange

open scoped CyclotomicLocalAlgebra TensorProduct

section Topology

variable (K : Type*) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K]

/-- The local tensor algebra has its natural module topology, independently of
any choice of a local root or splitting isomorphism. -/
scoped instance : TopologicalSpace (LocalAlgebra K) := moduleTopology K (LocalAlgebra K)

scoped instance : IsModuleTopology K (LocalAlgebra K) := ⟨rfl⟩

scoped instance : IsTopologicalRing (LocalAlgebra K) :=
  IsModuleTopology.isTopologicalRing K (LocalAlgebra K)

/-- Base change respects the natural topologies on the tensor and quotient. -/
def presentationContinuousEquiv : LocalAlgebra K ≃A[K] CyclotomicLocalAlgebra.Model K where
  __ := presentation K
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (presentation K).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap (presentation K).symm.toLinearMap

/-- Splitting of the local tensor algebra, with its module topology. -/
def splittingContinuousEquiv (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    LocalAlgebra K ≃A[K] K × K :=
  (presentationContinuousEquiv K).trans (CyclotomicLocalAlgebra.splittingContinuousEquiv ζ hζ)

@[simp]
theorem splittingContinuousEquiv_zeta (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    splittingContinuousEquiv K ζ hζ (1 ⊗ₜ[ℚ] CyclotomicField.zeta) = (ζ, -1 - ζ) := by
  change CyclotomicLocalAlgebra.splittingEquiv ζ hζ (presentation K _) = _
  simp

/-- The two local coordinates of every `a + bζ`, with the embeddings fixed by
the chosen root. This is the formula used in the local height comparisons. -/
theorem splittingContinuousEquiv_linear (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) (a b : K) :
    splittingContinuousEquiv K ζ hζ
      (a ⊗ₜ[ℚ] (1 : CyclotomicField.E) + b ⊗ₜ[ℚ] CyclotomicField.zeta) =
        (a + b * ζ, a + b * (-1 - ζ)) := by
  have hb : b ⊗ₜ[ℚ] CyclotomicField.zeta =
      algebraMap K (LocalAlgebra K) b * (1 ⊗ₜ[ℚ] CyclotomicField.zeta) := by
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hb]
  change splittingContinuousEquiv K ζ hζ
    (algebraMap K (LocalAlgebra K) a +
      algebraMap K (LocalAlgebra K) b * (1 ⊗ₜ[ℚ] CyclotomicField.zeta)) = _
  simp only [map_add, map_mul, AlgHomClass.commutes, splittingContinuousEquiv_zeta]
  rfl

/-- On units, the tensor algebra is topologically the split Fourier group. -/
def splittingUnitsEquiv (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (LocalAlgebra K)ˣ ≃ₜ* Kˣ × Kˣ :=
  (Units.mapContinuousMulEquiv {
    __ := (presentationContinuousEquiv K).toAlgEquiv.toMulEquiv
    __ := (presentationContinuousEquiv K).toHomeomorph }).trans
      (CyclotomicLocalAlgebra.splittingUnitsEquiv ζ hζ)

end Topology

/-- The split-prime criterion for the base change of the global quadratic field. -/
def padicUnitsEquiv (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    (LocalAlgebra ℚ_[p])ˣ ≃ₜ* ℚ_[p]ˣ × ℚ_[p]ˣ :=
  splittingUnitsEquiv ℚ_[p] (Classical.choose (CyclotomicLocalRoots.field_root p hp))
    (Classical.choose_spec (CyclotomicLocalRoots.field_root p hp))

end Cubic.QuadraticCorrespondence.CyclotomicBaseChange
