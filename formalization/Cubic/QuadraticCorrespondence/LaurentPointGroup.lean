import Cubic.QuadraticCorrespondence.SplitLaurentPoints
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# The group law dual to the Laurent coordinate ring

Points of a lattice group algebra are characters of the lattice. Their group
law is pointwise multiplication of characters, equivalently the law dual to
mathlib's comultiplication. This construction does not use the cyclotomic
parametrization. The instances are scoped to avoid changing unrelated algebra
homomorphism types.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.LaurentPointGroup

open scoped TensorProduct

variable {K L R : Type*} [Field K] [AddCommGroup L] [CommRing R] [Algebra K R]

/-- The universal property of the lattice algebra, with values in units. -/
def characterEquiv : (AddMonoidAlgebra K L →ₐ[K] R) ≃ (Multiplicative L →* Rˣ) :=
  (AddMonoidAlgebra.lift K R L).symm.trans MonoidHom.toHomUnitsMulEquiv.toEquiv

scoped instance pointCommGroup : CommGroup (AddMonoidAlgebra K L →ₐ[K] R) :=
  characterEquiv.commGroup

@[simp]
theorem character_mul (f g : AddMonoidAlgebra K L →ₐ[K] R) :
    characterEquiv (f * g) = characterEquiv f * characterEquiv g :=
  characterEquiv.apply_symm_apply _

@[simp]
theorem character_one : characterEquiv (1 : AddMonoidAlgebra K L →ₐ[K] R) = 1 :=
  characterEquiv.apply_symm_apply _

@[simp]
theorem character_inv (f : AddMonoidAlgebra K L →ₐ[K] R) :
    characterEquiv f⁻¹ = (characterEquiv f)⁻¹ :=
  characterEquiv.apply_symm_apply _

theorem mul_single (f g : AddMonoidAlgebra K L →ₐ[K] R) (n : L) (c : K) :
    (f * g) (AddMonoidAlgebra.single n c) =
      algebraMap K R c * (f (AddMonoidAlgebra.single n 1) * g (AddMonoidAlgebra.single n 1)) := by
  change AddMonoidAlgebra.lift K R L _ (AddMonoidAlgebra.single n c) = _
  simp [Algebra.smul_def, characterEquiv]

@[simp]
theorem one_single (n : L) (c : K) :
    (1 : AddMonoidAlgebra K L →ₐ[K] R) (AddMonoidAlgebra.single n c) = algebraMap K R c := by
  change AddMonoidAlgebra.lift K R L _ (AddMonoidAlgebra.single n c) = _
  simp [Algebra.smul_def]

@[simp]
theorem inv_single (f : AddMonoidAlgebra K L →ₐ[K] R) (n : L) (c : K) :
    f⁻¹ (AddMonoidAlgebra.single n c) = f (AddMonoidAlgebra.single (-n) c) := by
  change AddMonoidAlgebra.lift K R L _ (AddMonoidAlgebra.single n c) = _
  rw [AddMonoidAlgebra.lift_single]
  have h := DFunLike.congr_fun ((AddMonoidAlgebra.lift K R L).apply_symm_apply f)
    (AddMonoidAlgebra.single (-n) c)
  rw [AddMonoidAlgebra.lift_single] at h
  exact h

private theorem map_single (f : AddMonoidAlgebra K L →ₐ[K] R) (n : L) (c : K) :
    f (AddMonoidAlgebra.single n c) = algebraMap K R c * f (AddMonoidAlgebra.single n 1) := by
  have h : AddMonoidAlgebra.single n c = c • AddMonoidAlgebra.single n (1 : K) := by simp
  rw [h, map_smul, Algebra.smul_def]

/-- This is the lattice-algebra coproduct. -/
theorem mul_eq_comul (f g : AddMonoidAlgebra K L →ₐ[K] R) (b : AddMonoidAlgebra K L) :
    (f * g) b = LinearMap.mul' K R
      (TensorProduct.map f.toLinearMap g.toLinearMap (Coalgebra.comul (R := K) b)) := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc]
  | single n c =>
    simp only [mul_single]
    simp
    rw [map_single g n c]
    ring

/-- Change of coefficient algebra preserves the Laurent point group law. -/
theorem comp_mul {S : Type*} [CommRing S] [Algebra K S]
    (φ : R →ₐ[K] S) (f g : AddMonoidAlgebra K L →ₐ[K] R) :
    φ.comp (f * g) = (φ.comp f) * (φ.comp g) := by
  apply AddMonoidAlgebra.algHom_ext
  intro n
  simp [AlgHom.comp_apply, mul_single]

/-- Every lattice homomorphism gives a homomorphism of point groups. -/
theorem comp_mapDomain_mul {M : Type*} [AddCommGroup M] (h : M →+ L)
    (f g : AddMonoidAlgebra K L →ₐ[K] R) :
    (f * g).comp (AddMonoidAlgebra.mapDomainAlgHom K K h) =
      (f.comp (AddMonoidAlgebra.mapDomainAlgHom K K h)) *
        (g.comp (AddMonoidAlgebra.mapDomainAlgHom K K h)) := by
  apply AddMonoidAlgebra.algHom_ext
  intro n
  simp [AlgHom.comp_apply, mul_single]

open SplitLaurentInvariants SplitLaurentPoints

/-- The two chosen coordinate characters multiply in the usual way. -/
theorem coordinates_mul (f g : LaurentRing (K := K) →ₐ[K] R) :
    coordinates (f * g) = coordinates f * coordinates g := by
  apply Prod.ext <;> apply Units.ext
  · change (f * g) (AddMonoidAlgebra.single (1, 0) 1) =
      f (AddMonoidAlgebra.single (1, 0) 1) * g (AddMonoidAlgebra.single (1, 0) 1)
    simp [mul_single]
  · change (f * g) (AddMonoidAlgebra.single (0, 1) 1) =
      f (AddMonoidAlgebra.single (0, 1) 1) * g (AddMonoidAlgebra.single (0, 1) 1)
    simp [mul_single]

/-- The point coordinates preserve the group law. -/
def coordinatesMulEquiv : (LaurentRing (K := K) →ₐ[K] R) ≃* Rˣ × Rˣ :=
  { pointEquiv with map_mul' := coordinates_mul }

end Cubic.QuadraticCorrespondence.LaurentPointGroup
