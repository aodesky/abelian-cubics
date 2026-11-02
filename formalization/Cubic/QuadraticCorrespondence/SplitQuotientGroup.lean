import Cubic.QuadraticCorrespondence.LaurentPointGroup
import Cubic.QuadraticCorrespondence.SplitCoverFunctor

/-!
# The split quotient group law comes from the original cover

The invariant Laurent presentation transports the lattice coproduct to the
cyclic invariant ring. We verify that its inclusion in the cover ring preserves
this coproduct. Thus the resulting point group law is the restriction of the
original law, including on quotient points with no cover lift.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.SplitQuotientGroup

open scoped TensorProduct LaurentPointGroup
open SplitLaurentInvariants

variable {K : Type*} [Field K] (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3)
variable {R : Type*} [CommRing R] [Algebra K R]

/-- Precomposition by the invariant-ring presentation. -/
def presentation : (invariantRing ζ →ₐ[K] R) ≃ (LaurentRing (K := K) →ₐ[K] R) :=
  (invariantEquiv ζ hζ).symm.arrowCongr (AlgEquiv.refl : R ≃ₐ[K] R)

/-- The group law from the invariant ring's Laurent characters. -/
def pointGroup : CommGroup (invariantRing ζ →ₐ[K] R) :=
  (presentation ζ hζ).commGroup

def presentationMulEquiv :
    letI := pointGroup ζ hζ (R := R)
    (invariantRing ζ →ₐ[K] R) ≃* (LaurentRing (K := K) →ₐ[K] R) := by
  letI := pointGroup ζ hζ (R := R)
  exact { presentation ζ hζ with
    map_mul' := fun _ _ => (presentation ζ hζ).apply_symm_apply _ }

/-- The coproduct on invariant functions, constructed through their Laurent presentation. -/
def comul : invariantRing ζ →ₐ[K] invariantRing ζ ⊗[K] invariantRing ζ :=
  (Algebra.TensorProduct.map (invariantEquiv ζ hζ).toAlgHom
    (invariantEquiv ζ hζ).toAlgHom).comp
      ((Bialgebra.comulAlgHom K (LaurentRing (K := K))).comp
        (invariantEquiv ζ hζ).symm.toAlgHom)

/-- The invariant-ring coproduct is the restriction of the original cover coproduct. -/
theorem comul_subtype (b : invariantRing ζ) :
    Algebra.TensorProduct.map (invariantRing ζ).val (invariantRing ζ).val (comul ζ hζ b) =
      Coalgebra.comul (R := K) (b : LaurentRing (K := K)) := by
  obtain ⟨f, rfl⟩ := (invariantEquiv ζ hζ).surjective b
  change Algebra.TensorProduct.map _ _
    (Algebra.TensorProduct.map _ _
      (Coalgebra.comul (R := K) ((invariantEquiv ζ hζ).symm (invariantEquiv ζ hζ f)))) = _
  rw [AlgEquiv.symm_apply_apply]
  have h := DFunLike.congr_fun
    (BialgHomClass.map_comp_comulAlgHom (AddMonoidAlgebra.mapDomainBialgHom K
      CharacterLattice.pullback)) f
  change Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _
    (Coalgebra.comul (R := K) f)) = Coalgebra.comul (R := K) (pullbackHom f)
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  exact h

/-- Multiplication on all quotient points is dual to this restricted coproduct. -/
theorem mul_eq_comul (f g : invariantRing ζ →ₐ[K] R) (b : invariantRing ζ) :
    letI := pointGroup ζ hζ (R := R)
    (f * g) b = LinearMap.mul' K R
      (TensorProduct.map f.toLinearMap g.toLinearMap (comul ζ hζ b)) := by
  letI := pointGroup ζ hζ (R := R)
  obtain ⟨c, rfl⟩ := (invariantEquiv ζ hζ).surjective b
  have h := DFunLike.congr_fun ((presentationMulEquiv ζ hζ).map_mul f g) c
  change (f * g) (invariantEquiv ζ hζ c) = _ at h
  rw [h, LaurentPointGroup.mul_eq_comul]
  simp only [comul, AlgHom.comp_apply, AlgEquiv.coe_algHom,
    AlgEquiv.symm_apply_apply]
  congr 1
  change TensorProduct.map _ _ (Coalgebra.comul (R := K) c) =
    TensorProduct.map f.toLinearMap g.toLinearMap
      (Algebra.TensorProduct.map _ _ (Coalgebra.comul (R := K) c))
  induction Coalgebra.comul (R := K) c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Restriction from the split cover preserves the original multiplication. -/
theorem restrict_mul (f g : LaurentRing (K := K) →ₐ[K] R) :
    letI := pointGroup ζ hζ (R := R)
    (f * g).comp (invariantRing ζ).val =
      (f.comp (invariantRing ζ).val) * (g.comp (invariantRing ζ).val) := by
  letI := pointGroup ζ hζ (R := R)
  apply (presentation ζ hζ).injective
  change (f * g).comp pullbackHom =
    presentationMulEquiv ζ hζ (f.comp (invariantRing ζ).val * g.comp (invariantRing ζ).val)
  rw [(presentationMulEquiv ζ hζ).map_mul]
  exact LaurentPointGroup.comp_mapDomain_mul CharacterLattice.pullback f g

/-- The quotient-character coordinates preserve the invariant-ring group law. -/
def coordinatesMulEquiv :
    letI := pointGroup ζ hζ (R := R)
    (invariantRing ζ →ₐ[K] R) ≃* Rˣ × Rˣ := by
  letI := pointGroup ζ hζ (R := R)
  exact (presentationMulEquiv ζ hζ).trans LaurentPointGroup.coordinatesMulEquiv

section OriginalCover

variable [CharZero K] (z : K) (hz : z ^ 2 + z + 1 = 0)
open Cubic.OrbitParametrization.CyclicGroupAlgebra SplitCoverFunctor

/-- The lattice law is exactly the group law of the original augmentation-one cover. -/
theorem coverPointEquiv_mul (g h : traceOneUnits R) :
    coverPointEquiv z hz (g * h) = coverPointEquiv z hz g * coverPointEquiv z hz h := by
  apply SplitLaurentPoints.pointEquiv.injective
  change SplitLaurentPoints.coordinates (coverPointEquiv z hz (g * h)) =
    SplitLaurentPoints.coordinates (coverPointEquiv z hz g * coverPointEquiv z hz h)
  rw [LaurentPointGroup.coordinates_mul]
  simp only [coverPointEquiv_apply, SplitLaurentPoints.coordinates_evaluate, map_mul]

end OriginalCover

end Cubic.QuadraticCorrespondence.SplitQuotientGroup
