import CubicTargets.OrbitParametrization.TwistedCubicField
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Cubic.OrbitParametrization.TwistCohomology

/-!
# `example:twoRationalPointsSamePoly`

The Galois group of a cubic Galois extension has order three, hence is isomorphic to
`C₃`. With an identification `ι : C₃ ≃* Gal(K/ℚ)`, `K` is a `C₃`-algebra in the field
model of `C3Alg` (a field of degree three with a faithful action).

The paper gives no proof. Non-isomorphism with the twist: an isomorphism `K → K'` of
`C₃`-algebras is a field automorphism `τ` with `τ(g y) = g⁻¹ τ(y)`. Since `Gal(K/ℚ) ≅ C₃`
is abelian and `τ` lies in it, `τ` commutes with `g`, so `g = g⁻¹` on `K`, which fails
for a generator.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open Module

/-- An isomorphism to the twist commuting with a faithful abelian action is impossible. -/
theorem not_isomorphic_twist_of_galois (K : Type) [Field K] [Algebra ℚ K]
    (ι : C3 ≃* (K ≃ₐ[ℚ] K)) (A : C3Alg) (e : A.carrier ≃ₐ[ℚ] K)
    (he : ∀ (g : C3) (y : A.carrier), e (A.act g y) = ι g (e y)) : ¬ A.Isomorphic A.twist := by
  rintro ⟨τ, hτ⟩
  -- transport `τ` to an automorphism of `K`
  let τ' : K ≃ₐ[ℚ] K := (e.symm.trans τ).trans e
  have key : ∀ (g : C3) (z : K), τ' (ι g z) = ι g⁻¹ (τ' z) := by
    intro g z
    obtain ⟨y, rfl⟩ := e.surjective z
    change e (τ (e.symm (ι g (e y)))) = ι g⁻¹ (e (τ (e.symm (e y))))
    rw [← he g y, e.symm_apply_apply, e.symm_apply_apply, hτ, C3Alg.twist_act]
    exact he g⁻¹ (τ y)
  -- `τ'` lies in the abelian group `ι(C₃)`, so it commutes with `ι g`
  obtain ⟨h, hh⟩ := ι.surjective τ'
  let s : C3 := Multiplicative.ofAdd 1
  have hs : ι s = ι s⁻¹ := by
    ext z
    obtain ⟨w, rfl⟩ := (ι h).surjective z
    have h1 := key s w
    rw [← hh] at h1
    have hc : ι h (ι s w) = ι s (ι h w) := by
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, mul_comm]
    rw [← hc, h1]
  exact absurd (ι.injective hs) (by decide)

theorem fieldClaim :
    CubicTargets.OrbitParametrization.TwistedCubicField.FieldClaim := by
  intro K _ _ _ hdim
  refine ⟨?_, fun ι => ⟨?_, fun A e he => not_isomorphic_twist_of_galois K ι A e he⟩⟩
  · have hcard : Nat.card (K ≃ₐ[ℚ] K) = 3 := by rw [IsGalois.card_aut_eq_finrank, hdim]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact ⟨(mulEquivOfPrimeCardEq hcard (by rw [Nat.card_eq_fintype_card]; rfl)).symm⟩
  · let A : C3Alg :=
      { carrier := K
        act := ι.toMonoidHom
        model := Or.inl ⟨Field.toIsField K, hdim, ι.injective⟩ }
    exact ⟨A, AlgEquiv.refl, fun _ _ => rfl⟩

theorem «example:twoRationalPointsSamePoly» :
    CubicTargets.OrbitParametrization.TwistedCubicField.Claim :=
  ⟨fieldClaim, TwistCohomology.field_cocycles⟩

end Cubic.OrbitParametrization.C3Algebra
