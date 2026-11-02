import CubicTargets.QuadraticCorrespondence.IsoCocharLattices
import Mathlib.Tactic.FieldSimp

/-!
# Proof of `eqn:isoCocharLattices`

The isomorphism is the restriction of the rational linear map
`(x, y) ↦ (2x - y, -x + 2y)` on `N_{E,ℚ}'`, the inverse of the matrix with
columns `ω = (2/3, 1/3)` and `γω = (1/3, 2/3)`. It commutes with the swap `γ`,
is injective (determinant three), and carries `N_E = ℤ⟨ω, γω⟩` onto
`N_E' = ℤ⟨v₁, v₂⟩` because it sends `ω ↦ v₁` and `γω ↦ v₂`.

The paper gives no separate proof; the display records the change of basis,
whose integral form `CocharacterIsomorphism.fromCyclotomic` is the inverse
direction in `(v₁, ω)` coordinates.
-/

namespace Cubic.QuadraticCorrespondence.IsoCocharLattices

open CubicTargets.QuadraticCorrespondence.IsoCocharLattices
open Cubic.OrbitParametrization.CocharacterLattice

/-- The rational map `ω ↦ v₁`, `γω ↦ v₂` on `N_{E,ℚ}'`. -/
def basisChange : (ℚ × ℚ) →ₗ[ℤ] (ℚ × ℚ) where
  toFun x := (2 * x.1 - x.2, -x.1 + 2 * x.2)
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' c x := by ext <;> simp [zsmul_eq_mul] <;> ring

theorem basisChange_injective : Function.Injective basisChange := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [basisChange, LinearMap.coe_mk, AddHom.coe_mk] at h₁ h₂
  ext <;> linarith

theorem gamma_apply (x : ℚ × ℚ) : gamma x = x.swap := rfl

theorem basisChange_gamma (x : ℚ × ℚ) : basisChange (gamma x) = gamma (basisChange x) := by
  simp only [basisChange, gamma_apply, LinearMap.coe_mk, AddHom.coe_mk, Prod.swap]
  ext <;> dsimp <;> ring

theorem basisChange_omega : basisChange ω = v₁ := by
  ext <;> norm_num [basisChange, ω, v₁]

theorem basisChange_gamma_omega : basisChange (gamma ω) = v₂ := by
  ext <;> norm_num [basisChange, gamma_apply, ω, v₂]

theorem v₁_eq : v₁ = (2 : ℤ) • ω - (1 : ℤ) • gamma ω := by
  ext <;> norm_num [v₁, ω, gamma_apply]

theorem v₂_eq : v₂ = (2 : ℤ) • gamma ω - (1 : ℤ) • ω := by
  ext <;> norm_num [v₂, ω, gamma_apply]

theorem gamma_omega_eq : gamma ω = v₁ + v₂ - ω := by
  ext <;> norm_num [v₁, v₂, ω, gamma_apply]

theorem quotient_span : quotientLattice = Submodule.span ℤ {ω, gamma ω} := by
  set S := Submodule.span ℤ ({ω, gamma ω} : Set (ℚ × ℚ))
  have hω : ω ∈ S := Submodule.subset_span (by simp)
  have hγω : gamma ω ∈ S := Submodule.subset_span (by simp)
  apply le_antisymm
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [v₁_eq]; exact S.sub_mem (S.smul_mem _ hω) (S.smul_mem _ hγω)
      · rw [v₂_eq]; exact S.sub_mem (S.smul_mem _ hγω) (S.smul_mem _ hω)
    · exact Submodule.span_le.mpr (by simpa using hω)
  · apply Submodule.span_le.mpr
    intro x hx
    have h₁ : v₁ ∈ quotientLattice :=
      Submodule.mem_sup_left (Submodule.subset_span (by simp))
    have h₂ : v₂ ∈ quotientLattice :=
      Submodule.mem_sup_left (Submodule.subset_span (by simp))
    have h₃ : ω ∈ quotientLattice :=
      Submodule.mem_sup_right (Submodule.subset_span (by simp))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h₃
    · rw [gamma_omega_eq]
      exact quotientLattice.sub_mem (quotientLattice.add_mem h₁ h₂) h₃

theorem mem_quotientLattice {x : ℚ × ℚ} :
    x ∈ quotientLattice ↔ ∃ a b : ℤ, a • ω + b • gamma ω = x := by
  rw [quotient_span, Submodule.mem_span_pair]

theorem quotient_independent : LinearIndependent ℤ ![ω, gamma ω] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp [ω, gamma_apply, zsmul_eq_mul] at h₁ h₂
  have hs : (s : ℚ) = 0 := by linarith
  have ht : (t : ℚ) = 0 := by linarith
  exact ⟨by exact_mod_cast hs, by exact_mod_cast ht⟩

theorem cover_independent : LinearIndependent ℤ ![v₁, v₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp [v₁, v₂, zsmul_eq_mul] at h₁ h₂
  exact ⟨h₁, h₂⟩

theorem quotient_stable (x : ℚ × ℚ) (hx : x ∈ quotientLattice) : gamma x ∈ quotientLattice := by
  obtain ⟨a, b, rfl⟩ := mem_quotientLattice.mp hx
  refine mem_quotientLattice.mpr ⟨b, a, ?_⟩
  rw [map_add, map_zsmul, map_zsmul, add_comm]
  congr 2

theorem cover_stable (x : ℚ × ℚ) (hx : x ∈ coverLattice) : gamma x ∈ coverLattice := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  refine Submodule.mem_span_pair.mpr ⟨b, a, ?_⟩
  rw [map_add, map_zsmul, map_zsmul, add_comm]
  congr 2

theorem map_quotientLattice : quotientLattice.map basisChange = coverLattice := by
  rw [quotient_span, Submodule.map_span, Set.image_pair, basisChange_omega,
    basisChange_gamma_omega]
  rfl

/-- The isomorphism `N_E ≃ N_E'` of the display. -/
noncomputable def iso : quotientLattice ≃ₗ[ℤ] coverLattice :=
  (Submodule.equivMapOfInjective basisChange basisChange_injective quotientLattice).trans
    (LinearEquiv.ofEq _ _ map_quotientLattice)

theorem iso_apply (x : quotientLattice) : (iso x : ℚ × ℚ) = basisChange x := rfl

theorem «eqn:isoCocharLattices» : Claim where
  quotient_span := quotient_span
  quotient_independent := quotient_independent
  cover_independent := cover_independent
  quotient_stable := quotient_stable
  cover_stable := cover_stable
  iso := ⟨iso,
    fun x hx => by rw [iso_apply, hx, basisChange_omega],
    fun x hx => by rw [iso_apply, hx, basisChange_gamma_omega],
    fun x y hy => by rw [iso_apply, iso_apply, hy, basisChange_gamma]⟩

end Cubic.QuadraticCorrespondence.IsoCocharLattices
