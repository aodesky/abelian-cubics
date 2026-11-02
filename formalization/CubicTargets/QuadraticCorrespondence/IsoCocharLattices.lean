import Cubic.OrbitParametrization.CocharacterLattice
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Concrete statement of `eqn:isoCocharLattices`

The paper's display

  `N_E = ℤ⟨ω, γω⟩ → N_E' = ℤ⟨v₁, v₂⟩`,  `ω ↦ v₁`,  `γω ↦ v₂`,

asserts three things: the cocharacters `ω` and `γω` form a basis of `N_E`;
`N_E'` has basis `v₁, v₂`; and the assignment on bases is a `Γ`-equivariant
isomorphism of lattices.

Documented equivalent (lattice level). No scheme-level classification of the
characters and cocharacters of the tori `T_E` and `𝒢_{1,E}` exists in this
project, so the lattices are the ones *defined* in the paper (in
the paragraph introducing `ω`), all inside `N_{E,ℚ}' = N_E' ⊗ ℚ`, written in
the coordinates of the basis `(v₁, v₂)` of the quotient of `ℚ C₃` by the line
`ℚ(v₀'+v₁'+v₂')`:

* `N_E' = ℤ v₁ + ℤ v₂` (the image of the cocharacter lattice of `𝒢₁`);
* `ω = (2v₁+v₂)/3` and `N_E = N_E' + ℤ ω`, the paper's enlarged lattice;
* `Γ = {1, γ}` acts on `M_E'` by swapping `v₁^∨` and `v₂^∨`, so on the dual
  `N_E'` (and on `N_{E,ℚ}'`) by swapping `v₁` and `v₂`; in coordinates this is
  `Prod.swap`. In particular `γω = (v₁+2v₂)/3`.

`Γ`-stability of both lattices is included, so that equivariance is a statement
about the restricted actions.
-/

namespace CubicTargets.QuadraticCorrespondence.IsoCocharLattices

open Cubic.OrbitParametrization.CocharacterLattice

/-- `N_E' = ℤ⟨v₁, v₂⟩`, the cocharacter lattice of `𝒢_{1,E}`. -/
def coverLattice : Submodule ℤ (ℚ × ℚ) := Submodule.span ℤ {v₁, v₂}

/-- `N_E = N_E' + ℤω`, the cocharacter lattice of `T_E`. -/
def quotientLattice : Submodule ℤ (ℚ × ℚ) := coverLattice ⊔ Submodule.span ℤ {ω}

/-- The nontrivial element `γ ∈ Γ`, acting on `N_{E,ℚ}'` by swapping `v₁` and `v₂`. -/
def gamma : (ℚ × ℚ) ≃ₗ[ℤ] (ℚ × ℚ) := LinearEquiv.prodComm ℤ ℚ ℚ

structure Claim : Prop where
  /-- `N_E = ℤ⟨ω, γω⟩`: the two cocharacters span `N_E` ... -/
  quotient_span : quotientLattice = Submodule.span ℤ {ω, gamma ω}
  /-- ... and are linearly independent, so they form a basis. -/
  quotient_independent : LinearIndependent ℤ ![ω, gamma ω]
  /-- `v₁, v₂` are linearly independent, so they form a basis of `N_E'`. -/
  cover_independent : LinearIndependent ℤ ![v₁, v₂]
  /-- Both lattices are `Γ`-stable. -/
  quotient_stable : ∀ x ∈ quotientLattice, gamma x ∈ quotientLattice
  cover_stable : ∀ x ∈ coverLattice, gamma x ∈ coverLattice
  /-- The `Γ`-equivariant isomorphism with `ω ↦ v₁` and `γω ↦ v₂`. -/
  iso : ∃ f : quotientLattice ≃ₗ[ℤ] coverLattice,
    (∀ x : quotientLattice, (x : ℚ × ℚ) = ω → (f x : ℚ × ℚ) = v₁) ∧
    (∀ x : quotientLattice, (x : ℚ × ℚ) = gamma ω → (f x : ℚ × ℚ) = v₂) ∧
    (∀ x y : quotientLattice, (y : ℚ × ℚ) = gamma x →
      (f y : ℚ × ℚ) = gamma (f x : ℚ × ℚ))

end CubicTargets.QuadraticCorrespondence.IsoCocharLattices
