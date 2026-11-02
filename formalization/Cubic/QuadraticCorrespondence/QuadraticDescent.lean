import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Effective descent for a quadratic semilinear involution

For a quadratic extension with an anti-invariant generator `δ`, a semilinear
involution on a commutative algebra recovers that algebra by extension of
scalars from its fixed subalgebra. The comparison is the natural map
`c ⊗ b ↦ c • b`. No reducedness or finite-dimensionality of the algebra is
assumed, so this applies to coordinate rings and arbitrary coefficient algebras.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuadraticDescent

open scoped TensorProduct

variable {F K B : Type*} [Field F] [Field K] [Algebra F K]
  [CommRing B] [Algebra K B] [Algebra F B] [IsScalarTower F K B]

/-- The ground-field subalgebra fixed by the given involution. -/
def fixedRing (σ : B ≃ₐ[F] B) : Subalgebra F B :=
  AlgHom.equalizer σ.toAlgHom (AlgHom.id F B)

/-- The canonical scalar-extension comparison, before proving it is invertible. -/
def baseChangeHom (σ : B ≃ₐ[F] B) : K ⊗[F] fixedRing σ →ₐ[K] B :=
  Algebra.TensorProduct.lift (Algebra.ofId K B) (fixedRing σ).val
    (fun _ _ => Commute.all _ _)

@[simp]
theorem baseChangeHom_tmul (σ : B ≃ₐ[F] B) (c : K) (b : fixedRing σ) :
    baseChangeHom σ (c ⊗ₜ[F] b) = c • (b : B) := by
  simp [baseChangeHom, Algebra.smul_def]

variable (γ : K ≃ₐ[F] K) (σ : B ≃ₐ[F] B)
  (hσ : ∀ c : K, σ (algebraMap K B c) = algebraMap K B (γ c))

omit [IsScalarTower F K B] in
include hσ in
theorem conjugate_smul (c : K) (b : B) : σ (c • b) = γ c • σ b := by
  simp only [Algebra.smul_def, map_mul, hσ]

variable (δ : K) (hδ : δ ≠ 0) (hγδ : γ δ = -δ) (htwo : (2 : K) ≠ 0)
  (hσσ : Function.Involutive σ)

omit [IsScalarTower F K B] in
include hσ hδ hγδ htwo hσσ in
/-- The even and odd parts give a decomposition into fixed elements. -/
theorem exists_fixed_decomposition (b : B) :
    ∃ a c : fixedRing σ, b = (a : B) + δ • (c : B) := by
  have hγtwo : γ ((2 : K)⁻¹) = (2 : K)⁻¹ := by simp only [map_inv₀, map_ofNat]
  have hγden : γ ((2 * δ)⁻¹) = -((2 * δ)⁻¹) := by
    simp only [map_inv₀, map_mul, map_ofNat, hγδ, mul_neg, inv_neg]
  have ha : σ ((2 : K)⁻¹ • (b + σ b)) = (2 : K)⁻¹ • (b + σ b) := by
    rw [conjugate_smul γ σ hσ, hγtwo, map_add, hσσ b, add_comm]
  have hc : σ ((2 * δ)⁻¹ • (b - σ b)) = (2 * δ)⁻¹ • (b - σ b) := by
    rw [conjugate_smul γ σ hσ, hγden, map_sub, hσσ b]
    module
  refine ⟨⟨_, ha⟩, ⟨_, hc⟩, ?_⟩
  change b = (2 : K)⁻¹ • (b + σ b) + δ • ((2 * δ)⁻¹ • (b - σ b))
  have hd : δ * (2 * δ)⁻¹ = (2 : K)⁻¹ := by field_simp
  rw [smul_smul, hd, ← smul_add]
  have hs : (b + σ b) + (b - σ b) = (2 : K) • b := by module
  rw [hs, smul_smul, inv_mul_cancel₀ htwo, one_smul]

omit [IsScalarTower F K B] in
include hσ hδ hγδ htwo in
/-- Uniqueness of the two fixed components, including for nonreduced algebras. -/
theorem fixed_decomposition_eq_zero (a c : fixedRing σ)
    (h : (a : B) + δ • (c : B) = 0) : a = 0 ∧ c = 0 := by
  have ha : σ (a : B) = a := a.property
  have hc : σ (c : B) = c := c.property
  have h' : (a : B) - δ • (c : B) = 0 := by
    have he := congrArg σ h
    simpa only [map_add, conjugate_smul γ σ hσ, ha, hc, hγδ,
      neg_smul, map_zero, sub_eq_add_neg] using he
  have hc' : (2 * δ) • (c : B) = 0 := by
    calc
      (2 * δ) • (c : B) = ((a : B) + δ • (c : B)) - ((a : B) - δ • (c : B)) := by module
      _ = 0 := by rw [h, h', sub_self]
  have hc0 : (c : B) = 0 := (smul_eq_zero.mp hc').resolve_left (mul_ne_zero htwo hδ)
  exact ⟨Subtype.ext (by simpa [hc0] using h), Subtype.ext hc0⟩

variable (hspan : ∀ c : K, ∃ a b : F, c = a • (1 : K) + b • δ)

omit [IsScalarTower F K B] [Algebra K B] [Algebra F B] [CommRing B] in
include hspan in
/-- The quadratic spanning property gives a two-term tensor normal form. -/
theorem exists_tensor_decomposition {M : Type*} [AddCommGroup M] [Module F M]
    (x : K ⊗[F] M) : ∃ a b : M, x = (1 : K) ⊗ₜ[F] a + δ ⊗ₜ[F] b := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c b =>
    obtain ⟨u, v, hc⟩ := hspan c
    refine ⟨u • b, v • b, ?_⟩
    rw [hc, TensorProduct.add_tmul]
    simp only [TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by simp only [TensorProduct.tmul_add]; abel⟩

include hσ hδ hγδ htwo hσσ hspan in
theorem baseChangeHom_bijective : Function.Bijective (baseChangeHom (K := K) σ) := by
  constructor
  · apply (injective_iff_map_eq_zero (baseChangeHom (K := K) σ)).mpr
    intro x hx
    obtain ⟨a, c, rfl⟩ := exists_tensor_decomposition δ hspan x
    have h : (a : B) + δ • (c : B) = 0 := by simpa using hx
    obtain ⟨rfl, rfl⟩ := fixed_decomposition_eq_zero γ σ hσ δ hδ hγδ htwo a c h
    simp
  · intro b
    obtain ⟨a, c, hb⟩ := exists_fixed_decomposition γ σ hσ δ hδ hγδ htwo hσσ b
    exact ⟨1 ⊗ₜ[F] a + δ ⊗ₜ[F] c, by simpa using hb.symm⟩

/-- Effective quadratic descent via the natural scalar-extension map. -/
def baseChangeEquiv : K ⊗[F] fixedRing σ ≃ₐ[K] B :=
  AlgEquiv.ofBijective (baseChangeHom σ)
    (baseChangeHom_bijective γ σ hσ δ hδ hγδ htwo hσσ hspan)

@[simp]
theorem baseChangeEquiv_tmul (c : K) (b : fixedRing σ) :
    baseChangeEquiv γ σ hσ δ hδ hγδ htwo hσσ hspan (c ⊗ₜ[F] b) = c • (b : B) :=
  baseChangeHom_tmul σ c b

end Cubic.QuadraticCorrespondence.QuadraticDescent
