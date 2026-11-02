import Cubic.OrbitParametrization.ModuliMap
import Cubic.ToricHeights.DescendedCyclicInvariant

/-!
# The cover ring is spanned over the quotient by the coordinates

Let `A` be the rational coordinate ring of the cover (`coverFixedRing`) and `A^G`
the quotient ring. The cyclic generator acts on `A` by the diagonal twist, which
commutes with the Galois conjugation. Elements of `A` fixed by it lie in `A^G`.

The universal augmentation-one unit over `A` has the coordinates `Xᵢ` as
coefficients. Every `a ∈ A` is `Σᵢ cᵢ Xᵢ` with `cᵢ ∈ A^G`: in `A[C₃]`, the element
`α = Σₘ σᵐ(a)[m]` equals `γ ū` with `ū = Σⱼ Xⱼ[-j]` a unit, and `γ = α ū⁻¹` has
twist-invariant coefficients. This is the input from the torsor property used
in [O'Desky–Rosen, Prop. 2.4] to identify `A ⊗_{A^G} ℚ` with a pair.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open CyclicGroupAlgebra
open Cubic.QuadraticCorrespondence Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.QuadraticCorrespondence.CyclotomicTorusGalois SplitLaurentInvariants SplitCoverFunctor
open Cubic.QuadraticCorrespondence.RationalCoverFunctor DescendedCoefficients
open Cubic.ToricHeights.DescendedCyclicInvariant

/-- The cyclic generator of the cover action. -/
abbrev ρ : Eˣ := rootUnit zeta zeta_relation

theorem conjugate_twist (f : LaurentRing (K := E)) :
    SplitLaurentGalois.conjugate conjugation (twist ρ f) =
      twist ρ (SplitLaurentGalois.conjugate conjugation f) := by
  ext n
  rw [SplitLaurentGalois.conjugate_apply, twist_apply, twist_apply,
    SplitLaurentGalois.conjugate_apply, map_mul]
  congr 1
  have hc : conjugation ((ρ : Eˣ) : E) = ((ρ ^ 2 : Eˣ) : E) := by
    change conjugation zeta = _
    rw [conjugation_zeta_sq]
    rfl
  have hcz : ∀ k : ℤ, conjugation (((ρ ^ k : Eˣ)) : E) = ((ρ ^ (2 * k) : Eˣ) : E) := by
    intro k
    have hu : (Units.map conjugation.toMonoidHom ρ) = ρ ^ 2 := Units.ext hc
    have h1 : Units.map conjugation.toMonoidHom (ρ ^ k) = ρ ^ (2 * k) := by
      rw [map_zpow, hu, zpow_mul]
      norm_cast
    exact congrArg Units.val h1
  rw [hcz]
  have h3 : ρ ^ (3 : ℤ) = 1 := by
    have := (rootUnit_primitive zeta zeta_relation).pow_eq_one
    exact_mod_cast this
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [show 2 * (n.2 + 2 * n.1) = (n.1 + 2 * n.2) + 3 * (n.1) by ring, zpow_add, zpow_mul, h3,
    one_zpow, mul_one]

/-- The cover coordinate ring as a type. -/
abbrev CoverAlg := ↥coverFixedRing

theorem twist_mem (a : CoverAlg) : twist ρ (a : LaurentRing (K := E)) ∈ coverFixedRing := by
  have ha : SplitLaurentGalois.conjugate conjugation (a : LaurentRing (K := E)) = a := a.property
  change SplitLaurentGalois.conjugate conjugation (twist ρ (a : LaurentRing (K := E))) = _
  rw [conjugate_twist, ha]
  rfl

/-- The action of the generator on the cover coordinate ring. -/
def coverAct : CoverAlg →ₐ[ℚ] CoverAlg :=
  AlgHom.codRestrict (((twist ρ).restrictScalars ℚ).comp coverFixedRing.val) coverFixedRing
    (fun a => twist_mem a)

theorem coverAct_coe (a : CoverAlg) : (coverAct a : LaurentRing (K := E)) = twist ρ a := rfl

theorem coverAct_cube (a : CoverAlg) : coverAct (coverAct (coverAct a)) = a := by
  apply Subtype.ext
  simp only [coverAct_coe]
  have h := congrArg (fun φ : LaurentRing (K := E) →ₐ[E] LaurentRing (K := E) =>
    φ (a : LaurentRing (K := E))) (twist_cube ρ (by
      have := (rootUnit_primitive zeta zeta_relation).pow_eq_one
      exact_mod_cast this))
  simpa using h

/-- Elements fixed by the generator lie in the quotient ring. -/
theorem mem_quotient_of_fixed (a : CoverAlg) (ha : coverAct a = a) :
    (a : LaurentRing (K := E)) ∈ quotientFixedRing :=
  ⟨a.property, by
    change twist ρ (a : LaurentRing (K := E)) = a
    exact congrArg Subtype.val ha⟩

/-- The universal coordinates. -/
def coord (i : ZMod 3) : CoverAlg := ⟨coverCoordinate i, coverCoordinate_conjugation i⟩

theorem coverAct_coord (i : ZMod 3) : coverAct (coord i) = coord (-1 + i) :=
  Subtype.ext (coverCoordinate_twist i)

/-- A rational cover point evaluates the coordinates to the coefficients of its unit. -/
theorem rationalCover_coord {A : Type*} [CommRing A] [Algebra ℚ A] (g : traceOneUnits A)
    (i : ZMod 3) : rationalCoverPointEquiv A g (coord i) = (g.val : GroupAlgebra A) i := by
  apply CyclotomicScalarDescent.includeRight_injective A
  change (1 : E) ⊗ₜ[ℚ] rationalCoverPointEquiv A g (coord i) = _
  rw [← CyclotomicPointDescent.extendPoint_fixed, extend_rationalCoverPoint]
  change coverPointEquiv zeta zeta_relation (CyclotomicCoverDescent.extendCover A g)
    (coverCoordinate i) = _
  rw [evaluate_coverCoordinate]
  simp only [CyclotomicCoverDescent.extendCover, mapUnits_coefficient]
  rfl

/-- The universal augmentation-one unit over the cover coordinate ring. -/
def universalUnit : traceOneUnits CoverAlg :=
  (rationalCoverPointEquiv CoverAlg).symm (AlgHom.id ℚ CoverAlg)

theorem universalUnit_apply (i : ZMod 3) :
    ((universalUnit.val : GroupAlgebra CoverAlg)) i = coord i := by
  have h := rationalCover_coord universalUnit i
  rw [universalUnit, Equiv.apply_symm_apply] at h
  exact h.symm

private theorem eq_coordinates {R : Type*} [CommRing R] (f : GroupAlgebra R) :
    f = coordinates R (f 0) (f 1) (f 2) := (coordinates_coefficients R f).symm

private theorem coordinates_inj {R : Type*} [CommRing R] {a b c a' b' c' : R}
    (h : coordinates R a b c = coordinates R a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have h0 := congrArg (fun f : GroupAlgebra R => f 0) h
  have h1 := congrArg (fun f : GroupAlgebra R => f 1) h
  have h2 := congrArg (fun f : GroupAlgebra R => f 2) h
  simp +decide [coordinates] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

/-- Every element of the cover ring is a combination of the coordinates with
coefficients in the quotient ring. -/
theorem span_coord (a : CoverAlg) :
    ∃ c₀ c₁ c₂ : quotientFixedRing,
      a = RationalQuotientFunctor.quotientInclusion c₀ * coord 0 +
        RationalQuotientFunctor.quotientInclusion c₁ * coord 1 +
        RationalQuotientFunctor.quotientInclusion c₂ * coord 2 := by
  set U := (universalUnit.val : GroupAlgebra CoverAlg)
  set V := ((universalUnit.val⁻¹ : (GroupAlgebra CoverAlg)ˣ) : GroupAlgebra CoverAlg)
  have hUV : U * V = 1 := universalUnit.val.mul_inv
  have hU : ∀ i, U i = coord i := universalUnit_apply
  -- the coefficient equations of `U V = 1`
  have hUV' := hUV
  rw [eq_coordinates U, eq_coordinates V, coordinates_mul, ← coordinates_one] at hUV'
  obtain ⟨e₀, e₁, e₂⟩ := coordinates_inj hUV'
  -- the generator shifts the inverse
  let shiftMap := AddMonoidAlgebra.mapRangeRingHom (ZMod 3) coverAct.toRingHom
  have hSU : shiftMap U = coordinates CoverAlg (U 2) (U 0) (U 1) := by
    rw [eq_coordinates (shiftMap U)]
    simp only [shiftMap, AddMonoidAlgebra.mapRangeRingHom_apply, hU, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, coverAct_coord]
    rw [show (-1 + 0 : ZMod 3) = 2 by decide, show (-1 + 1 : ZMod 3) = 0 by decide,
      show (-1 + 2 : ZMod 3) = 1 by decide]
  have hW : coordinates CoverAlg (U 2) (U 0) (U 1) * coordinates CoverAlg (V 1) (V 2) (V 0) = 1 := by
    rw [coordinates_mul, ← coordinates_one]
    congr 1
    · linear_combination e₀
    · linear_combination e₁
    · linear_combination e₂
  have hSV : shiftMap V = coordinates CoverAlg (V 1) (V 2) (V 0) := by
    have h1 : shiftMap U * shiftMap V = 1 := by rw [← map_mul, hUV, map_one]
    calc shiftMap V = shiftMap V * (shiftMap U * coordinates CoverAlg (V 1) (V 2) (V 0)) := by rw [hSU, hW, mul_one]
      _ = (shiftMap U * shiftMap V) * coordinates CoverAlg (V 1) (V 2) (V 0) := by ring
      _ = _ := by rw [h1, one_mul]
  have hσV : coverAct (V 0) = V 1 ∧ coverAct (V 1) = V 2 ∧ coverAct (V 2) = V 0 := by
    rw [eq_coordinates (shiftMap V)] at hSV
    simpa [shiftMap, AddMonoidAlgebra.mapRangeRingHom_apply] using coordinates_inj hSV
  obtain ⟨hv0, hv1, hv2⟩ := hσV
  have ha3 := coverAct_cube a
  set σa := coverAct a
  set σ2a := coverAct σa
  let γ₀ := a * V 0 + σa * V 1 + σ2a * V 2
  let γ₁ := a * V 2 + σa * V 0 + σ2a * V 1
  let γ₂ := a * V 1 + σa * V 2 + σ2a * V 0
  have hγ₀ : coverAct γ₀ = γ₀ := by
    simp only [γ₀, map_add, map_mul, hv0, hv1, hv2, ha3]
    ring
  have hγ₁ : coverAct γ₁ = γ₁ := by
    simp only [γ₁, map_add, map_mul, hv0, hv1, hv2, ha3]
    ring
  have hγ₂ : coverAct γ₂ = γ₂ := by
    simp only [γ₂, map_add, map_mul, hv0, hv1, hv2, ha3]
    ring
  refine ⟨⟨γ₀, mem_quotient_of_fixed γ₀ hγ₀⟩, ⟨γ₁, mem_quotient_of_fixed γ₁ hγ₁⟩,
    ⟨γ₂, mem_quotient_of_fixed γ₂ hγ₂⟩, ?_⟩
  have hι : ∀ (c : CoverAlg) (hc : (c : LaurentRing (K := E)) ∈ quotientFixedRing),
      RationalQuotientFunctor.quotientInclusion ⟨c, hc⟩ = c := fun c hc => rfl
  rw [hι, hι, hι, ← hU, ← hU, ← hU]
  simp only [γ₀, γ₁, γ₂]
  linear_combination (-a) * e₀ - σa * e₁ - σ2a * e₂

end Cubic.OrbitParametrization.C3Algebra
