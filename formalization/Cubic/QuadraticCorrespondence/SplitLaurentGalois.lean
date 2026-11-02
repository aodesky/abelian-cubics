import Cubic.QuadraticCorrespondence.SplitLaurentEvaluation
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Galois symmetry of the quotient Laurent presentation

Conjugation acts on coefficients and exchanges the two character exponents.
The quotient-character pullback commutes with this action. Consequently it
identifies the fixed subalgebra of the quotient Laurent ring with the elements
of the cover Laurent ring fixed both by conjugation and by the cyclic action.

This is an isomorphism of explicit fixed subalgebras. For the cyclotomic
field, `CyclotomicTorusDescent` proves the natural base-change comparisons;
`RationalCoverFunctor` identifies the descended cover with the original functor.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.SplitLaurentGalois

open SplitLaurentInvariants SplitLaurentEvaluation

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The semilinear Galois action: conjugate coefficients and swap exponents. -/
def conjugate (γ : K ≃ₐ[F] K) : LaurentRing (K := K) ≃ₐ[F] LaurentRing (K := K) :=
  (AddMonoidAlgebra.mapRangeAlgEquiv F (ℤ × ℤ) γ).trans
    (AddMonoidAlgebra.domCongr F K (AddEquiv.prodComm : (ℤ × ℤ) ≃+ (ℤ × ℤ)))

theorem conjugate_apply (γ : K ≃ₐ[F] K) (f : LaurentRing (K := K)) (n : ℤ × ℤ) :
    conjugate γ f n = γ (f n.swap) := by
  simp [conjugate, AddMonoidAlgebra.domCongr_apply]

theorem conjugate_single (γ : K ≃ₐ[F] K) (n : ℤ × ℤ) (c : K) :
    conjugate γ (AddMonoidAlgebra.single n c) = AddMonoidAlgebra.single n.swap (γ c) := by
  simp [conjugate, AddMonoidAlgebra.domCongr_single]

theorem conjugate_algebraMap (γ : K ≃ₐ[F] K) (c : K) :
    conjugate γ (algebraMap K (LaurentRing (K := K)) c) =
      algebraMap K (LaurentRing (K := K)) (γ c) := by
  change conjugate γ (AddMonoidAlgebra.single 0 c) = AddMonoidAlgebra.single 0 (γ c)
  rw [conjugate_single]
  rfl

theorem conjugate_involutive (γ : K ≃ₐ[F] K) (hγ : Function.Involutive γ) :
    Function.Involutive (conjugate γ) := by
  intro f
  ext n
  simp only [conjugate_apply, Prod.swap_swap]
  exact hγ (f n)

/-- The paper's quotient-character basis is Galois equivariant. -/
theorem conjugate_pullback (γ : K ≃ₐ[F] K) (f : LaurentRing (K := K)) :
    conjugate γ (pullbackHom f) = pullbackHom (conjugate γ f) := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp [hf, hg]
  · intro n c
    simp only [pullbackHom_single, conjugate_single, CharacterLattice.pullback_swap]

section Evaluation

variable {R : Type*} [CommRing R] [Algebra K R] [Algebra F R]

/-- The semilinear action on the two character values. -/
def pointConjugate (γR : R ≃ₐ[F] R) (x : Rˣ × Rˣ) : Rˣ × Rˣ :=
  (Units.map γR.toMonoidHom x.2, Units.map γR.toMonoidHom x.1)

/-- Evaluation respects the semilinear actions on coefficients and points.
The compatibility of the two coefficient automorphisms is explicit. -/
theorem evaluate_conjugate (γ : K ≃ₐ[F] K) (γR : R ≃ₐ[F] R)
    (hγ : ∀ c : K, γR (algebraMap K R c) = algebraMap K R (γ c))
    (x : Rˣ × Rˣ) (f : LaurentRing (K := K)) :
    evaluate (pointConjugate γR x) (conjugate γ f) = γR (evaluate x f) := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp [hf, hg]
  · intro n c
    rw [conjugate_single, evaluate_single, evaluate_single]
    change algebraMap K R (γ c) *
        ((Units.map γR.toMonoidHom x.2) ^ n.2 *
          (Units.map γR.toMonoidHom x.1) ^ n.1 : Rˣ) =
      γR (algebraMap K R c * (x.1 ^ n.1 * x.2 ^ n.2 : Rˣ))
    rw [← hγ c]
    simp only [← map_zpow, Units.val_mul, Units.coe_map, map_mul]
    ac_rfl

end Evaluation

/-- The subalgebra fixed by coefficient conjugation and exchange of characters. -/
def fixedRing (γ : K ≃ₐ[F] K) : Subalgebra F (LaurentRing (K := K)) :=
  AlgHom.equalizer (conjugate γ).toAlgHom (AlgHom.id F _)

/-- Elements of the cover coordinate ring fixed by both relevant actions. -/
def fixedInvariantRing (γ : K ≃ₐ[F] K) (ζ : Kˣ) : Subalgebra F (LaurentRing (K := K)) :=
  fixedRing γ ⊓ (invariantRing ζ).restrictScalars F

/-- Restriction of the quotient-character pullback to the fixed subalgebras. -/
def fixedPullbackHom (γ : K ≃ₐ[F] K) (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    fixedRing γ →ₐ[F] fixedInvariantRing γ ζ :=
  ((pullbackHom.restrictScalars F).comp (fixedRing γ).val).codRestrict _ (by
    intro f
    constructor
    · change conjugate γ (pullbackHom (f : LaurentRing (K := K))) = pullbackHom f
      rw [conjugate_pullback, show conjugate γ (f : LaurentRing (K := K)) = f from f.property]
    · change pullbackHom (f : LaurentRing (K := K)) ∈ invariantRing ζ
      rw [← range_pullbackHom ζ hζ]
      exact ⟨f, rfl⟩)

theorem fixedPullbackHom_bijective (γ : K ≃ₐ[F] K) (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    Function.Bijective (fixedPullbackHom γ ζ hζ) := by
  constructor
  · intro f g h
    apply Subtype.ext
    apply pullbackHom_injective
    exact congrArg Subtype.val h
  · intro y
    have hy : (y : LaurentRing (K := K)) ∈ invariantRing ζ := y.property.2
    rw [← range_pullbackHom ζ hζ] at hy
    obtain ⟨x, hx⟩ := hy
    change pullbackHom x = (y : LaurentRing (K := K)) at hx
    have hxfix : conjugate γ x = x := by
      apply pullbackHom_injective
      rw [← conjugate_pullback, hx]
      exact y.property.1
    exact ⟨⟨x, hxfix⟩, Subtype.ext hx⟩

/-- The quotient Laurent presentation descends at the level of fixed rings. -/
def fixedQuotientEquiv (γ : K ≃ₐ[F] K) (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    fixedRing γ ≃ₐ[F] fixedInvariantRing γ ζ :=
  AlgEquiv.ofBijective (fixedPullbackHom γ ζ hζ) (fixedPullbackHom_bijective γ ζ hζ)

end Cubic.QuadraticCorrespondence.SplitLaurentGalois
