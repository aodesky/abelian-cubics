import Cubic.OrbitParametrization.FibrePair
import CubicTargets.OrbitParametrization.ModularInterpretation

/-!
# `thm:modularInterpretation`

The paper cites [O'Desky–Rosen, §2, Prop. 2.4]. We follow its second proof with
`R = ℚ`, `A` the cover coordinate ring and `A^G` the quotient ring.

* `γ₂` (`point`): a pair `(K,x)` gives, by Lemma 2.2 (`NormalUnit`), the
  `C₃`-equivariant map `f : A → K` with `f(X₁) = x`; its restriction to `A^G` is
  rational (`ModuliMap`).
* Every rational point arises: `γ₁(P)` is the fibre algebra `A ⊗_{A^G,P} ℚ`
  (`FibreAlgebra`), a `C₃`-algebra with trace-one normal element `X̄₁`
  (`FibrePair`), and `γ₂(γ₁(P)) = P` (`point_fibrePair`).
* Pairs with the same point are equivalent (`γ₁ ∘ γ₂ ≅ id`): the equivariant map
  `f̃ : A ⊗_{A^G,P} ℚ → K` carries the coordinate basis to the normal basis, so it
  is an isomorphism (`pairFibreEquiv`); composing two of them gives the
  equivalence.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open CyclicGroupAlgebra Polynomial
open Cubic.QuadraticCorrespondence Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open Cubic.QuadraticCorrespondence.RationalCoverFunctor Cubic.QuadraticCorrespondence.RationalQuotientFunctor
open DescendedCoefficients

/-- The conjugates of a normal element form a basis. -/
def normalBasis (p : Pair) : Module.Basis C3 ℚ p.algebra.carrier :=
  Module.Basis.mk p.normal (by
    rw [p.normal.span_eq_top_of_card_eq_finrank (by rw [finrank_eq_three]; rfl)])

theorem normalBasis_apply (p : Pair) (g : C3) : normalBasis p g = p.algebra.act g p.element := by
  simp [normalBasis]

theorem pointOver_eq (p : Pair) (P : quotientFixedRing →ₐ[ℚ] ℚ) (hP : point p = P) :
    quotientPoint p.algebra.carrier (unitOf p) = (Algebra.ofId ℚ p.algebra.carrier).comp P := by
  ext b
  rw [← hP]
  exact (algebraMap_point p b).symm

/-- The source's map `f̃ : γ₁(γ₂(K,x)) = A ⊗_{A^G,P} ℚ → K`, induced by the equivariant map
`A → K` sending `X₁` to `x`. -/
def pairFibreHom (p : Pair) (P : quotientFixedRing →ₐ[ℚ] ℚ) (hP : point p = P) :
    Fibre P →ₐ[ℚ] p.algebra.carrier :=
  fibreHom P (unitOf p) (pointOver_eq p P hP)

theorem pairFibreHom_coord (p : Pair) (P : quotientFixedRing →ₐ[ℚ] ℚ) (hP : point p = P)
    (i : ZMod 3) : pairFibreHom p P hP (fibreCoord P i) =
      p.algebra.act (Multiplicative.ofAdd (-i)) p.element := by
  rw [pairFibreHom, fibreHom_coord, unitOf_val, unitElement_apply]

/-- `f̃` is `C₃`-equivariant. -/
theorem pairFibreHom_equivariant (p : Pair) (P : quotientFixedRing →ₐ[ℚ] ℚ) (hP : point p = P)
    (g : C3) (s : Fibre P) :
    pairFibreHom p P hP (fibreActHom P g s) = p.algebra.act g (pairFibreHom p P hP s) := by
  have hlin : (pairFibreHom p P hP).toLinearMap.comp (fibreActHom P g).toLinearMap =
      (p.algebra.act g).toLinearMap.comp (pairFibreHom p P hP).toLinearMap := by
    apply (fibreBasis P).ext
    intro i
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
      AlgHom.toLinearMap_apply]
    rw [show fibreBasis P i = fibreCoord P i by simp [fibreBasis], ← ofAdd_toAdd g,
      fibreActHom_coord, pairFibreHom_coord, pairFibreHom_coord, ← AlgEquiv.mul_apply, ← map_mul]
    congr 2
    rw [← ofAdd_add]
    congr 1
    abel
  exact congrArg (fun φ : Fibre P →ₗ[ℚ] p.algebra.carrier => φ s) hlin

/-- `f̃` carries the coordinate basis to the normal basis, so it is an isomorphism:
an equivariant map of `C₃`-torsors is an isomorphism. -/
theorem pairFibreHom_bijective (p : Pair) (P : quotientFixedRing →ₐ[ℚ] ℚ) (hP : point p = P) :
    Function.Bijective (pairFibreHom p P hP) := by
  have hsurj : Function.Surjective (pairFibreHom p P hP) := by
    intro k
    rw [← (normalBasis p).sum_repr k]
    refine ⟨∑ g : C3, (normalBasis p).repr k g • fibreCoord P (-(Multiplicative.toAdd g)), ?_⟩
    simp only [map_sum, map_smul, pairFibreHom_coord, neg_neg, ofAdd_toAdd, normalBasis_apply]
  have hinj : Function.Injective (pairFibreHom p P hP) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (pairFibreHom p P hP).toLinearMap)
      (by rw [fibre_finrank, finrank_eq_three])).mpr hsurj
  exact ⟨hinj, hsurj⟩

def pairFibreEquiv (p : Pair) (P : quotientFixedRing →ₐ[ℚ] ℚ) (hP : point p = P) :
    Fibre P ≃ₐ[ℚ] p.algebra.carrier :=
  AlgEquiv.ofBijective (pairFibreHom p P hP) (pairFibreHom_bijective p P hP)

/-- Pairs with the same rational point are equivalent: `γ₁ ∘ γ₂ ≅ id`. -/
theorem equivalent_of_point_eq (p q : Pair) (h : point p = point q) : Equivalent p q := by
  let ep := pairFibreEquiv p (point p) rfl
  let eq := pairFibreEquiv q (point p) h.symm
  have hep : ∀ t, ep t = pairFibreHom p (point p) rfl t := fun t => rfl
  have heq : ∀ t, eq t = pairFibreHom q (point p) h.symm t := fun t => rfl
  refine ⟨ep.symm.trans eq, fun g y => ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := ep.surjective y
    simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    rw [hep, ← pairFibreHom_equivariant, ← hep, AlgEquiv.symm_apply_apply, heq, heq,
      pairFibreHom_equivariant]
  · have hx : ep (fibreCoord (point p) 0) = p.element := by
      rw [hep, pairFibreHom_coord, neg_zero, show Multiplicative.ofAdd (0 : ZMod 3) = 1 from rfl,
        map_one]
      rfl
    rw [AlgEquiv.trans_apply, ← hx, AlgEquiv.symm_apply_apply, heq, pairFibreHom_coord, neg_zero,
      show Multiplicative.ofAdd (0 : ZMod 3) = 1 from rfl, map_one]
    rfl

/-- Equivalent pairs have the same rational point. -/
theorem point_eq_of_equivalent (p q : Pair) (h : Equivalent p q) : point p = point q := by
  obtain ⟨e, he, hx⟩ := h
  have hunit : mapUnits e.toAlgHom.toRingHom (unitOf p) = unitOf q := by
    apply Subtype.ext
    apply Units.ext
    ext i
    rw [mapUnits_coefficient, unitOf_val, unitOf_val, unitElement_apply, unitElement_apply]
    change e (p.algebra.act _ p.element) = _
    rw [he, hx]
  apply AlgHom.ext
  intro b
  apply (algebraMap ℚ q.algebra.carrier).injective
  have hq := congrArg (fun φ : quotientFixedRing →ₐ[ℚ] q.algebra.carrier => φ b)
    (quotientPoint_mapUnits p.algebra.carrier e.toAlgHom (unitOf p))
  simp only at hq
  rw [hunit] at hq
  rw [algebraMap_point, pointOver, hq, AlgHom.comp_apply, ← pointOver, ← algebraMap_point]
  exact (e.commutes _).symm

/-- Every rational point arises: `γ₂(γ₁(P)) = P`. -/
theorem point_surjective : Function.Surjective point :=
  fun P => ⟨fibrePair P, point_fibrePair P⟩

theorem «thm:modularInterpretation» :
    CubicTargets.OrbitParametrization.ModularInterpretation.Claim := by
  refine ⟨point, point_surjective, fun p q =>
    ⟨equivalent_of_point_eq p q, point_eq_of_equivalent p q⟩, ?_⟩
  refine ⟨fun p => ?_, fun p => ⟨unitOf p, rfl, fun b => algebraMap_point p b⟩⟩
  have hprod : ∏ g : C3, (X - C (p.algebra.act g p.element)) =
      (X - C p.element) * (X - C (p.algebra.act σ p.element)) *
        (X - C (p.algebra.act (σ ^ 2) p.element)) := by
    rw [← Equiv.prod_comp Multiplicative.ofAdd]
    refine (Fin.prod_univ_three
      (fun i : ZMod 3 => X - C (p.algebra.act (Multiplicative.ofAdd i) p.element))).trans ?_
    rw [show Multiplicative.ofAdd (0 : ZMod 3) = (1 : C3) from rfl,
      show Multiplicative.ofAdd (2 : ZMod 3) = σ ^ 2 by decide, map_one]
    rfl
  rw [hprod]
  exact characteristicPolynomial_point p

end Cubic.OrbitParametrization.C3Algebra
