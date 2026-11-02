import Cubic.OrbitParametrization.NormalUnit
import Cubic.QuadraticCorrespondence.DescendedCoefficients

/-!
# From a `C₃`-algebra with a trace-one normal element to a rational point

This is the map `γ₂` of [O'Desky–Rosen, Prop. 2.4, second proof]. By Lemma 2.2
(`NormalUnit`), `x` gives an augmentation-one unit `u` of `K[C₃]`, i.e. a
`K`-point of the cover. Its image in the quotient is fixed by `C₃`, because `C₃`
acts on `u` by left multiplication by `[g]`, and so it is rational.

The characteristic polynomial of the point is `(t-x)(t-σx)(t-σ²x)`.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open CyclicGroupAlgebra Polynomial
open Cubic.QuadraticCorrespondence Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open Cubic.QuadraticCorrespondence.RationalQuotientFunctor DescendedCoefficients

/-- The `K`-point of the quotient given by a pair. -/
def pointOver (p : Pair) : quotientFixedRing →ₐ[ℚ] p.algebra.carrier :=
  quotientPoint p.algebra.carrier (unitOf p)

theorem pointOver_fixed (p : Pair) (h : C3) (b : quotientFixedRing) :
    p.algebra.act h (pointOver p b) = pointOver p b := by
  have hm := quotientPoint_mapUnits p.algebra.carrier (p.algebra.act h).toAlgHom (unitOf p)
  have hc := congrArg (fun g => quotientPoint p.algebra.carrier g b)
    (mapUnits_act p h)
  simp only [quotientPoint_cyclic_mul] at hc
  rw [show (p.algebra.act h).toAlgHom.toRingHom = (p.algebra.act h).toRingEquiv.toRingHom from rfl,
    ] at hm
  rw [hm] at hc
  exact hc

theorem pointOver_rational (p : Pair) (b : quotientFixedRing) :
    pointOver p b ∈ (⊥ : Subalgebra ℚ p.algebra.carrier) := by
  obtain ⟨q, hq⟩ := fixed_rational p.algebra _ (fun h => pointOver_fixed p h b)
  exact hq ▸ Subalgebra.algebraMap_mem _ q

/-- The rational point `γ₂(K,x)`. -/
def point (p : Pair) : quotientFixedRing →ₐ[ℚ] ℚ :=
  (Algebra.botEquiv ℚ p.algebra.carrier).toAlgHom.comp
    ((pointOver p).codRestrict ⊥ (pointOver_rational p))

theorem algebraMap_point (p : Pair) (b : quotientFixedRing) :
    algebraMap ℚ p.algebra.carrier (point p b) = pointOver p b := by
  have h := (Algebra.botEquiv ℚ p.algebra.carrier).symm_apply_apply
    ((pointOver p).codRestrict ⊥ (pointOver_rational p) b)
  rw [Algebra.botEquiv_symm_apply] at h
  exact congrArg Subtype.val h

/-- The characteristic polynomial of `γ₂(K,x)` is that of `x`. -/
theorem characteristicPolynomial_point (p : Pair) :
    (characteristicPolynomial (point p)).map (algebraMap ℚ p.algebra.carrier) =
      (X - C p.element) * (X - C (p.algebra.act σ p.element)) *
        (X - C (p.algebra.act (σ ^ 2) p.element)) := by
  have htr : p.element + p.algebra.act σ p.element + p.algebra.act (σ ^ 2) p.element = 1 := by
    rw [← traceSum_eq]
    exact p.traceOne
  have ha := algebraMap_point p linearCoefficient
  have hb := algebraMap_point p constantCoefficient
  rw [pointOver, quotientPoint_linearCoefficient] at ha
  rw [pointOver, quotientPoint_constantCoefficient] at hb
  simp only [unitOf_val, unitElement_apply] at ha hb
  rw [show Multiplicative.ofAdd (-(0 : ZMod 3)) = (1 : C3) by decide, map_one,
    show Multiplicative.ofAdd (-(1 : ZMod 3)) = σ ^ 2 by decide,
    show Multiplicative.ofAdd (-(2 : ZMod 3)) = σ by decide] at ha hb
  simp only [characteristicPolynomial, CorrespondencePolynomials.cubic, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, ha, hb,
    secondCoeff, constantCoeff, AlgEquiv.one_apply]
  have hC : C (1 : p.algebra.carrier) = C (p.element + p.algebra.act σ p.element +
      p.algebra.act (σ ^ 2) p.element) := by rw [htr]
  rw [show (X : p.algebra.carrier[X]) ^ 2 = X ^ 2 * C 1 by simp, hC]
  simp only [C_add, C_mul, C_neg]
  ring

end Cubic.OrbitParametrization.C3Algebra
