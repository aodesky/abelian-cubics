import Cubic.QuadraticCorrespondence.GeometricQuotientFibres
import Cubic.QuadraticCorrespondence.DescendedCoefficients
import Mathlib.Algebra.CharZero.Infinite

/-!
# Galois action on a geometric lift of a rational quotient point

Every automorphism acts on a lift by an element of the original cyclic group.
The three coefficients of that lift are the roots of the descended cubic.
These statements retain the original cover and invariant-ring map, including
the possible repeated-root case.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuotientGaloisAction

open CyclotomicField CyclotomicTorusGalois RationalQuotientFunctor
open GeometricQuotientFibres DescendedCoefficients
open Cubic.OrbitParametrization Cubic.OrbitParametrization.CyclicGroupAlgebra
open Polynomial

variable {K : Type*} [Field K] [CharZero K]
  [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]

/-- The scalar extension of the rational quotient point. -/
def pointOver (p : quotientFixedRing →ₐ[ℚ] ℚ) : quotientFixedRing →ₐ[ℚ] K :=
  (Algebra.ofId ℚ K).comp p

theorem exists_cyclic_shift (p : quotientFixedRing →ₐ[ℚ] ℚ) (g : traceOneUnits K)
    (hg : quotientPoint K g = pointOver p) (σ : K ≃ₐ[ℚ] K) :
    ∃ i, mapUnits σ.toAlgHom.toRingHom g = cyclicUnits K i * g := by
  apply (quotientPoint_eq_iff _ _).mp
  rw [quotientPoint_mapUnits K σ.toAlgHom, hg]
  ext b
  exact σ.commutes (p b)

/-- The cube of any Galois automorphism fixes the whole original cover lift. -/
theorem cube_fixes_lift (p : quotientFixedRing →ₐ[ℚ] ℚ) (g : traceOneUnits K)
    (hg : quotientPoint K g = pointOver p) (σ : K ≃ₐ[ℚ] K) :
    mapUnits (σ ^ 3).toAlgHom.toRingHom g = g := by
  obtain ⟨i, hi⟩ := exists_cyclic_shift p g hg σ
  have hi3 : i ^ 3 = 1 := by
    simpa only [show Fintype.card (Multiplicative (ZMod 3)) = 3 from by decide] using
      pow_card_eq_one (x := i)
  change mapUnits (σ.toAlgHom.toRingHom.comp (σ.toAlgHom.toRingHom.comp σ.toAlgHom.toRingHom)) g = g
  rw [mapUnits_comp, mapUnits_comp, hi, map_mul, mapUnits_cyclicUnits, hi,
    map_mul, mapUnits_cyclicUnits, map_mul, mapUnits_cyclicUnits, hi]
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← pow_two, ← pow_succ, hi3,
    map_one, one_mul]

omit [Algebra E K] [IsScalarTower ℚ E K] in
/-- Factorization of the descended cubic by the coordinates of any lift. -/
theorem polynomial_eq_prod (p : quotientFixedRing →ₐ[ℚ] ℚ) (g : traceOneUnits K)
    (hg : quotientPoint K g = pointOver p) :
    (characteristicPolynomial p).map (algebraMap ℚ K) =
      (X - C ((g.val : GroupAlgebra K) 0)) *
      (X - C ((g.val : GroupAlgebra K) 1)) *
      (X - C ((g.val : GroupAlgebra K) 2)) := by
  have ha := quotientPoint_linearCoefficient g
  have hb := quotientPoint_constantCoefficient g
  rw [hg] at ha hb
  change algebraMap ℚ K (p linearCoefficient) = _ at ha
  change algebraMap ℚ K (p constantCoefficient) = _ at hb
  apply Polynomial.funext
  intro t
  simp only [characteristicPolynomial, CorrespondencePolynomials.cubic, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, ha, hb]
  exact traceOneCubic_eq_prod _ _ _ t (trace_one K g)

omit [Algebra E K] [IsScalarTower ℚ E K] in
theorem mem_rootSet_iff (p : quotientFixedRing →ₐ[ℚ] ℚ) (g : traceOneUnits K)
    (hg : quotientPoint K g = pointOver p) (x : K) :
    x ∈ (characteristicPolynomial p).rootSet K ↔
      x = (g.val : GroupAlgebra K) 0 ∨ x = (g.val : GroupAlgebra K) 1 ∨
        x = (g.val : GroupAlgebra K) 2 := by
  rw [Polynomial.mem_rootSet]
  have hn : characteristicPolynomial p ≠ 0 := by
    intro h
    have h3 := congrArg (fun f : ℚ[X] => f.coeff 3) h
    norm_num [characteristicPolynomial, CorrespondencePolynomials.cubic] at h3
  simp only [hn, ne_eq, not_false_eq_true, true_and, aeval_def, ← eval_map,
    polynomial_eq_prod p g hg, eval_mul, eval_sub, eval_X, eval_C,
    mul_eq_zero, sub_eq_zero, or_assoc]

end Cubic.QuadraticCorrespondence.QuotientGaloisAction
