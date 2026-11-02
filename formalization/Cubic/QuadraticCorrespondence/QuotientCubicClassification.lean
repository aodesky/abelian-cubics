import Cubic.QuadraticCorrespondence.QuotientGaloisAction
import Cubic.QuadraticCorrespondence.SmallGaloisGroup
import Cubic.QuadraticCorrespondence.RationalCoefficientFormula
import CubicTargets.QuadraticCorrespondence.QuotientCubicClassification
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The descended cubics are cyclic or rationally split

Lift a rational quotient point to the original cover over an algebraic
closure. Galois acts on its fibre through the original cyclic action. Since
the cover coordinates are exactly the cubic roots, the splitting-field Galois
group has at most three elements, and every element cubes to one. This proves
the classification used by `prop:cyclotomicParametrization` and the real-root
argument in `lemma:rootVsToric`, without using the moduli interpretation of the quotient.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuotientCubicClassification

open CyclotomicField CyclotomicTorusGalois RationalQuotientFunctor
open GeometricQuotientFibres DescendedCoefficients QuotientGaloisAction
open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Polynomial

section Geometric

variable {K : Type*} [Field K] [CharZero K]
  [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K] [IsAlgClosed K]
  (p : quotientFixedRing →ₐ[ℚ] ℚ)

local instance : Fact (((characteristicPolynomial p).map (algebraMap ℚ K)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

omit [Algebra E K] [IsScalarTower ℚ E K] in
/-- Agreement on a cover lift implies agreement on the entire splitting field. -/
theorem restrict_eq_of_lift_eq (g : traceOneUnits K) (hg : quotientPoint K g = pointOver p)
    (σ τ : K ≃ₐ[ℚ] K)
    (h : mapUnits σ.toAlgHom.toRingHom g = mapUnits τ.toAlgHom.toRingHom g) :
    Polynomial.Gal.restrict (characteristicPolynomial p) K σ =
      Polynomial.Gal.restrict (characteristicPolynomial p) K τ := by
  apply Polynomial.Gal.galActionHom_injective (characteristicPolynomial p) K
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [Polynomial.Gal.galActionHom_restrict]
  have hc (i : ZMod 3) : σ ((g.val : GroupAlgebra K) i) =
      τ ((g.val : GroupAlgebra K) i) :=
    congrArg (fun u : traceOneUnits K => (u.val : GroupAlgebra K) i) h
  rcases (QuotientGaloisAction.mem_rootSet_iff p g hg x).mp x.property with hx | hx | hx
  · rw [hx]; exact hc 0
  · rw [hx]; exact hc 1
  · rw [hx]; exact hc 2

variable [Normal ℚ K]

/-- The original geometric cyclic fibre bounds the polynomial Galois group. -/
theorem galois_card_le_three (g : traceOneUnits K) (hg : quotientPoint K g = pointOver p) :
    Fintype.card (characteristicPolynomial p).Gal ≤ 3 := by
  classical
  choose σ hσ using Polynomial.Gal.restrict_surjective (characteristicPolynomial p) K
  choose i hi using fun τ => exists_cyclic_shift p g hg (σ τ)
  have hinj : Function.Injective i := by
    intro τ υ h
    rw [← hσ τ, ← hσ υ]
    apply restrict_eq_of_lift_eq p g hg
    rw [hi, hi, h]
  simpa only [show Fintype.card (Multiplicative (ZMod 3)) = 3 from by decide] using
    Fintype.card_le_of_injective i hinj

theorem galois_cube_eq_one (g : traceOneUnits K) (hg : quotientPoint K g = pointOver p)
    (τ : (characteristicPolynomial p).Gal) : τ ^ 3 = 1 := by
  obtain ⟨σ, rfl⟩ := Polynomial.Gal.restrict_surjective (characteristicPolynomial p) K τ
  rw [← map_pow]
  calc
    Polynomial.Gal.restrict (characteristicPolynomial p) K (σ ^ 3) =
        Polynomial.Gal.restrict (characteristicPolynomial p) K 1 := by
      apply restrict_eq_of_lift_eq p g hg
      simpa only [show (1 : K ≃ₐ[ℚ] K).toAlgHom.toRingHom = RingHom.id K from rfl,
        mapUnits_id] using cube_fixes_lift p g hg σ
    _ = 1 := map_one _

end Geometric

/-- The classification comes from the original cyclic quotient, including nonseparable cubics. -/
theorem cyclic_or_splits (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    CorrespondencePolynomials.HasCyclicCubicGaloisGroup (characteristicPolynomial p) ∨
      (characteristicPolynomial p).Splits := by
  obtain ⟨g, hg⟩ := quotientPoint_surjective (K := AlgebraicClosure E) (pointOver p)
  exact SmallGaloisGroup.cyclic_or_splits (characteristicPolynomial p)
    (galois_card_le_three p g hg) (galois_cube_eq_one p g hg)

/-- A triple root would force the nonzero character norm `1-3a` to vanish. -/
theorem not_triple_root (p : quotientFixedRing →ₐ[ℚ] ℚ) :
    ¬ ∃ r : ℚ, characteristicPolynomial p = (X - C r) ^ 3 := by
  rintro ⟨r, hr⟩
  have he : (X - C r) ^ 3 =
      X ^ 3 - C (3 * r) * X ^ 2 + C (3 * r ^ 2) * X - C (r ^ 3) := by
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [he] at hr
  have h2 := congrArg (fun f : ℚ[X] => f.coeff 2) hr
  have h1 := congrArg (fun f : ℚ[X] => f.coeff 1) hr
  simp only [characteristicPolynomial, CorrespondencePolynomials.cubic,
    coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h2 h1
  norm_num at h2 h1
  apply RationalCoefficientFormula.inverse_denominator_ne_zero p
  nlinarith [sq_nonneg (r - 1 / 3)]

theorem claim : CubicTargets.QuadraticCorrespondence.QuotientCubicClassification.Claim := by
  intro p
  exact ⟨cyclic_or_splits p, not_triple_root p⟩

end Cubic.QuadraticCorrespondence.QuotientCubicClassification
