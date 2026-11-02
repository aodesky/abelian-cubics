import Cubic.Introduction.IntegralEisenstein
import Cubic.Counting.CyclicCubicField
import Cubic.QuadraticCorrespondence.QuotientPolynomialConverse
import Cubic.QuadraticCorrespondence.QuotientCubicClassification

/-! The resolvent is a cube exactly in the split case. The forward
calculation is Cardano's rational root `(1+Tr(r))/3`; conversely the
Lagrange resolvent of three rational roots cubes to one of the two
conjugate oriented parameters. -/

noncomputable section

namespace Cubic.Introduction.ResolventCubes

open EisensteinPointData IntegralEisenstein
open Cubic.QuadraticCorrespondence CyclotomicField CyclotomicTorusGalois
open DescendedCoefficients RationalCoefficientFormula CorrespondencePolynomials
open Cubic.ToricHeights AffinePointComparison
open Cubic.OrbitParametrization (secondCoeff)
open Polynomial

theorem trace_resolvent (α : E) :
    Algebra.trace ℚ E (EisensteinPointData.resolvent α) =
      Algebra.norm ℚ α * Algebra.trace ℚ E α := by
  apply (algebraMap ℚ E).injective
  simp only [EisensteinPointData.resolvent, trace_eq_add_conjugation,
    map_mul, AlgEquiv.commutes]
  ring

theorem trace_cube (r : E) :
    Algebra.trace ℚ E (r ^ 3) =
      Algebra.trace ℚ E r ^ 3 - 3 * Algebra.norm ℚ r * Algebra.trace ℚ E r := by
  apply (algebraMap ℚ E).injective
  simp only [trace_eq_add_conjugation, norm_eq_mul_conjugation, map_pow,
    map_sub, map_mul, map_ofNat]
  ring

theorem root_of_cube (P : TorusPoints) {r : E} (hr : r ^ 3 = pointResolvent P) :
    IsRoot (characteristicPolynomial P) ((1 + Algebra.trace ℚ E r) / 3) := by
  have hn : Algebra.norm ℚ r = Algebra.norm ℚ (parameterEquiv P : E) := by
    apply (show Odd 3 by decide).pow_injective
    have h := congrArg (Algebra.norm ℚ) hr
    simpa only [map_pow, pointResolvent, norm_resolvent] using h
  have ht := congrArg (Algebra.trace ℚ E) hr
  rw [trace_cube, pointResolvent, trace_resolvent, hn] at ht
  rw [IsRoot.def, characteristicPolynomial_eq]
  simp only [cubic, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination ht / 27

theorem point_trace (P : TorusPoints) :
    Algebra.trace ℚ E (pointResolvent P) =
      2 - 9 * P linearCoefficient - 27 * P constantCoefficient := by
  rw [pointResolvent, trace_resolvent, linearCoefficient_eq, constantCoefficient_eq]
  ring

theorem cube_of_splits (P : TorusPoints) (hs : (characteristicPolynomial P).Splits) :
    ∃ r : E, r ^ 3 = pointResolvent P := by
  let C : _root_.Cubic ℚ := ⟨1, -1, P linearCoefficient, P constantCoefficient⟩
  have hC : C.a ≠ 0 := one_ne_zero
  have hpoly : C.toPoly = characteristicPolynomial P := by
    simp [C, _root_.Cubic.toPoly, characteristicPolynomial, cubic, sub_eq_add_neg]
  have hs' : (C.toPoly.map (RingHom.id ℚ)).Splits := by
    simpa only [Polynomial.map_id, hpoly] using hs
  obtain ⟨x, y, z, h3⟩ := (_root_.Cubic.splits_iff_roots_eq_three hC).mp hs'
  have hsum : x + y + z = 1 := by
    have h := _root_.Cubic.b_eq_three_roots hC h3
    simp only [C, RingHom.id_apply, one_mul] at h
    linarith
  have hsecond : secondCoeff x y z = P linearCoefficient := by
    have h := _root_.Cubic.c_eq_three_roots hC h3
    simp only [C, RingHom.id_apply, one_mul] at h
    dsimp [secondCoeff]
    linear_combination -h
  have hthird : x * y * z = -P constantCoefficient := by
    have h := _root_.Cubic.d_eq_three_roots hC h3
    simp only [C, RingHom.id_apply, one_mul] at h
    linarith
  let r : E := algebraMap ℚ E x + algebraMap ℚ E y * zeta +
    algebraMap ℚ E z * zeta ^ 2
  let t : E := algebraMap ℚ E x + algebraMap ℚ E y * zeta ^ 2 +
    algebraMap ℚ E z * zeta
  have hsumE : algebraMap ℚ E x + algebraMap ℚ E y + algebraMap ℚ E z = 1 := by
    simpa only [map_add, map_one] using congrArg (algebraMap ℚ E) hsum
  have hsecondE : secondCoeff (algebraMap ℚ E x) (algebraMap ℚ E y)
      (algebraMap ℚ E z) = algebraMap ℚ E (P linearCoefficient) := by
    simpa only [secondCoeff, map_add, map_mul] using congrArg (algebraMap ℚ E) hsecond
  have hthirdE : algebraMap ℚ E x * algebraMap ℚ E y * algebraMap ℚ E z =
      -algebraMap ℚ E (P constantCoefficient) := by
    simpa only [map_mul, map_neg] using congrArg (algebraMap ℚ E) hthird
  have hprod : r * t = algebraMap ℚ E (1 - 3 * P linearCoefficient) := by
    dsimp [r, t]
    rw [TraceOneCharacters.eigenvalue_product zeta zeta_relation, hsumE, hsecondE]
    simp
  have hcubes : r ^ 3 + t ^ 3 =
      algebraMap ℚ E (2 - 9 * P linearCoefficient - 27 * P constantCoefficient) := by
    dsimp [r, t]
    rw [TraceOneCharacters.eigenvalue_cubes_sum zeta zeta_relation, hsumE, hsecondE]
    have hthirdE' := hthirdE
    simp only [one_pow, mul_one, map_sub, map_mul, map_ofNat]
    linear_combination 27 * hthirdE'
  let β := pointResolvent P
  have hb := quadratic_norm_trace β
  have hN : Algebra.norm ℚ β = (1 - 3 * P linearCoefficient) ^ 3 := by
    dsimp [β]
    rw [pointResolvent, norm_resolvent, norm_parameter]
  have hz : (β - r ^ 3) * (β - t ^ 3) = 0 := by
    calc
      _ = β ^ 2 - (r ^ 3 + t ^ 3) * β + (r * t) ^ 3 := by ring
      _ = 0 := by
        rw [hcubes, hprod, ← map_pow, ← hN, ← point_trace]
        exact hb
  rcases mul_eq_zero.mp hz with h | h
  · exact ⟨r, (sub_eq_zero.mp h).symm⟩
  · exact ⟨t, (sub_eq_zero.mp h).symm⟩

theorem cyclic_iff_nonCube (P : TorusPoints) :
    HasCyclicCubicGaloisGroup (characteristicPolynomial P) ↔
      ¬ ∃ r : E, r ^ 3 = pointResolvent P := by
  constructor
  · rintro hc ⟨r, hr⟩
    exact Cubic.Counting.CyclicCubicField.not_isRoot_of_cyclic _ _ hc _
      (root_of_cube P hr)
  · intro h
    rcases QuotientCubicClassification.cyclic_or_splits P with hc | hs
    · exact hc
    · exact False.elim (h (cube_of_splits P hs))

end Cubic.Introduction.ResolventCubes
