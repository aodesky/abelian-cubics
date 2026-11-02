import Cubic.QuadraticCorrespondence.QuotientPolynomialMultiplicity
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Every admissible cubic comes from a rational quotient point

This is the converse clause of `prop:cyclotomicParametrization`. The paper's
proof only says that the relations may be solved for `N` and `T` because
`N ≠ 0`; it does not show that `N ≠ 0` for an arbitrary admissible cubic, or
that the inverse quadratic has its roots in `E`. Both follow from the fact
that the discriminant of an admissible cubic is a rational square:

* split case: it is the square of the product of root differences;
* cyclic case: that product lies in a splitting field of degree three, and its
  square is rational, so its minimal polynomial has degree one.

The inverse quadratic has discriminant `-27 disc(f) / N²`, which is then `-3`
times a rational square, hence a square in `E`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.QuotientPolynomialConverse

open CyclotomicField DescendedCoefficients RationalCoefficientFormula
open CorrespondencePolynomials QuotientPolynomialFibres Polynomial

/-- The cubic `t³ - t² + at + b` in mathlib's cubic-coefficient form. -/
private def cubicData (a b : ℚ) : _root_.Cubic ℚ := ⟨1, -1, a, b⟩

private theorem toPoly_cubicData (a b : ℚ) : (cubicData a b).toPoly = cubic a b := by
  simp [cubicData, _root_.Cubic.toPoly, cubic, sub_eq_add_neg]

private theorem cubicData_a (a b : ℚ) : (cubicData a b).a ≠ 0 := one_ne_zero

private theorem cubic_ne_zero (a b : ℚ) : cubic a b ≠ 0 := by
  rw [← toPoly_cubicData]
  exact _root_.Cubic.ne_zero_of_a_ne_zero (cubicData_a a b)

theorem discr_square_of_splits {a b : ℚ} (h : (cubic a b).Splits) :
    ∃ d : ℚ, (cubicData a b).discr = d ^ 2 := by
  have hs : ((cubicData a b).toPoly.map (RingHom.id ℚ)).Splits := by
    rw [toPoly_cubicData, Polynomial.map_id]
    exact h
  obtain ⟨x, y, z, h3⟩ := (_root_.Cubic.splits_iff_roots_eq_three (cubicData_a a b)).mp hs
  refine ⟨(x - y) * (x - z) * (y - z), ?_⟩
  have := _root_.Cubic.discr_eq_prod_three_roots (cubicData_a a b) h3
  simpa [cubicData] using this

/-- A separable cubic whose Galois group is cyclic of order three has square discriminant. -/
theorem discr_square_of_cyclic {a b : ℚ} (h : HasCyclicCubicGaloisGroup (cubic a b)) :
    ∃ d : ℚ, (cubicData a b).discr = d ^ 2 := by
  by_cases h0 : (cubicData a b).discr = 0
  · exact ⟨0, by rw [h0]; ring⟩
  let L := (cubic a b).SplittingField
  have hsL : (cubic a b).map (algebraMap ℚ L) |>.Splits := SplittingField.splits (cubic a b)
  have hs : ((cubicData a b).toPoly.map (algebraMap ℚ L)).Splits := by
    rw [toPoly_cubicData]
    exact hsL
  obtain ⟨x, y, z, h3⟩ := (_root_.Cubic.splits_iff_roots_eq_three (cubicData_a a b)).mp hs
  -- Nonzero discriminant gives separability, so the Galois group has order `[L : ℚ]`.
  have hsep : (cubic a b).Separable := by
    have hnd := (_root_.Cubic.discr_ne_zero_iff_roots_nodup (cubicData_a a b) hs).mp h0
    rw [_root_.Cubic.roots, _root_.Cubic.map_toPoly, toPoly_cubicData] at hnd
    rwa [nodup_roots_iff_of_splits (map_ne_zero (cubic_ne_zero a b)) hsL, separable_map] at hnd
  have hfin : Module.finrank ℚ L = 3 := by
    obtain ⟨e⟩ := h
    rw [← Polynomial.Gal.card_of_separable hsep, Nat.card_congr e.toEquiv]
    simp
  -- The product of root differences squares to the rational discriminant.
  set δ : L := (x - y) * (x - z) * (y - z)
  have hδ : algebraMap ℚ L (cubicData a b).discr = δ ^ 2 := by
    have := _root_.Cubic.discr_eq_prod_three_roots (cubicData_a a b) h3
    simpa [cubicData, δ, mul_assoc] using this
  have hint : IsIntegral ℚ δ := Algebra.IsIntegral.isIntegral δ
  have hle : (minpoly ℚ δ).natDegree ≤ 2 := by
    have hp : aeval δ (X ^ 2 - C (cubicData a b).discr) = 0 := by
      simp [hδ]
    calc (minpoly ℚ δ).natDegree ≤ (X ^ 2 - C (cubicData a b).discr).natDegree :=
          natDegree_le_of_dvd (minpoly.dvd ℚ δ hp) (X_pow_sub_C_ne_zero two_pos _)
      _ = 2 := natDegree_X_pow_sub_C
  have hdvd := minpoly.degree_dvd hint
  rw [hfin] at hdvd
  have hpos := minpoly.natDegree_pos hint
  have h1 : (minpoly ℚ δ).natDegree = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> omega
  obtain ⟨d, hd⟩ := minpoly.natDegree_eq_one_iff.mp h1
  refine ⟨d, (algebraMap ℚ L).injective ?_⟩
  rw [hδ, map_pow, hd]

theorem discr_square {a b : ℚ} (h : Admissible (cubic a b)) :
    ∃ d : ℚ, (cubicData a b).discr = d ^ 2 :=
  h.1.elim discr_square_of_cyclic discr_square_of_splits

/-- The nonvanishing `1-3a = N ≠ 0` for every admissible cubic. -/
theorem norm_ne_zero {a b : ℚ} (h : Admissible (cubic a b)) : 1 - 3 * a ≠ 0 := by
  intro hN
  obtain ⟨d, hd⟩ := discr_square h
  have ha : a = 1 / 3 := by linarith
  have hdisc : (cubicData a b).discr = -27 * (b + 1 / 27) ^ 2 := by
    simp only [_root_.Cubic.discr, cubicData, ha]
    ring
  have hb : b = -1 / 27 := by nlinarith [sq_nonneg d, sq_nonneg (b + 1 / 27)]
  apply h.2
  refine ⟨1 / 3, ?_⟩
  have key : ∀ r : ℚ, (X - C r) ^ 3 = X ^ 3 - C (3 * r) * X ^ 2 + C (3 * r ^ 2) * X - C (r ^ 3) := by
    intro r
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [key, cubic, ha, hb]
  norm_num
  ring

/-- The inverse quadratic's discriminant in terms of the cubic's. -/
private theorem inverse_discriminant (a b : ℚ) (hN : 1 - 3 * a ≠ 0) :
    (3 - (1 + 27 * b) / (1 - 3 * a)) ^ 2 - 4 * (1 - 3 * a) =
      -27 * (cubicData a b).discr / (1 - 3 * a) ^ 2 := by
  simp only [_root_.Cubic.discr, cubicData]
  field_simp
  ring

private theorem conjugation_sqrtNegThree : conjugation sqrtNegThree = -sqrtNegThree := by
  simp only [sqrtNegThree, map_add, map_mul, map_one, map_ofNat, conjugation_zeta]
  ring

/-- The converse clause: every admissible cubic is the polynomial of a rational quotient point. -/
theorem exists_point {a b : ℚ} (h : Admissible (cubic a b)) :
    ∃ p : Points, characteristicPolynomial p = cubic a b := by
  have hN := norm_ne_zero h
  obtain ⟨d, hd⟩ := discr_square h
  set N := 1 - 3 * a with hNdef
  set T := 3 - (1 + 27 * b) / N with hTdef
  set w : E := algebraMap ℚ E (3 * d / N) * sqrtNegThree
  set x : E := (algebraMap ℚ E T + w) / 2
  have hw : w ^ 2 = algebraMap ℚ E (T ^ 2 - 4 * N) := by
    rw [hTdef, hNdef, inverse_discriminant a b hN, hd]
    simp only [w, mul_pow, sqrtNegThree_sq, ← map_pow]
    rw [show (-3 : E) = algebraMap ℚ E (-3) by simp, ← map_mul]
    congr 1
    have hN' : 1 - 3 * a ≠ 0 := hN
    rw [hNdef]
    field_simp
    ring
  have hconj : conjugation x = (algebraMap ℚ E T - w) / 2 := by
    simp only [x, w, map_div₀, map_add, map_mul, AlgEquiv.commutes, map_ofNat,
      conjugation_sqrtNegThree]
    ring
  have htr : Algebra.trace ℚ E x = T := by
    apply (algebraMap ℚ E).injective
    rw [trace_eq_add_conjugation, hconj]
    ring
  have hnm : Algebra.norm ℚ x = N := by
    apply (algebraMap ℚ E).injective
    rw [norm_eq_mul_conjugation, hconj]
    simp only [map_sub, map_mul, map_pow, map_ofNat] at hw
    linear_combination (-1 / 4 : E) * hw
  have hx : x ≠ 0 := by
    rintro hx
    rw [hx, Algebra.norm_zero] at hnm
    exact hN hnm.symm
  refine ⟨parameterEquiv.symm (Units.mk0 x hx), ?_⟩
  rw [characteristicPolynomial_eq, Equiv.apply_symm_apply, Units.val_mk0, htr, hnm, hTdef, hNdef]
  have hN' : 1 - 3 * a ≠ 0 := hN
  congr 1
  · ring
  · field_simp
    ring

theorem finite_fibre {a b : ℚ} :
    {p : Points | characteristicPolynomial p = cubic a b}.Finite :=
  QuotientPolynomialFibres.finite_fibre _

theorem separable_fibre_card {a b : ℚ} (h : Admissible (cubic a b)) (hs : (cubic a b).Separable) :
    Nat.card {p : Points // characteristicPolynomial p = cubic a b} = 2 := by
  obtain ⟨p, hp⟩ := exists_point h
  rw [← hp] at hs ⊢
  exact QuotientPolynomialMultiplicity.separable_fibre_card p hs

theorem repeated_fibre_card {a b : ℚ} (h : Admissible (cubic a b)) (hs : ¬ (cubic a b).Separable) :
    Nat.card {p : Points // characteristicPolynomial p = cubic a b} = 1 := by
  obtain ⟨p, hp⟩ := exists_point h
  rw [← hp] at hs ⊢
  exact QuotientPolynomialMultiplicity.repeated_fibre_card p hs

end Cubic.QuadraticCorrespondence.QuotientPolynomialConverse
