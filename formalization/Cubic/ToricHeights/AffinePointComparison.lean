import Cubic.ToricHeights.AffinePointParameter

/-! Every integral point of the original affine invariant ring is a unique torus
point. The nonvanishing `1−3a` follows from integral `a`; the inverse map uses
the oriented invariant `δ`, so its two possible signs are retained. -/

noncomputable section

namespace Cubic.ToricHeights.AffinePointComparison

open Cubic.QuadraticCorrespondence CyclotomicField CyclotomicTorusGalois
open DescendedCoefficients RationalCoefficientFormula DescendedCyclicInvariant
open AffineInvariantRing

abbrev ChartPoints := AffineChartInvariants.RationalPoint
abbrev TorusPoints := quotientFixedRing →ₐ[ℚ] ℚ

def restrictPoint (Q : TorusPoints) : ChartPoints :=
  Q.toRingHom.comp invariantRestriction.toRingHom

def a (P : ChartPoints) : ℚ := P ⟨AffineChartInvariants.e2, AffineChartInvariants.e2_mem⟩
def b (P : ChartPoints) : ℚ := -P ⟨AffineChartInvariants.e3, AffineChartInvariants.e3_mem⟩
def d (P : ChartPoints) : ℚ := P ⟨AffineChartInvariants.delta, AffineChartInvariants.delta_mem⟩

theorem restrict_a (Q : TorusPoints) : a (restrictPoint Q) = Q linearCoefficient := by
  simp [a, restrictPoint, invariantRestriction_linear, AffineChartInvariants.e2]

theorem restrict_b (Q : TorusPoints) : b (restrictPoint Q) = Q constantCoefficient := by
  have h : (⟨-AffineChartInvariants.e3, invariants.neg_mem AffineChartInvariants.e3_mem⟩ :
      invariants) = ⟨constantPolynomial, constantPolynomial_fixed⟩ := rfl
  change -(Q (invariantRestriction ⟨AffineChartInvariants.e3,
    AffineChartInvariants.e3_mem⟩)) = _
  rw [← map_neg Q, ← map_neg invariantRestriction]
  change Q (invariantRestriction ⟨-AffineChartInvariants.e3, _⟩) = _
  rw [h, invariantRestriction_constant]

theorem invariantRestriction_delta :
    invariantRestriction ⟨AffineChartInvariants.delta, AffineChartInvariants.delta_mem⟩ =
      DescendedCyclicInvariant.delta := by
  apply Subtype.ext
  change restrict AffineChartInvariants.delta = coverDelta
  simp [AffineChartInvariants.delta, coverDelta]

theorem restrict_d (Q : TorusPoints) : d (restrictPoint Q) = Q DescendedCyclicInvariant.delta := by
  change Q (invariantRestriction ⟨AffineChartInvariants.delta,
    AffineChartInvariants.delta_mem⟩) = _
  rw [invariantRestriction_delta]

theorem chart_ext {P Q : ChartPoints} (ha : a P = a Q) (hb : b P = b Q)
    (hd : d P = d Q) : P = Q := by
  have hg := Algebra.adjoin_adjoin_coe_preimage (R := ℤ)
    (s := ({AffineChartInvariants.e2, AffineChartInvariants.e3,
      AffineChartInvariants.delta} : Set ChartRing))
  rw [← AffineC3Invariants.«eqn:affineC3invariants»] at hg
  apply RingHom.toIntAlgHom_injective
  apply AlgHom.ext_of_adjoin_eq_top hg
  intro f hf
  change f.val ∈ ({AffineChartInvariants.e2, AffineChartInvariants.e3,
    AffineChartInvariants.delta} : Set ChartRing) at hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with he | he | he
  · have he' : f = ⟨AffineChartInvariants.e2, AffineChartInvariants.e2_mem⟩ := Subtype.ext he
    simpa only [he', a, RingHom.toIntAlgHom_apply] using ha
  · have he' : f = ⟨AffineChartInvariants.e3, AffineChartInvariants.e3_mem⟩ := Subtype.ext he
    have h := neg_injective hb
    simpa only [he', b, RingHom.toIntAlgHom_apply] using h
  · have he' : f = ⟨AffineChartInvariants.delta, AffineChartInvariants.delta_mem⟩ := Subtype.ext he
    simpa only [he', d, RingHom.toIntAlgHom_apply] using hd

theorem relation (P : ChartPoints) :
    d P ^ 2 - (a P + 3 * b P) * d P +
      (a P ^ 3 - b P + 9 * b P ^ 2 + 6 * a P * b P) = 0 := by
  have hq : (⟨AffineChartInvariants.delta, AffineChartInvariants.delta_mem⟩ : invariants) ^ 2 -
      (⟨AffineChartInvariants.e2, AffineChartInvariants.e2_mem⟩ -
        3 * ⟨AffineChartInvariants.e3, AffineChartInvariants.e3_mem⟩) *
          ⟨AffineChartInvariants.delta, AffineChartInvariants.delta_mem⟩ +
      ((⟨AffineChartInvariants.e2, AffineChartInvariants.e2_mem⟩ : invariants) ^ 3 +
        ⟨AffineChartInvariants.e3, AffineChartInvariants.e3_mem⟩ -
        6 * ⟨AffineChartInvariants.e2, AffineChartInvariants.e2_mem⟩ *
          ⟨AffineChartInvariants.e3, AffineChartInvariants.e3_mem⟩ +
        9 * (⟨AffineChartInvariants.e3, AffineChartInvariants.e3_mem⟩ : invariants) ^ 2) = 0 :=
    Subtype.ext AffineIntegrality.delta_quadratic
  have h := congrArg P hq
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero] at h
  unfold a b d
  linear_combination h

theorem norm_ne_zero (P : ChartPoints) (hP : AffineChartInvariants.IsD0Integral P) :
    1 - 3 * a P ≠ 0 := by
  obtain ⟨m, hm⟩ := hP ⟨AffineChartInvariants.e2, AffineChartInvariants.e2_mem⟩
  change a P = (m : ℚ) at hm
  rw [hm]
  have hi : (1 - 3 * m : ℤ) ≠ 0 := by omega
  exact_mod_cast hi

theorem restrict_injective : Function.Injective restrictPoint := by
  intro P Q he
  have ha := congrArg a he
  have hb := congrArg b he
  have hd := congrArg d he
  simp only [restrict_a, restrict_b, restrict_d] at ha hb hd
  apply parameterEquiv.injective
  apply Units.ext
  have hp := AffinePointParameter.parameter_equation P
  have hq := AffinePointParameter.parameter_equation Q
  rw [← ha, ← hb, ← hd] at hq
  have hn : (2 * (1 - 3 * algebraMap ℚ E (P linearCoefficient))) ≠ 0 := by
    have h := inverse_denominator_ne_zero P
    have he : 1 - 3 * algebraMap ℚ E (P linearCoefficient) ≠ 0 := by
      simpa only [map_sub, map_one, map_mul, map_ofNat] using
        ((map_ne_zero (algebraMap ℚ E)).mpr h)
    exact mul_ne_zero (by norm_num) he
  exact mul_left_cancel₀ hn (hp.trans hq.symm)

theorem exists_extension (P : ChartPoints) (hn : 1 - 3 * a P ≠ 0) :
    ∃ Q : TorusPoints, restrictPoint Q = P := by
  let N := 1 - 3 * a P
  let J := 2 - 9 * a P - 27 * b P
  let D := 2 * d P - a P - 3 * b P
  let T := J / N
  let w : E := algebraMap ℚ E (3 * D / N) * sqrtNegThree
  let x : E := (algebraMap ℚ E T + w) / 2
  have hN : N ≠ 0 := hn
  have hNE : algebraMap ℚ E N ≠ 0 := (map_ne_zero _).mpr hN
  have hrel : J ^ 2 + 27 * D ^ 2 = 4 * N ^ 3 := by
    dsimp [J, D, N]
    linear_combination 108 * relation P
  have hT : T ^ 2 - 4 * N = -27 * D ^ 2 / N ^ 2 := by
    dsimp [T]
    field_simp
    linear_combination hrel
  have hw : w ^ 2 = algebraMap ℚ E (T ^ 2 - 4 * N) := by
    rw [hT]
    simp only [w, mul_pow, sqrtNegThree_sq, map_div₀, map_mul, map_pow,
      map_neg, map_ofNat]
    ring
  have hc : conjugation x = (algebraMap ℚ E T - w) / 2 := by
    simp only [x, w, map_div₀, map_add, map_mul, AlgEquiv.commutes,
      map_ofNat, AffinePointParameter.conjugation_sqrt]
    ring
  have htrace : Algebra.trace ℚ E x = T := by
    apply (algebraMap ℚ E).injective
    rw [trace_eq_add_conjugation, hc]
    ring
  have hnorm : Algebra.norm ℚ x = N := by
    apply (algebraMap ℚ E).injective
    rw [norm_eq_mul_conjugation, hc]
    simp only [map_sub, map_mul, map_pow, map_ofNat] at hw
    dsimp only [x]
    linear_combination -hw / 4
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, Algebra.norm_zero] at hnorm
    exact hN hnorm.symm
  let Q : TorusPoints := parameterEquiv.symm (Units.mk0 x hx)
  have hparam : (parameterEquiv Q : E) = x := by simp [Q]
  have ha : Q linearCoefficient = a P := by
    rw [linearCoefficient_eq, hparam, hnorm]
    dsimp [N]
    ring
  have hb : Q constantCoefficient = b P := by
    rw [constantCoefficient_eq, hparam, hnorm, htrace]
    dsimp [T, J, N]
    field_simp
    ring
  have heq : 2 * algebraMap ℚ E N * x =
      algebraMap ℚ E J + 3 * sqrtNegThree * algebraMap ℚ E D := by
    dsimp [x, w, T]
    simp only [map_div₀, map_mul, map_ofNat]
    field_simp
  have hd : Q DescendedCyclicInvariant.delta = d P := by
    apply (algebraMap ℚ E).injective
    have hq := AffinePointParameter.parameter_equation Q
    rw [ha, hb, hparam] at hq
    dsimp only [N, J, D] at heq
    simp only [map_sub, map_one, map_mul, map_ofNat] at heq
    have hs : 6 * sqrtNegThree ≠ 0 := mul_ne_zero (by norm_num)
      AffinePointParameter.sqrt_ne_zero
    apply mul_left_cancel₀ hs
    linear_combination heq - hq
  refine ⟨Q, chart_ext ?_ ?_ ?_⟩
  · simpa only [restrict_a] using ha
  · simpa only [restrict_b] using hb
  · simpa only [restrict_d] using hd

theorem exists_unique_integral_extension (P : ChartPoints)
    (hP : AffineChartInvariants.IsD0Integral P) :
    ∃! Q : TorusPoints, restrictPoint Q = P := by
  obtain ⟨Q, hQ⟩ := exists_extension P (norm_ne_zero P hP)
  exact ⟨Q, hQ, fun Q' hQ' => restrict_injective (hQ'.trans hQ.symm)⟩

end Cubic.ToricHeights.AffinePointComparison
