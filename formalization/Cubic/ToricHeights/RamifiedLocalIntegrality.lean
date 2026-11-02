import Cubic.ToricHeights.RamifiedLocalModel
import Cubic.QuadraticCorrespondence.CyclotomicCoefficients
import Cubic.QuadraticCorrespondence.CyclotomicRamifiedResidueField

/-!
# Cyclotomic integrality and the exceptional cutoff

The local version of `eqn:integralityConditionsUsingCyclo` asks for
`N(u+vζ) ∈ 1+3ℤ₃` and `N(u+vζ)(3-Tr(u+vζ)) ∈ 1+27ℤ₃`.
These conditions are imposed on arbitrary `u,v : ℚ₃`; their integrality
must be derived before reduction modulo 27. This file connects those explicit
conditions with the congruence cutoff used in the Fourier model. The
comparison with the original local quotient is in `QuotientLocalIntegrality`
and `QuotientInvariantIntegrality`.
-/

noncomputable section

namespace Cubic.ToricHeights.RamifiedLocalIntegrality

open Cubic.QuadraticCorrespondence
open CyclotomicRamifiedField
open CyclotomicCoefficients

/-- The exact two congruence conditions in the paper, with p-adic integer witnesses. -/
def Conditions (u v : ℚ_[3]) : Prop :=
  (∃ n : ℤ_[3], normForm u v = 1 + 3 * (n : ℚ_[3])) ∧
  (∃ m : ℤ_[3], normForm u v * (3 - traceForm u v) = 1 + 27 * (m : ℚ_[3]))

theorem linear_mul_conjugation (u v : ℚ_[3]) :
    linear u v * conjugation (linear u v) = algebraMap ℚ_[3] Extension (normForm u v) := by
  rw [conjugation_linear]
  simp only [linear, normForm, map_sub, map_add, map_pow, map_mul]
  linear_combination -(algebraMap ℚ_[3] Extension v) ^ 2 * zeta_relation

/-- The polynomial norm expression has absolute value equal to the squared extension norm. -/
theorem norm_normForm (u v : ℚ_[3]) : ‖normForm u v‖ = ‖linear u v‖ ^ 2 := by
  rw [← CyclotomicRamifiedField.norm_algebraMap (normForm u v),
    ← linear_mul_conjugation, norm_mul, norm_conjugation, pow_two]

private theorem norm_one_add_three (n : ℤ_[3]) : ‖(1 + 3 * (n : ℚ_[3]) : ℚ_[3])‖ = 1 := by
  have hn : ‖(n : ℚ_[3])‖ ≤ 1 := n.property
  have hsmall : ‖(3 : ℚ_[3]) * n‖ < 1 := by
    rw [norm_mul]
    have hthree : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := Padic.norm_p
    rw [hthree]
    linarith
  have hadd (a b : ℚ_[3]) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := Padic.nonarchimedean _ _
  have hle : ‖(1 + 3 * (n : ℚ_[3]) : ℚ_[3])‖ ≤ 1 := by
    exact (hadd 1 (3 * n)).trans (by rw [norm_one]; exact max_le le_rfl hsmall.le)
  apply le_antisymm hle
  by_contra h
  have hlt := lt_of_not_ge h
  have hb := hadd (1 + 3 * (n : ℚ_[3])) (-(3 * (n : ℚ_[3])))
  simp only [add_neg_cancel_right, norm_one, norm_neg] at hb
  exact (not_lt_of_ge hb) (max_lt hlt hsmall)

/-- Integrality of the cyclotomic coordinates is a consequence of the conditions. -/
theorem coordinates_integral {u v : ℚ_[3]} (h : Conditions u v) : ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 := by
  obtain ⟨n, hn⟩ := h.1
  have hnorm : ‖linear u v‖ ^ 2 = 1 := by rw [← norm_normForm, hn, norm_one_add_three]
  have hunit : ‖linear u v‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 2 ≠ 0)).mp hnorm
  exact (norm_linear_le_one_iff u v).mp hunit.le

/-- Kernel-checked finite arithmetic for the integral coordinates modulo 27. -/
theorem residue_conditions : ∀ u v : ZMod (3 ^ 3),
    normForm u v * (3 - traceForm u v) = 1 →
      (ZMod.castHom (by decide : 3 ^ 1 ∣ 3 ^ 3) (ZMod (3 ^ 1)) u = 1 ∧
       ZMod.castHom (by decide : 3 ^ 1 ∣ 3 ^ 3) (ZMod (3 ^ 1)) v = 0) := by
  decide

private theorem three_dvd_of_reduce_zero {x : ℤ_[3]} (h : PadicInt.toZModPow 1 x = 0) :
    (3 : ℤ_[3]) ∣ x := by
  have hx : x ∈ RingHom.ker (PadicInt.toZModPow 1 : ℤ_[3] →+* ZMod (3 ^ 1)) := h
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hx
  simpa using hx

/-- Transfer the finite computation through mathlib's compatible p-adic reductions. -/
theorem integral_coordinates_congruent (u v m : ℤ_[3])
    (h : normForm u v * (3 - traceForm u v) = 1 + 27 * m) :
    (3 : ℤ_[3]) ∣ (u - 1) ∧ (3 : ℤ_[3]) ∣ v := by
  have hr : normForm (PadicInt.toZModPow 3 u) (PadicInt.toZModPow 3 v) *
      (3 - traceForm (PadicInt.toZModPow 3 u) (PadicInt.toZModPow 3 v)) = 1 := by
    have hr := congrArg (PadicInt.toZModPow 3) h
    have h27 : (27 : ZMod (3 ^ 3)) = 0 := by decide
    simpa [normForm, traceForm, map_ofNat, h27] using hr
  obtain ⟨hu, hv⟩ := residue_conditions _ _ hr
  have hcast (x : ℤ_[3]) :
      ZMod.castHom (by decide : 3 ^ 1 ∣ 3 ^ 3) (ZMod (3 ^ 1)) (PadicInt.toZModPow 3 x) =
        PadicInt.toZModPow 1 x :=
    DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow 1 3 (by decide)) x
  rw [hcast] at hu hv
  refine ⟨three_dvd_of_reduce_zero ?_, three_dvd_of_reduce_zero hv⟩
  rw [map_sub, map_one, hu, sub_self]

/-- The paper's two conditions are exactly the cyclotomic-coordinate congruences.
No integrality hypothesis on `u` or `v` is assumed. -/
theorem conditions_iff_coordinate_congruences (u v : ℚ_[3]) :
    Conditions u v ↔ ∃ c d : ℤ_[3], u = 1 + 3 * (c : ℚ_[3]) ∧ v = 3 * (d : ℚ_[3]) := by
  constructor
  · intro h
    obtain ⟨hu, hv⟩ := coordinates_integral h
    let a : ℤ_[3] := ⟨u, hu⟩
    let b : ℤ_[3] := ⟨v, hv⟩
    obtain ⟨m, hm⟩ := h.2
    have hab : normForm a b * (3 - traceForm a b) = 1 + 27 * m := by
      apply Subtype.ext
      simpa [normForm, traceForm, a, b] using hm
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := integral_coordinates_congruent a b m hab
    refine ⟨c, d, ?_, ?_⟩
    · have h := congrArg (fun x : ℤ_[3] => (x : ℚ_[3])) hc
      change u - 1 = 3 * (c : ℚ_[3]) at h
      linear_combination h
    · exact congrArg (fun x : ℤ_[3] => (x : ℚ_[3])) hd
  · rintro ⟨c, d, rfl, rfl⟩
    constructor
    · refine ⟨traceForm c d + 3 * normForm c d, ?_⟩
      change normForm (1 + 3 * (c : ℚ_[3])) (3 * (d : ℚ_[3])) =
        1 + 3 * (traceForm (c : ℚ_[3]) d + 3 * normForm (c : ℚ_[3]) d)
      simp only [normForm, traceForm]
      ring
    · refine ⟨-c * (c - d) - normForm c d * traceForm c d, ?_⟩
      change normForm (1 + 3 * (c : ℚ_[3])) (3 * (d : ℚ_[3])) *
        (3 - traceForm (1 + 3 * (c : ℚ_[3])) (3 * (d : ℚ_[3]))) =
        1 + 27 * (-(c : ℚ_[3]) * (c - d) - normForm (c : ℚ_[3]) d * traceForm (c : ℚ_[3]) d)
      simp only [normForm, traceForm]
      ring

/-- Express the coordinate congruences intrinsically in the local integer ring. -/
theorem conditions_iff_congruence_locus (u v : ℚ_[3]) :
    Conditions u v ↔ ∃ a : integers, linear u v = 1 + 3 * (a : Extension) := by
  rw [conditions_iff_coordinate_congruences]
  constructor
  · rintro ⟨c, d, rfl, rfl⟩
    refine ⟨⟨linear c d, (norm_linear_le_one_iff _ _).mpr ⟨c.property, d.property⟩⟩, ?_⟩
    simp only [linear, map_add, map_mul, map_one, map_ofNat]
    ring
  · rintro ⟨a, ha⟩
    obtain ⟨c, d, hcd⟩ := exists_linear (a : Extension)
    have hint : ‖linear c d‖ ≤ 1 := hcd ▸ a.property
    obtain ⟨hc, hd⟩ := (norm_linear_le_one_iff c d).mp hint
    rw [hcd] at ha
    have hzero : linear (u - (1 + 3 * c)) (v - 3 * d) = 0 := by
      simp only [linear, map_sub, map_add, map_mul, map_one, map_ofNat] at ha ⊢
      linear_combination ha
    obtain ⟨hu, hv⟩ := (linear_eq_zero_iff _ _).mp hzero
    exact ⟨⟨c, hc⟩, ⟨d, hd⟩, sub_eq_zero.mp hu, sub_eq_zero.mp hv⟩

/-- This supplies the exact arithmetic comparison with the Fourier model's cutoff. -/
theorem conditions_iff_mem_integralLocus (x : RamifiedLocalModel.Points) (u v : ℚ_[3])
    (hx : (x : Extension) = linear u v) :
    Conditions u v ↔ x ∈ RamifiedLocalModel.integralLocus := by
  rw [conditions_iff_congruence_locus, RamifiedLocalModel.mem_integralLocus_iff_exists, hx]

/-- Integrality of the two variable coefficients of the paper's monic trace-one cubic. -/
def CoefficientsIntegral (u v : ℚ_[3]) : Prop :=
  ‖linearCoefficient u v‖ ≤ 1 ∧ ‖constantCoefficient u v‖ ≤ 1

/-- The congruences are equivalent to integrality of the displayed cubic coefficients. -/
theorem coefficientsIntegral_iff_conditions (u v : ℚ_[3]) :
    CoefficientsIntegral u v ↔ Conditions u v := by
  constructor
  · rintro ⟨ha, hb⟩
    let a : ℤ_[3] := ⟨linearCoefficient u v, ha⟩
    let b : ℤ_[3] := ⟨constantCoefficient u v, hb⟩
    constructor
    · refine ⟨-a, ?_⟩
      change normForm u v = 1 + 3 * (-((1 - normForm u v) / 3))
      field_simp
      ring
    · refine ⟨b, ?_⟩
      change normForm u v * (3 - traceForm u v) =
        1 + 27 * ((normForm u v * (3 - traceForm u v) - 1) / 27)
      field_simp
      ring
  · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    have ha : linearCoefficient u v = -(n : ℚ_[3]) := by
      rw [linearCoefficient, hn]
      ring
    have hb : constantCoefficient u v = (m : ℚ_[3]) := by
      rw [constantCoefficient, hm]
      ring
    exact ⟨by rw [ha, norm_neg]; exact n.property, by rw [hb]; exact m.property⟩

/-- The arithmetic support comparison, directly in terms of the cubic coefficients. -/
theorem coefficientsIntegral_iff_mem_integralLocus
    (x : RamifiedLocalModel.Points) (u v : ℚ_[3]) (hx : (x : Extension) = linear u v) :
    CoefficientsIntegral u v ↔ x ∈ RamifiedLocalModel.integralLocus := by
  rw [coefficientsIntegral_iff_conditions, conditions_iff_mem_integralLocus x u v hx]

/-- Define the cutoff by integrality of the paper's coefficient expressions.
For points of the original quotient, `QuotientLocalIntegrality.ramified_mem_iff`
identifies these expressions with the descended cubic coefficients. -/
def coefficientLocus : Set RamifiedLocalModel.Points :=
  {x | ∃ u v : ℚ_[3], (x : Extension) = linear u v ∧ CoefficientsIntegral u v}

/-- The locus defined by coefficient integrality is exactly the congruence subgroup. -/
theorem coefficientLocus_eq_integralLocus : coefficientLocus = RamifiedLocalModel.integralLocus := by
  ext x
  constructor
  · rintro ⟨u, v, hx, hc⟩
    exact (coefficientsIntegral_iff_mem_integralLocus x u v hx).mp hc
  · intro hx
    obtain ⟨u, v, huv⟩ := exists_linear (x : Extension)
    exact ⟨u, v, huv, (coefficientsIntegral_iff_mem_integralLocus x u v huv).mpr hx⟩

/-- The arithmetic cutoff is the second principal congruence level, using the
maximal ideal of the local integer ring. -/
theorem mem_integralLocus_iff_maximalIdeal_sq (x : RamifiedLocalModel.Points) :
    x ∈ RamifiedLocalModel.integralLocus ↔
      ∃ a : integers, a ∈ IsLocalRing.maximalIdeal integers ^ 2 ∧
        (x : Extension) = 1 + (a : Extension) := by
  rw [RamifiedLocalModel.mem_integralLocus_iff_exists]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨3 * a, ?_, ?_⟩
    · rw [maximalIdeal_sq, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    · simpa using ha
  · rintro ⟨a, ha, hx⟩
    rw [maximalIdeal_sq, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨b, by simpa using hx⟩

end Cubic.ToricHeights.RamifiedLocalIntegrality
