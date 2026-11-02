import Cubic.QuadraticCorrespondence.CyclotomicRamifiedIntegers
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The residue field and the square of the maximal ideal at three

For the norm-integral ring in the quadratic local field,
prove that the maximal ideal is `(1-ζ)`, its square is `(3)`, and the residue
field is `𝔽₃`. This distinguishes the residue field from the nonreduced quotient
modulo three, whose six units give the exceptional Fourier mass.

These arithmetic facts are used in the proofs of `prop:localIntegrality` and
`eqn:heightforrationaladeles`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicRamifiedReduction

/-- Reduction modulo the ramified parameter, sending `ζ` to one. -/
def residue : IntegralModel →+* ZMod 3 :=
  (TrivSqZeroExt.fstHom (ZMod 3) (ZMod 3) (ZMod 3)).toRingHom.comp reduction

@[simp]
theorem residue_linear (a b : ℤ_[3]) :
    residue (linear a b) = PadicInt.toZMod (a + b) := by
  change (reduction (linear a b)).fst = _
  rw [reduction_linear_fst, map_add]

@[simp]
theorem residue_zeta : residue zeta = 1 := by
  change (reduction zeta).fst = _
  simp [residueZeta]

theorem residue_surjective : Function.Surjective residue :=
  ZMod.ringHom_surjective residue

/-- The relation has a unit factor: the square of the parameter is `-3ζ`. -/
theorem parameter_sq : (1 - zeta) ^ 2 = -3 * zeta := by
  linear_combination zeta_relation

theorem three_eq_parameter_mul : (3 : IntegralModel) = (1 - zeta) * (2 + zeta) := by
  linear_combination zeta_relation

/-- The reduced quotient has kernel `(1-ζ)`, whereas reduction modulo three
has kernel `(3)`. -/
theorem ker_residue : RingHom.ker residue = Ideal.span {1 - zeta} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · obtain ⟨a, b, rfl⟩ := exists_linear x
    rw [residue_linear]
    intro h
    have hab : (3 : ℤ_[3]) ∣ a + b := by
      rwa [← RingHom.mem_ker, PadicInt.ker_toZMod,
        PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := hab
    refine ⟨(2 + zeta) * algebraMap ℤ_[3] IntegralModel c -
      algebraMap ℤ_[3] IntegralModel b, ?_⟩
    calc
      linear a b = algebraMap ℤ_[3] IntegralModel (a + b) -
          algebraMap ℤ_[3] IntegralModel b * (1 - zeta) := by
            simp only [linear, map_add]
            ring
      _ = _ := by rw [hc, map_mul, map_ofNat, three_eq_parameter_mul]; ring
  · rintro ⟨y, rfl⟩
    simp

theorem parameter_ideal_sq : Ideal.span {1 - zeta} ^ 2 = Ideal.span {(3 : IntegralModel)} := by
  rw [Ideal.span_singleton_pow, parameter_sq]
  have hu : IsUnit (-zeta) := zetaUnit.isUnit.neg
  simpa only [neg_mul, mul_neg] using Ideal.span_singleton_mul_right_unit hu (3 : IntegralModel)

end Cubic.QuadraticCorrespondence.CyclotomicRamifiedReduction

namespace Cubic.QuadraticCorrespondence.CyclotomicRamifiedField

/-- Units of the norm-integral ring are exactly the elements of norm one. -/
theorem isUnit_integer_iff (x : integers) : IsUnit x ↔ ‖(x : Extension)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    apply le_antisymm u.val.property
    have hi : ‖(u.inv : Extension)‖ ≤ 1 := u.inv.property
    have hm : ‖(u.val : Extension)‖ * ‖(u.inv : Extension)‖ = 1 := by
      rw [← norm_mul]
      have h := congrArg Subtype.val u.val_inv
      exact (congrArg norm h).trans norm_one
    nlinarith [norm_nonneg (((u : integers) : Extension))]
  · intro hx
    have hx0 : (x : Extension) ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; norm_num)
    let y : integers := ⟨(x : Extension)⁻¹, by change ‖(x : Extension)⁻¹‖ ≤ 1; simp [hx]⟩
    exact ⟨⟨x, y, Subtype.ext (mul_inv_cancel₀ hx0),
      Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem not_isUnit_integer_iff (x : integers) : ¬ IsUnit x ↔ ‖(x : Extension)‖ < 1 := by
  rw [isUnit_integer_iff]
  exact ne_iff_lt_iff_le.mpr x.property

instance : IsLocalRing integers := IsLocalRing.of_nonunits_add fun x y hx hy => by
  change ¬ IsUnit x at hx
  change ¬ IsUnit y at hy
  change ¬ IsUnit (x + y)
  rw [not_isUnit_integer_iff] at hx hy ⊢
  exact (isNonarchimedean_spectralNorm (x : Extension) (y : Extension)).trans_lt (max_lt hx hy)

/-- The paper's parameter `1-ζ`, in the integral subring. -/
def uniformizer : integers := integralEquiv (1 - CyclotomicRamifiedReduction.zeta)

@[simp]
theorem coe_uniformizer : (uniformizer : Extension) = 1 - zeta := by
  change integralEmbedding (1 - CyclotomicRamifiedReduction.zeta) = _
  simp

/-- Residue reduction transported through the integral-basis equivalence. -/
def residue : integers →+* ZMod 3 :=
  CyclotomicRamifiedReduction.residue.comp integralEquiv.symm.toRingHom

theorem residue_surjective : Function.Surjective residue :=
  CyclotomicRamifiedReduction.residue_surjective.comp integralEquiv.symm.surjective

theorem ker_residue : RingHom.ker residue = Ideal.span {uniformizer} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change CyclotomicRamifiedReduction.residue (integralEquiv.symm x) = 0 ↔ _
  rw [← RingHom.mem_ker, CyclotomicRamifiedReduction.ker_residue, Ideal.mem_span_singleton]
  rw [← map_dvd_iff integralEquiv, RingEquiv.apply_symm_apply]
  rfl

/-- The maximal ideal is generated by `1-ζ`. -/
theorem maximalIdeal_eq_parameter : IsLocalRing.maximalIdeal integers = Ideal.span {uniformizer} := by
  have h := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective residue residue_surjective)
  exact h.symm.trans ker_residue

theorem mem_maximalIdeal_iff_norm (x : integers) :
    x ∈ IsLocalRing.maximalIdeal integers ↔ ‖(x : Extension)‖ < 1 := by
  exact not_isUnit_integer_iff x

/-- The paper's equality `3𝓞 = 𝔪²` in the norm-integral ring. -/
theorem maximalIdeal_sq : IsLocalRing.maximalIdeal integers ^ 2 = Ideal.span {(3 : integers)} := by
  rw [maximalIdeal_eq_parameter, Ideal.span_singleton_pow]
  have hs : uniformizer ^ 2 = 3 * integralEquiv (-CyclotomicRamifiedReduction.zeta) := by
    rw [uniformizer, ← map_pow, CyclotomicRamifiedReduction.parameter_sq]
    simp only [map_mul, map_neg, map_ofNat]
    ring
  rw [hs]
  exact Ideal.span_singleton_mul_right_unit
    ((CyclotomicRamifiedReduction.zetaUnit.isUnit.neg).map integralEquiv.toRingHom) _

/-- The local residue field, as mathlib's quotient by the maximal ideal. -/
def residueFieldEquiv : IsLocalRing.ResidueField integers ≃+* ZMod 3 := by
  letI : IsLocalHom residue := .of_surjective residue residue_surjective
  let f := IsLocalRing.ResidueField.lift residue
  refine RingEquiv.ofBijective f ⟨f.injective, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  exact ⟨IsLocalRing.residue integers x, rfl⟩

theorem card_residueField : Nat.card (IsLocalRing.ResidueField integers) = 3 := by
  rw [Nat.card_congr residueFieldEquiv.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- Reduction on integral units modulo the maximal ideal, not modulo its square. -/
def residueUnits : integersˣ →* (ZMod 3)ˣ := Units.map residue

theorem residueUnits_surjective : Function.Surjective residueUnits := by
  exact IsLocalRing.surjective_units_map_of_local_ringHom residue residue_surjective
    (.of_surjective residue residue_surjective)

/-- The first principal congruence subgroup `1+𝔪`, inside integral units. -/
def firstCongruenceSubgroup : Subgroup integersˣ := residueUnits.ker

theorem mem_firstCongruenceSubgroup (u : integersˣ) :
    u ∈ firstCongruenceSubgroup ↔ (u : integers) - 1 ∈ IsLocalRing.maximalIdeal integers := by
  change residueUnits u = 1 ↔ _
  rw [← Units.val_inj]
  change residue (u : integers) = 1 ↔ _
  rw [← sub_eq_zero, ← map_one residue, ← map_sub, ← RingHom.mem_ker,
    ker_residue, maximalIdeal_eq_parameter]

/-- The first level has index two; the paper's level `1+3𝓞 = 1+𝔪²` has index six. -/
theorem firstCongruenceSubgroup_index : firstCongruenceSubgroup.index = 2 := by
  calc
    _ = Nat.card (ZMod 3)ˣ := Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective residueUnits residueUnits_surjective).toEquiv
    _ = 2 := by rw [Nat.card_eq_fintype_card]; decide

end Cubic.QuadraticCorrespondence.CyclotomicRamifiedField
