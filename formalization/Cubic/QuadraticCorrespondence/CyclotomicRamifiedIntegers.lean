import Cubic.QuadraticCorrespondence.CyclotomicRamifiedField
import Cubic.QuadraticCorrespondence.CyclotomicRamifiedReduction

/-!
# The integral basis at the ramified place

Identify the integral polynomial order with the closed unit ball in the
local field. Although `1,ζ` is not an orthonormal basis at three, integrality
is still equivalent to integrality of both coefficients. Conjugation bounds
the second coefficient by `√3`; the discrete base-field norm then bounds it
by one. This connects the finite quotient calculation with the local
integral units.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicRamifiedField

open Polynomial

def zeta : Extension := AdjoinRoot.root (cyclotomic 3 ℚ_[3])

theorem zeta_relation : zeta ^ 2 + zeta + 1 = 0 := by
  have h : (AdjoinRoot.root (cyclotomic 3 ℚ_[3])) ^ 2 +
      AdjoinRoot.root (cyclotomic 3 ℚ_[3]) + 1 = 0 := by
    simpa [cyclotomic_three] using AdjoinRoot.eval₂_root (cyclotomic 3 ℚ_[3])
  exact congrArg quotientEquiv.symm h |>.trans (by simp)

private def conjugationHom : Extension →ₐ[ℚ_[3]] Extension :=
  AdjoinRoot.liftAlgHom (cyclotomic 3 ℚ_[3]) (Algebra.ofId ℚ_[3] Extension)
    (-1 - zeta) (by
      simpa [cyclotomic_three] using CyclotomicLocalAlgebra.other_root zeta zeta_relation)

@[simp]
private theorem conjugationHom_zeta : conjugationHom zeta = -1 - zeta :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem conjugationHom_comp : conjugationHom.comp conjugationHom = .id ℚ_[3] Extension := by
  apply AdjoinRoot.algHom_ext
  change conjugationHom (conjugationHom zeta) = zeta
  simp only [conjugationHom_zeta, map_sub, map_neg, map_one]
  ring

def conjugation : Extension ≃ₐ[ℚ_[3]] Extension :=
  AlgEquiv.ofAlgHom conjugationHom conjugationHom conjugationHom_comp conjugationHom_comp

@[simp]
theorem conjugation_zeta : conjugation zeta = -1 - zeta := conjugationHom_zeta

@[simp]
theorem norm_conjugation (x : Extension) : ‖conjugation x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv conjugation x).symm

@[simp]
theorem norm_zeta : ‖zeta‖ = 1 := by
  have h : zeta ^ 3 = 1 := by linear_combination (zeta - 1) * zeta_relation
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 3 ≠ 0)).mp
  simpa only [norm_pow, norm_one] using congrArg norm h

theorem norm_three : ‖(3 : Extension)‖ = 1 / 3 := by
  have hq : ‖(3 : ℚ_[3])‖ = 1 / 3 := by simpa using (Padic.norm_p (p := 3))
  simpa only [map_ofNat] using (norm_algebraMap (3 : ℚ_[3])).trans hq

/-- The two conjugate roots have difference of norm `3^(-1/2)`. -/
theorem norm_root_difference_sq : ‖2 * zeta + 1‖ ^ 2 = 1 / 3 := by
  have hs : (2 * zeta + 1) ^ 2 = -3 := by linear_combination 4 * zeta_relation
  rw [← norm_pow, hs, norm_neg, norm_three]

theorem root_difference_ne_zero : 2 * zeta + 1 ≠ 0 := by
  intro h
  have := norm_root_difference_sq
  norm_num [h] at this

def linear (a b : ℚ_[3]) : Extension :=
  algebraMap ℚ_[3] Extension a + algebraMap ℚ_[3] Extension b * zeta

theorem conjugation_linear (a b : ℚ_[3]) : conjugation (linear a b) =
    algebraMap ℚ_[3] Extension a + algebraMap ℚ_[3] Extension b * (-1 - zeta) := by
  simp [linear]

theorem linear_sub_conjugation (a b : ℚ_[3]) :
    linear a b - conjugation (linear a b) = algebraMap ℚ_[3] Extension b * (2 * zeta + 1) := by
  rw [conjugation_linear]
  simp only [linear]
  ring

theorem linear_eq_zero_iff (a b : ℚ_[3]) : linear a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hb : algebraMap ℚ_[3] Extension b * (2 * zeta + 1) = 0 := by
      rw [← linear_sub_conjugation, h, map_zero, sub_self]
    have hb0 : b = 0 := (algebraMap ℚ_[3] Extension).injective
      (by simpa using (mul_eq_zero.mp hb).resolve_right root_difference_ne_zero)
    refine ⟨?_, hb0⟩
    apply (algebraMap ℚ_[3] Extension).injective
    simpa [linear, hb0] using h
  · rintro ⟨rfl, rfl⟩
    simp [linear]

theorem exists_linear (x : Extension) : ∃ a b : ℚ_[3], x = linear a b := by
  let pb : PowerBasis ℚ_[3] Extension := AdjoinRoot.powerBasis' (cyclotomic.monic 3 ℚ_[3])
  obtain ⟨f, hdeg, hf⟩ := pb.exists_eq_aeval x
  have hd : f.natDegree < 2 := by
    simpa only [pb, AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic] using hdeg
  have he := f.eq_X_add_C_of_degree_le_one
    (degree_le_of_natDegree_le (Nat.le_of_lt_succ hd))
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hf, he]
  simp [linear, pb, zeta, add_comm]

private theorem norm_add_le_max (x y : Extension) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  isNonarchimedean_spectralNorm x y

/-- The ramified cyclotomic power basis is an integral basis. -/
theorem norm_linear_le_one_iff (a b : ℚ_[3]) :
    ‖linear a b‖ ≤ 1 ↔ ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 := by
  constructor
  · intro hx
    have hprod : ‖b‖ * ‖2 * zeta + 1‖ ≤ 1 := by
      calc
        _ = ‖linear a b - conjugation (linear a b)‖ := by
          rw [linear_sub_conjugation, norm_mul, norm_algebraMap]
        _ ≤ max ‖linear a b‖ ‖conjugation (linear a b)‖ := by
          simpa only [sub_eq_add_neg, norm_neg] using
            norm_add_le_max (linear a b) (-conjugation (linear a b))
        _ ≤ 1 := by simpa using hx
    have hsquare := pow_le_pow_left₀ (mul_nonneg (norm_nonneg b) (norm_nonneg _)) hprod 2
    rw [mul_pow, norm_root_difference_sq] at hsquare
    have hblt : ‖b‖ < 3 := by nlinarith [norm_nonneg b]
    have hb : ‖b‖ ≤ 1 := by
      simpa using (Padic.norm_le_pow_iff_norm_lt_pow_add_one b 0).mpr (by simpa using hblt)
    refine ⟨?_, hb⟩
    have ha : algebraMap ℚ_[3] Extension a =
        linear a b - algebraMap ℚ_[3] Extension b * zeta := by simp [linear]
    calc
      ‖a‖ = ‖algebraMap ℚ_[3] Extension a‖ := (norm_algebraMap a).symm
      _ = ‖linear a b - algebraMap ℚ_[3] Extension b * zeta‖ := congrArg norm ha
      _ ≤ max ‖linear a b‖ ‖b‖ := by
        simpa only [sub_eq_add_neg, norm_neg, norm_mul, norm_algebraMap, norm_zeta, mul_one] using
          norm_add_le_max (linear a b) (-(algebraMap ℚ_[3] Extension b * zeta))
      _ ≤ 1 := max_le hx hb
  · rintro ⟨ha, hb⟩
    have h : ‖linear a b‖ ≤ max ‖a‖ ‖b‖ := by
      simpa only [linear, norm_mul, norm_algebraMap, norm_zeta, mul_one] using
        norm_add_le_max (algebraMap ℚ_[3] Extension a) (algebraMap ℚ_[3] Extension b * zeta)
    exact h.trans (max_le ha hb)

/-- The ring of norm-integral elements in the local field. -/
def integers : Subring Extension where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb := (norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' ha := by simpa only [Set.mem_setOf_eq, norm_neg] using ha
  mul_mem' ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb

/-- The integral order maps to the field by its specified generator. -/
def integralEmbedding : CyclotomicRamifiedReduction.IntegralModel →+* Extension :=
  AdjoinRoot.lift ((algebraMap ℚ_[3] Extension).comp PadicInt.Coe.ringHom)
    zeta (by simpa [cyclotomic_three] using zeta_relation)

@[simp]
theorem integralEmbedding_zeta : integralEmbedding CyclotomicRamifiedReduction.zeta = zeta :=
  AdjoinRoot.lift_root _

@[simp]
theorem integralEmbedding_scalar (a : ℤ_[3]) :
    integralEmbedding (algebraMap ℤ_[3] CyclotomicRamifiedReduction.IntegralModel a) =
      algebraMap ℚ_[3] Extension (a : ℚ_[3]) := AdjoinRoot.lift_of _

@[simp]
theorem integralEmbedding_linear (a b : ℤ_[3]) :
    integralEmbedding (CyclotomicRamifiedReduction.linear a b) = linear a b := by
  simp only [CyclotomicRamifiedReduction.linear, map_add, map_mul,
    integralEmbedding_scalar, integralEmbedding_zeta, linear]

theorem integralEmbedding_injective : Function.Injective integralEmbedding := by
  apply (injective_iff_map_eq_zero integralEmbedding).mpr
  intro x hx
  obtain ⟨a, b, rfl⟩ := CyclotomicRamifiedReduction.exists_linear x
  rw [integralEmbedding_linear, linear_eq_zero_iff] at hx
  have ha : a = 0 := Subtype.ext hx.1
  have hb : b = 0 := Subtype.ext hx.2
  simp [ha, hb, CyclotomicRamifiedReduction.linear]

theorem integralEmbedding_mem (x : CyclotomicRamifiedReduction.IntegralModel) :
    integralEmbedding x ∈ integers := by
  obtain ⟨a, b, rfl⟩ := CyclotomicRamifiedReduction.exists_linear x
  change ‖integralEmbedding _‖ ≤ 1
  rw [integralEmbedding_linear, norm_linear_le_one_iff]
  exact ⟨a.property, b.property⟩

def integralHom : CyclotomicRamifiedReduction.IntegralModel →+* integers :=
  integralEmbedding.codRestrict integers integralEmbedding_mem

/-- The polynomial order is precisely the local integer ring. -/
def integralEquiv : CyclotomicRamifiedReduction.IntegralModel ≃+* integers :=
  RingEquiv.ofBijective integralHom ⟨
    fun _ _ h => integralEmbedding_injective (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨a, b, rfl⟩ := exists_linear x
      obtain ⟨ha, hb⟩ := (norm_linear_le_one_iff a b).mp hx
      refine ⟨CyclotomicRamifiedReduction.linear ⟨a, ha⟩ ⟨b, hb⟩, ?_⟩
      apply Subtype.ext
      exact integralEmbedding_linear _ _⟩

end Cubic.QuadraticCorrespondence.CyclotomicRamifiedField
