import Cubic.OrbitParametrization.C3Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Basic properties of `C₃`-algebras

Every `C₃`-algebra has dimension three over `ℚ`, its fixed elements are
rational, and the pairing `(a,b) ↦ Σ_g g(ab)` is nondegenerate. These are the
facts about `C₃`-algebras used in [O'Desky–Rosen, Lemma 2.2].
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open Module

variable (K : C3Alg)

/-- The sum of the conjugates. -/
def traceSum (y : K.carrier) : K.carrier := ∑ g : C3, K.act g y

theorem traceSum_fixed (y : K.carrier) (h : C3) : K.act h (traceSum K y) = traceSum K y := by
  simp only [traceSum, map_sum, ← AlgEquiv.mul_apply, ← map_mul]
  exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)

theorem finrank_eq_three : finrank ℚ K.carrier = 3 := by
  rcases K.model with ⟨-, h, -⟩ | ⟨e, -⟩
  · exact h
  · rw [e.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, ZMod.card]

instance : FiniteDimensional ℚ K.carrier :=
  Module.finite_of_finrank_pos (by rw [finrank_eq_three]; norm_num)

instance : Nontrivial K.carrier :=
  Module.nontrivial_of_finrank_pos (R := ℚ) (by rw [finrank_eq_three]; norm_num)

/-- Elements fixed by `C₃` are rational. -/
theorem fixed_rational (y : K.carrier) (hy : ∀ g : C3, K.act g y = y) :
    ∃ q : ℚ, algebraMap ℚ K.carrier q = y := by
  rcases K.model with ⟨hK, hdim, hinj⟩ | ⟨e, he⟩
  · letI : Field K.carrier := hK.toField
    let H : Subgroup (K.carrier ≃ₐ[ℚ] K.carrier) := K.act.range
    have hcard : Nat.card H = 3 := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_eq_fintype_card]
      rfl
    have hfix := IntermediateField.finrank_fixedField_eq_card H
    have htower := Module.finrank_mul_finrank ℚ (IntermediateField.fixedField H) K.carrier
    rw [hfix, hcard, hdim] at htower
    have h1 : finrank ℚ (IntermediateField.fixedField H) = 1 := by omega
    have hmem : y ∈ IntermediateField.fixedField H := by
      rw [IntermediateField.mem_fixedField_iff]
      rintro f ⟨g, rfl⟩
      exact hy g
    rw [IntermediateField.finrank_eq_one_iff.mp h1, IntermediateField.mem_bot] at hmem
    exact hmem
  · refine ⟨e y 0, ?_⟩
    apply e.injective
    ext h
    have hc : e y h = e y 0 := by
      have := he (Multiplicative.ofAdd h) y 0
      rw [hy] at this
      simpa using this.symm
    rw [AlgEquiv.commutes]
    simp [hc]

theorem traceSum_rational (y : K.carrier) : ∃ q : ℚ, algebraMap ℚ K.carrier q = traceSum K y :=
  fixed_rational K _ (traceSum_fixed K y)

/-- The trace pairing is nondegenerate. -/
theorem pairing_nondegenerate (a : K.carrier) (ha : a ≠ 0) :
    ∃ b : K.carrier, traceSum K (a * b) ≠ 0 := by
  rcases K.model with ⟨hK, -, -⟩ | ⟨e, he⟩
  · letI : Field K.carrier := hK.toField
    refine ⟨a⁻¹, ?_⟩
    rw [mul_inv_cancel₀ ha]
    simp only [traceSum, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card C3 : K.carrier) = algebraMap ℚ K.carrier 3 := by
      rw [show Fintype.card C3 = 3 from rfl]
      simp
    rw [this, mul_one]
    intro h0
    have := (algebraMap ℚ K.carrier).injective (h0.trans (map_zero _).symm)
    norm_num at this
  · have hne : e a ≠ 0 := by
      intro h0
      exact ha (e.injective (h0.trans (map_zero e).symm))
    obtain ⟨h, hh⟩ : ∃ h, e a h ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (funext hc)
    refine ⟨e.symm (Pi.single h 1), ?_⟩
    intro h0
    have h1 := congrArg (fun z => e z 0) h0
    simp only [traceSum, map_sum, Finset.sum_apply, he, map_mul, AlgEquiv.apply_symm_apply,
      map_zero, Pi.zero_apply, Pi.mul_apply] at h1
    rw [Fintype.sum_equiv (Equiv.refl _) _ (fun g => if (Multiplicative.toAdd g) = h then e a h
      else 0) (fun g => by
        by_cases hg : Multiplicative.toAdd g = h
        · simp [hg, Pi.single_apply]
        · simp [hg, zero_add])] at h1
    have h2 : ∀ x : C3, (Multiplicative.toAdd x = h) ↔ x = Multiplicative.ofAdd h :=
      fun x => ⟨fun hx => by rw [← hx]; rfl, fun hx => by rw [hx]; rfl⟩
    simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact hh h1

end Cubic.OrbitParametrization.C3Algebra
