import Cubic.OrbitParametrization.TwistCohomologyData

noncomputable section

namespace Cubic.OrbitParametrization.TwistCohomology

open C3Algebra TwistCohomologyData

theorem not_cohomologous_inverse (c : AbsoluteGroup →* C3) (hc : Function.Surjective c) :
    ¬ Cohomologous c (inverseCocycle c) := by
  rintro ⟨a, ha⟩
  obtain ⟨τ, hτ⟩ := hc (Multiplicative.ofAdd 1)
  have h := ha τ
  simp only [inverseCocycle, MonoidHom.comp_apply, invMonoidHom_apply, hτ,
    mul_inv_cancel_right, mul_comm a] at h
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ ≠
    Multiplicative.ofAdd 1) h

theorem regular_inverse_conjugate (c : AbsoluteGroup →* C3) :
    Cohomologous (regular.comp c) (regular.comp (inverseCocycle c)) := by
  refine ⟨Equiv.inv C3, fun τ => ?_⟩
  ext g
  simp [regular, inverseCocycle, mul_comm]

theorem field_cocycles : TwistCohomologyData.Claim := by
  intro K _ _ _ ι
  have hs : Function.Surjective (restriction K) :=
    (imageEquiv K).symm.autCongr.surjective.comp
      (AlgEquiv.restrictNormalHom_surjective (F := ℚ)
        (K₁ := imageField K) (AlgebraicClosure ℚ))
  have hc : Function.Surjective (fieldCocycle K ι) := ι.symm.surjective.comp hs
  have hk : (fieldCocycle K ι).ker = (imageField K).fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    ext τ
    simp only [MonoidHom.mem_ker, fieldCocycle, restriction, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [← ι.symm.map_one, ι.symm.injective.eq_iff,
      ← (imageEquiv K).symm.autCongr.map_one,
      (imageEquiv K).symm.autCongr.injective.eq_iff]
  refine ⟨hc, ?_, ?_, ?_, not_cohomologous_inverse _ hc, regular_inverse_conjugate _⟩
  · rw [hk]
    exact IntermediateField.fixingSubgroup_isOpen (imageField K)
  · intro τ y
    change ((imageEquiv K) ((imageEquiv K).symm
      ((τ.restrictNormal (imageField K)) (imageEquiv K y))) : AlgebraicClosure ℚ) = _
    rw [AlgEquiv.apply_symm_apply]
    exact AlgEquiv.restrictNormal_commutes τ (imageField K) (imageEquiv K y)
  · intro τ
    simp [fieldCocycle, inverseCocycle]

end Cubic.OrbitParametrization.TwistCohomology
