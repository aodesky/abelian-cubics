import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! An equalizer of an endomorphism of a normal domain is normal. Embed its
fraction field into the ambient fraction field, use ambient normality, and
clear a fixed denominator to prove that the resulting element is fixed. -/

noncomputable section

namespace Cubic.SurfaceGeometry.FixedRingNormality

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
  [IsIntegrallyClosed A]

theorem equalizer_normal (τ : A →ₐ[R] A) :
    IsIntegrallyClosed (AlgHom.equalizer τ (AlgHom.id R A)) := by
  let S := AlgHom.equalizer τ (AlgHom.id R A)
  let g : S →ₐ[S] FractionRing A := Algebra.ofId S (FractionRing A)
  have hg : Function.Injective g :=
    (IsFractionRing.injective A (FractionRing A)).comp Subtype.val_injective
  let φ : FractionRing S →ₐ[S] FractionRing A := IsFractionRing.liftAlgHom hg
  refine ⟨IsFractionRing.injective S (FractionRing S), fun {x} => ⟨?_, ?_⟩⟩
  · intro hx
    have hi : IsIntegral A (φ x) := (hx.map φ).tower_top
    obtain ⟨y,hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    obtain ⟨a,b,hb,hrep⟩ := IsFractionRing.div_surjective (A := S) x
    have hbS : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hbA : b.val ≠ 0 := by
      intro he
      exact hbS (Subtype.ext he)
    have hbF : algebraMap A (FractionRing A) b.val ≠ 0 := by
      intro he
      exact hbA (IsFractionRing.injective A (FractionRing A)
        (he.trans (map_zero _).symm))
    have hφ : φ x = algebraMap A (FractionRing A) a.val /
        algebraMap A (FractionRing A) b.val := by
      rw [← hrep, map_div₀, AlgHom.commutes, AlgHom.commutes]
      rfl
    have hab : y * b.val = a.val := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [map_mul, ← eq_div_iff hbF]
      exact hy.trans hφ
    have hfixed : τ y = y := by
      have ha : τ a.val = a.val := a.property
      have hb : τ b.val = b.val := b.property
      have h := congrArg τ hab
      rw [map_mul, ha, hb] at h
      exact mul_right_cancel₀ hbA (h.trans hab.symm)
    let ys : S := ⟨y,hfixed⟩
    refine ⟨ys, φ.injective ?_⟩
    change φ (algebraMap S (FractionRing S) ys) = φ x
    rw [AlgHom.commutes]
    exact hy
  · rintro ⟨y,rfl⟩
    exact isIntegral_algebraMap

end Cubic.SurfaceGeometry.FixedRingNormality
