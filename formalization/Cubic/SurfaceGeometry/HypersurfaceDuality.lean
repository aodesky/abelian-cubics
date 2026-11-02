import Cubic.SurfaceGeometry.HypersurfaceDualityData
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

noncomputable section

namespace Cubic.SurfaceGeometry.HypersurfaceDuality

open HypersurfaceDualityData

variable (k : Type*) [Field k]

theorem dualCoefficient_apply (φ : DualTerm k) (p : Ambient k) :
    volumeCoefficient k (φ p) = p * dualCoefficient k φ := by
  have he : φ p = p • φ 1 := by
    simpa only [smul_eq_mul, mul_one] using φ.map_smul p (1 : Ambient k)
  rw [he, map_smul]
  rfl

theorem dualCoefficient_differential (f : Ambient k) (φ : DualTerm k) :
    dualCoefficient k (dualDifferential k f φ) = f * dualCoefficient k φ := by
  change volumeCoefficient k (φ (f * 1)) = _
  simpa only [mul_one] using dualCoefficient_apply k φ f

theorem dual_range (f : Ambient k) :
    (LinearMap.range (dualDifferential k f)).map (dualCoefficient k).toLinearMap =
      Ideal.span {f} := by
  ext p
  rw [Submodule.mem_map, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨φ, ⟨ψ, rfl⟩, hp⟩
    refine ⟨dualCoefficient k ψ, ?_⟩
    exact hp.symm.trans (dualCoefficient_differential k f ψ)
  · rintro ⟨q, rfl⟩
    refine ⟨dualDifferential k f ((dualCoefficient k).symm q), ⟨_, rfl⟩, ?_⟩
    change dualCoefficient k (dualDifferential k f ((dualCoefficient k).symm q)) = _
    rw [dualCoefficient_differential, LinearEquiv.apply_symm_apply]

/-- The cohomology of the actual dual complex, identified by evaluation on 1
and the coefficient of the ambient volume form. -/
def cokernelEquiv (f : Ambient k) :
    DualCohomology k f ≃ₗ[Ambient k] Ambient k ⧸ Ideal.span {f} :=
  Submodule.Quotient.equiv _ _ (dualCoefficient k) (dual_range k f)

theorem cokernelEquiv_mk (f : Ambient k) (φ : DualTerm k) :
    cokernelEquiv k f ((LinearMap.range (dualDifferential k f)).mkQ φ) =
      Ideal.Quotient.mk _ (dualCoefficient k φ) := rfl

theorem homogeneousMap_iff (a n : ℤ) (φ : DualTerm k) :
    HomogeneousMap k a φ n ↔ Homogeneous k (dualCoefficient k φ) (a + n - 4) := by
  constructor
  · intro h
    have he := h 0 1 (MvPolynomial.isWeightedHomogeneous_one k _)
    simpa only [zero_add] using he
  · intro h d p hp
    rw [dualCoefficient_apply]
    have he := hp.mul h
    convert he using 1 <;> ring

theorem dualDifferential_homogeneous {f : Ambient k} {a n : ℤ}
    (hf : Homogeneous k f a) {φ : DualTerm k} (hφ : HomogeneousMap k 0 φ n) :
    HomogeneousMap k a (dualDifferential k f φ) n := by
  rw [homogeneousMap_iff] at hφ ⊢
  rw [dualCoefficient_differential]
  have he := hf.mul hφ
  convert he using 1 <;> ring

/-- The twist is determined by the grading on Hom, rather than by the desired
adjunction formula. -/
theorem cohomology_degree_iff (f : Ambient k) (a n : ℤ) (x : DualCohomology k f) :
    CohomologyDegree k f a n x ↔ ∃ p : Ambient k,
      Homogeneous k p (a + n - 4) ∧
        Ideal.Quotient.mk (Ideal.span {f}) p = cokernelEquiv k f x := by
  constructor
  · rintro ⟨φ,hφ,hx⟩
    refine ⟨dualCoefficient k φ, (homogeneousMap_iff k a n φ).mp hφ, ?_⟩
    rw [← cokernelEquiv_mk, hx]
  · rintro ⟨p,hp,hx⟩
    refine ⟨(dualCoefficient k).symm p, ?_, ?_⟩
    · rw [homogeneousMap_iff, LinearEquiv.apply_symm_apply]
      exact hp
    · apply (cokernelEquiv k f).injective
      rw [cokernelEquiv_mk, LinearEquiv.apply_symm_apply, hx]

theorem multiplication_range (f : Ambient k) :
    LinearMap.range (multiplication k f) = Ideal.span {f} := by
  ext p
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  change (∃ q, f * q = p) ↔ ∃ q, p = f * q
  exact exists_congr fun _ => eq_comm

/-- The nonzero hypersurface equation gives the free resolution used above. -/
theorem resolution_exact {f : Ambient k} (hf : f ≠ 0) :
    Function.Injective (multiplication k f) ∧
    LinearMap.range (multiplication k f) =
      LinearMap.ker (Ideal.span {f}).mkQ := by
  refine ⟨fun p q h => mul_left_cancel₀ hf h, ?_⟩
  rw [Submodule.ker_mkQ, multiplication_range]

end Cubic.SurfaceGeometry.HypersurfaceDuality
