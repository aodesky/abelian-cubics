import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Continuous characters of the real logarithmic coordinate

Use mathlib's covering-space lifting theorem for the circle exponential.
A character lifts uniquely with value zero at the origin; uniqueness of the
lift on `ℝ × ℝ` proves additivity. Mathlib's real-linearity theorem for
continuous additive maps then gives the paper's `exp(2π i t u)` convention.
This supplies the real-character classification needed after level descent.
-/

noncomputable section

namespace Cubic.PoissonSummation.RealCharacter

/-- The paper's positive-sign character; Fourier transforms use its inverse. -/
def character (t : ℝ) : PontryaginDual (Multiplicative ℝ) where
  toFun u := Circle.exp (2 * Real.pi * t * u.toAdd)
  map_one' := by simp
  map_mul' u v := by
    change Circle.exp (2 * Real.pi * t * (u.toAdd + v.toAdd)) = _
    rw [mul_add, Circle.exp_add]
  continuous_toFun := Circle.exp.continuous.comp
    (continuous_const.mul (show Continuous (fun u : Multiplicative ℝ => u.toAdd) from continuous_id))

/-- Every continuous unitary character of `ℝ` has the analyst's `2π` parameter. -/
theorem exists_parameter (χ : PontryaginDual (Multiplicative ℝ)) :
    ∃ t : ℝ, ∀ u : ℝ, χ (Multiplicative.ofAdd u) = Circle.exp (2 * Real.pi * t * u) := by
  let f : C(ℝ, Circle) := ⟨fun u => χ (Multiplicative.ofAdd u), χ.continuous⟩
  have hf₀ : f 0 = 1 := map_one χ
  have hfadd (u v : ℝ) : f (u + v) = f u * f v := map_mul χ _ _
  obtain ⟨F, ⟨hF₀, hF⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    f 0 0 (by simpa using hf₀.symm)
  have hlift (u : ℝ) : Circle.exp (F u) = f u := congrFun hF u
  let f₂ : C(ℝ × ℝ, Circle) := ⟨fun x => f (x.1 + x.2), by fun_prop⟩
  obtain ⟨F₂, _, huniq⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    f₂ (0, 0) 0 (by simpa [f₂] using hf₀.symm)
  let A : C(ℝ × ℝ, ℝ) := ⟨fun x => F (x.1 + x.2), by fun_prop⟩
  let B : C(ℝ × ℝ, ℝ) := ⟨fun x => F x.1 + F x.2, by fun_prop⟩
  have hA : A = F₂ := huniq A ⟨by simpa [A] using hF₀, by
    funext x
    exact hlift (x.1 + x.2)⟩
  have hB : B = F₂ := huniq B ⟨by simp [B, hF₀], by
    funext x
    exact (Circle.exp_add _ _).trans ((congrArg₂ (· * ·) (hlift x.1) (hlift x.2)).trans
      (hfadd x.1 x.2).symm)⟩
  have hadd (u v : ℝ) : F (u + v) = F u + F v :=
    DFunLike.congr_fun (hA.trans hB.symm) (u, v)
  let L : ℝ →+ ℝ := ⟨⟨F, hF₀⟩, hadd⟩
  have hlinear (u : ℝ) : F u = u * F 1 := by
    simpa using map_real_smul L F.continuous u 1
  refine ⟨F 1 / (2 * Real.pi), fun u => ?_⟩
  change f u = _
  rw [← hlift, hlinear]
  congr 1
  field_simp

theorem character_surjective : Function.Surjective character := by
  intro χ
  obtain ⟨t, ht⟩ := exists_parameter χ
  exact ⟨t, DFunLike.ext _ _ fun u => (ht u.toAdd).symm⟩

/-- Uniqueness of the real spectral parameter, with no integer ambiguity. -/
theorem character_injective : Function.Injective character := by
  intro t v h
  let f : C(ℝ, Circle) := ⟨fun u => character t (Multiplicative.ofAdd u),
    (character t).continuous⟩
  obtain ⟨F, _, huniq⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    f 0 0 (by simp [f, character])
  let A (r : ℝ) : C(ℝ, ℝ) := ⟨fun u => 2 * Real.pi * r * u, by fun_prop⟩
  have ht : A t = F := huniq (A t) ⟨by simp [A], rfl⟩
  have hv : A v = F := huniq (A v) ⟨by simp [A], by
    funext u
    exact (DFunLike.congr_fun h (Multiplicative.ofAdd u)).symm⟩
  have he := DFunLike.congr_fun (ht.trans hv.symm) 1
  dsimp [A] at he
  nlinarith [Real.pi_pos]

/-- Joint continuity gives continuity into the actual compact-open topology. -/
theorem continuous_character : Continuous character := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun x : ℝ × Multiplicative ℝ =>
    Circle.exp (2 * Real.pi * x.1 * x.2.toAdd))
  exact Circle.exp.continuous.comp
    ((continuous_const.mul continuous_fst).mul (show Continuous
      (fun x : ℝ × Multiplicative ℝ => x.2.toAdd) from continuous_snd))

/-- Parameter addition is pointwise multiplication of characters. -/
def characterHom : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ) where
  toFun t := character t.toAdd
  map_one' := by
    apply DFunLike.ext
    intro u
    change Circle.exp (2 * Real.pi * 0 * u.toAdd) = 1
    simp
  map_mul' t v := by
    apply DFunLike.ext
    intro u
    change Circle.exp (2 * Real.pi * (t.toAdd + v.toAdd) * u.toAdd) = _
    rw [mul_add, add_mul, Circle.exp_add]
    rfl
  continuous_toFun := continuous_character

/-- The analyst's real parameter is a topological group isomorphism, not only
a bijective parametrization. Openness follows from mathlib's open mapping
theorem for sigma-compact groups. -/
def characterEquiv : Multiplicative ℝ ≃ₜ* PontryaginDual (Multiplicative ℝ) := by
  let e : Multiplicative ℝ ≃* PontryaginDual (Multiplicative ℝ) :=
    MulEquiv.ofBijective characterHom.toMonoidHom ⟨character_injective, character_surjective⟩
  let h : Multiplicative ℝ ≃ₜ PontryaginDual (Multiplicative ℝ) :=
    e.toEquiv.toHomeomorphOfContinuousOpen continuous_character
      (characterHom.toMonoidHom.isOpenMap_of_sigmaCompact character_surjective
        continuous_character)
  exact { e with continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }

@[simp]
theorem characterEquiv_apply (t : Multiplicative ℝ) :
    characterEquiv t = character t.toAdd := rfl

end Cubic.PoissonSummation.RealCharacter
