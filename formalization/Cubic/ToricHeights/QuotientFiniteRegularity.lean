import Cubic.ToricHeights.QuotientFiniteCompact

/-!
# Regularity and additivity of the original finite local data

These are properties of the residue-weighted definitions before any integral
cutoff. They allow the finite adelic logarithm and height to be assembled on
the restricted product, independently of the Fourier evaluations.
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientFiniteRegularity

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois QuotientLocalCharacters
open QuotientFiniteHeight LocalLogarithmNormalization
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

variable (p : ℕ) [Fact p.Prime]

section Split
variable [Fact (p % 3 = 1)]

theorem split_logarithm_mul (P Q : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    splitLogarithm p (P * Q) = splitLogarithm p P + splitLogarithm p Q := by
  ext <;> simp [splitLogarithm, splitCoordinates, splitSecondCoordinates,
    localCocharacter_mul, realCoordinates, placeContribution] <;> ring

theorem continuous_splitLogarithm : Continuous (splitLogarithm p) := by
  have heq : splitLogarithm p = (fun x => conjugateAverage
      (normalizedLog p (SplitLocalModel.rayCoordinates p x))) ∘
        QuotientLocalModels.splitEquiv p := by
    funext P
    simp only [Function.comp_apply, splitLogarithm_eq, QuotientLocalModels.splitEquiv_apply]
  rw [heq]
  exact ((SplitLocalModel.locallyConstant_valuation p).comp (fun n =>
    conjugateAverage (normalizedLog p (realCoordinates n.toAdd)))).continuous.comp
      (QuotientLocalModels.splitEquiv p).continuous

theorem continuous_splitInverseHeight (s₀ σ : ℂ) :
    Continuous (splitInverseHeight p s₀ σ) := by
  have heq : splitInverseHeight p s₀ σ = SplitLocalModel.inverseHeight p s₀ σ ∘
      QuotientLocalModels.splitEquiv p := by
    funext P
    simp only [Function.comp_apply, splitInverseHeight_eq, QuotientLocalModels.splitEquiv_apply]
  rw [heq]
  exact ((SplitLocalModel.locallyConstant_valuation p).comp (fun n =>
    (p : ℂ) ^ supportFunction s₀ σ (realCoordinates n.toAdd))).continuous.comp
      (QuotientLocalModels.splitEquiv p).continuous

end Split

section Inert
variable [Fact (p % 3 = 2)]

theorem inert_logarithm_mul (P Q : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    inertLogarithm p (P * Q) = inertLogarithm p P + inertLogarithm p Q := by
  ext <;> simp [inertLogarithm, inertCoordinates, localCocharacter_mul,
    realCoordinates, placeContribution] <;> ring

theorem continuous_inertLogarithm : Continuous (inertLogarithm p) := by
  have heq : inertLogarithm p = (fun x => normalizedLog p
      (InertLocalModel.rayCoordinates p x)) ∘ QuotientLocalModels.inertEquiv p := by
    funext P
    simp only [Function.comp_apply, inertLogarithm_eq, QuotientLocalModels.inertEquiv_apply]
  rw [heq]
  exact ((InertLocalModel.locallyConstant_valuation p).comp (fun n =>
    normalizedLog p (realCoordinates n.toAdd.val))).continuous.comp
      (QuotientLocalModels.inertEquiv p).continuous

theorem continuous_inertInverseHeight (s₀ σ : ℂ) :
    Continuous (inertInverseHeight p s₀ σ) := by
  have heq : inertInverseHeight p s₀ σ = InertLocalModel.inverseHeight p s₀ σ ∘
      QuotientLocalModels.inertEquiv p := by
    funext P
    simp only [Function.comp_apply, inertInverseHeight_eq, QuotientLocalModels.inertEquiv_apply]
  rw [heq]
  exact ((InertLocalModel.locallyConstant_valuation p).comp (fun n =>
    (p : ℂ) ^ supportFunction s₀ σ (realCoordinates n.toAdd.val))).continuous.comp
      (QuotientLocalModels.inertEquiv p).continuous

end Inert

theorem ramified_logarithm_mul (P Q : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ramifiedLogarithm (P * Q) = ramifiedLogarithm P + ramifiedLogarithm Q := by
  ext <;> simp [ramifiedLogarithm, ramifiedCoordinates, localCocharacter_mul,
    realCoordinates, placeContribution] <;> ring

private theorem continuous_ramified_rayCoordinates : Continuous RamifiedLocalModel.rayCoordinates :=
  RamifiedLocalModel.continuous_logarithmicOrder.prodMk
    RamifiedLocalModel.continuous_logarithmicOrder

theorem continuous_ramifiedLogarithm : Continuous ramifiedLogarithm := by
  have heq : ramifiedLogarithm = (fun x => normalizedLog 3
      (RamifiedLocalModel.rayCoordinates x)) ∘ QuotientLocalModels.ramifiedEquiv := by
    funext P
    simp only [Function.comp_apply, ramifiedLogarithm_eq, QuotientLocalModels.ramifiedEquiv_apply]
  rw [heq]
  have hc : Continuous (normalizedLog 3) := by unfold normalizedLog; fun_prop
  exact (hc.comp continuous_ramified_rayCoordinates).comp
    QuotientLocalModels.ramifiedEquiv.continuous

theorem continuous_ramifiedInverseHeight (s₀ σ : ℂ) :
    Continuous (ramifiedInverseHeight s₀ σ) := by
  have heq : ramifiedInverseHeight s₀ σ = RamifiedLocalModel.inverseHeight s₀ σ ∘
      QuotientLocalModels.ramifiedEquiv := by
    funext P
    simp only [Function.comp_apply, ramifiedInverseHeight_eq, QuotientLocalModels.ramifiedEquiv_apply]
  rw [heq]
  apply Continuous.comp _ QuotientLocalModels.ramifiedEquiv.continuous
  unfold RamifiedLocalModel.inverseHeight
  exact Continuous.const_cpow
    ((supportFunction_continuous s₀ σ).comp continuous_ramified_rayCoordinates)
    (by norm_num)

end Cubic.ToricHeights.QuotientFiniteRegularity
