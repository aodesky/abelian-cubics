import CubicTargets.PoissonSummation.HeightFourierTransform
import Cubic.ToricHeights.BasicFacts
import Cubic.PoissonSummation.ArchimedeanFourier
import Cubic.PoissonSummation.RealCharacter

/-!
# The infinite place of `prop:heightFourierTransform`

We follow the paper's proof.

* `1_∞^{D₀} = 1`, and the height factors through the radial coordinate `c = log|·|`.
  The coordinate satisfies `ℓ_w(x) = c(x) v₀` (`ArchimedeanQuotientLogarithm.localCocharacter_eq`).
  So the height is `K_∞^max`-invariant, where `K_∞^max` is the kernel of `c`.
* Ramified `χ`: the transform vanishes by Schur's lemma (`characterIntegral_eq_zero_of_invariant`).
* Unramified `χ`: `χ` factors through `c`, since `T(ℝ) = K_∞^max × (radial section)`.
  The resulting continuous character of `ℝ` is `u ↦ e(tu)` (`RealCharacter.exists_parameter`).
  Then `m = -(t/2)(x+y)` is the unique `Γ`-invariant functional with `χ = e(⟨ℓ_w(·), m⟩)`.
* Formula: `c` pushes the normalized Haar measure forward to `du` (`ArchimedeanHaar.map_measure`).
  The integral splits over the two rays `ℝ≥0 v₀` and `ℝ≥0 (-v₀)`, as in the paper
  (`ArchimedeanFourier.integral_positive`, `integral_negative`). The `2πi` form is
  `ArchimedeanFourier.fourier_eq_paper_factor`, with `t = m(v₀)`.
-/

noncomputable section

namespace Cubic.PoissonSummation.ArchimedeanHeightFourier

open MeasureTheory
open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open Cubic.ToricHeights.ArchimedeanQuotientLogarithm (Points coordinate radialSection
  coordinate_mul coordinate_radialSection radialSection_add continuous_coordinate
  continuous_radialSection)
open IntegralityStabilizer
open CubicTargets.ToricHeights.BasicFacts
open CubicTargets.PoissonSummation.HeightFourierTransform
open CubicTargets.PoissonSummation.ChimDefn (invariantDual)
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology ArchimedeanHaarData

theorem archimedeanLog_eq (x : Points) : archimedeanLog x = (-coordinate x, -coordinate x) :=
  ArchimedeanQuotientLogarithm.localCocharacter_eq x

theorem mem_maxCompact_iff (k : Points) : k ∈ archimedeanMaxCompact ↔ coordinate k = 0 := by
  rw [MonoidHom.mem_ker]
  exact ofAdd_eq_one

theorem coordinate_inv (x : Points) : coordinate x⁻¹ = -coordinate x := by
  have h := coordinate_mul x⁻¹ x
  rw [inv_mul_cancel, ArchimedeanQuotientLogarithm.coordinate_one] at h
  linarith

/-- `H_∞(x,-s,D₀)` depends only on `c(x)`. -/
theorem infiniteIntegrand_eq (s₀ σ : ℂ) (x : Points) :
    infiniteIntegrand s₀ σ x = ArchimedeanFourier.inverseHeight s₀ σ (coordinate x) := by
  simp [infiniteIntegrand, archimedeanIndicator, ArchimedeanQuotientLogarithm.inverseHeight_eq,
    ArchimedeanFourier.inverseHeight]

theorem continuous_character_inv (χ : PontryaginDual Points) :
    Continuous (fun x => ((χ x : Circle) : ℂ)⁻¹) :=
  (continuous_subtype_val.comp χ.continuous).inv₀ fun _ => Circle.coe_ne_zero _

/-- Absolute convergence at infinity, for every unitary `χ`. -/
theorem integrable (χ : PontryaginDual Points) (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    Integrable (fun x => infiniteIntegrand s₀ σ x * ((χ x : Circle) : ℂ)⁻¹)
      ArchimedeanHaar.measure := by
  have hi : Integrable (ArchimedeanFourier.inverseHeight s₀ σ)
      (ArchimedeanHaar.measure.map coordinate) := by
    rw [ArchimedeanHaar.map_measure]
    exact ArchimedeanFourier.integrable_inverseHeight s₀ σ h₀ hσ
  have h := (integrable_map_measure hi.aestronglyMeasurable
    continuous_coordinate.measurable.aemeasurable).mp hi
  have hH : Integrable (infiniteIntegrand s₀ σ) ArchimedeanHaar.measure := by
    simpa only [Function.comp_def, ← infiniteIntegrand_eq] using h
  refine hH.norm.mono' (hH.aestronglyMeasurable.mul
    (continuous_character_inv χ).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [norm_mul_character_inv]

/-- Schur's lemma at infinity. This holds for every `s`. -/
theorem fourier_eq_zero_of_ramified (χ : PontryaginDual Points)
    (hχ : ∃ k ∈ archimedeanMaxCompact, χ k ≠ 1) (s₀ σ : ℂ) : infiniteFourier s₀ σ χ = 0 := by
  obtain ⟨k, hk, hχk⟩ := hχ
  apply characterIntegral_eq_zero_of_invariant _ _ χ k _ hχk
  intro x
  rw [infiniteIntegrand_eq, infiniteIntegrand_eq, coordinate_mul, (mem_maxCompact_iff k).mp hk,
    zero_add]

/-- The restriction of `χ` to the radial section, a continuous character of `ℝ`. -/
def radialCharacter (χ : PontryaginDual Points) : PontryaginDual (Multiplicative ℝ) where
  toFun u := χ (radialSection u.toAdd)
  map_one' := by
    have h := radialSection_add 0 0
    rw [add_zero] at h
    have h1 : radialSection 0 = 1 := by simpa using h
    change χ (radialSection 0) = 1
    rw [h1, map_one]
  map_mul' u v := by
    change χ (radialSection (u.toAdd + v.toAdd)) = _
    rw [radialSection_add, map_mul]
  continuous_toFun := χ.continuous.comp (continuous_radialSection.comp continuous_toAdd)

/-- An unramified character is `e(t c(x))`. -/
theorem exists_parameter (χ : PontryaginDual Points) (hχ : ∀ k ∈ archimedeanMaxCompact, χ k = 1) :
    ∃ t : ℝ, ∀ x, χ x = Circle.exp (2 * Real.pi * t * coordinate x) := by
  obtain ⟨t, ht⟩ := RealCharacter.exists_parameter (radialCharacter χ)
  refine ⟨t, fun x => ?_⟩
  set c := coordinate x
  have hk : (radialSection c)⁻¹ * x ∈ archimedeanMaxCompact := by
    rw [mem_maxCompact_iff, coordinate_mul, coordinate_inv, coordinate_radialSection]
    simp [c]
  have hx : x = radialSection c * ((radialSection c)⁻¹ * x) := by group
  rw [hx, map_mul, hχ _ hk, mul_one]
  exact ht c

/-- The functional `m = -(t/2)(x+y)`, so that `m(v₀) = t`. -/
def functional (t : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  (-(t / 2)) • (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ)

theorem functional_apply (t : ℝ) (n : ℝ × ℝ) : functional t n = -(t / 2) * (n.1 + n.2) := by
  simp [functional]
  ring

theorem functional_mem (t : ℝ) : functional t ∈ invariantDual := by
  intro n
  rw [functional_apply, functional_apply]
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring

/-- A `Γ`-invariant functional is determined by its value on `v₀`. -/
theorem eq_of_invariant {m m' : (ℝ × ℝ) →ₗ[ℝ] ℝ} (hm : m ∈ invariantDual) (hm' : m' ∈ invariantDual)
    (h : m (-1, -1) = m' (-1, -1)) : m = m' := by
  have key : ∀ f : (ℝ × ℝ) →ₗ[ℝ] ℝ, f ∈ invariantDual → ∀ n : ℝ × ℝ,
      f n = -(f (-1, -1)) / 2 * (n.1 + n.2) := by
    intro f hf n
    have h10 : f (0, 1) = f (1, 0) := hf (1, 0)
    have hn : n = n.1 • ((1 : ℝ), (0 : ℝ)) + n.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    have hv : ((-1 : ℝ), (-1 : ℝ)) = (-1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + (-1 : ℝ) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    have e1 : f n = n.1 * f (1, 0) + n.2 * f (0, 1) := by
      conv_lhs => rw [hn]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have e2 : f (-1, -1) = -f (1, 0) - f (0, 1) := by
      rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [e1, e2, h10]
    ring
  apply LinearMap.ext
  intro n
  rw [key m hm, key m' hm', h]

theorem circle_exp_eq_one_forall {l : ℝ} (h : ∀ c : ℝ, Circle.exp (2 * Real.pi * (c * l)) = 1) :
    l = 0 := by
  by_contra hl
  have h1 := h (1 / (2 * l))
  have he : 2 * Real.pi * (1 / (2 * l) * l) = Real.pi := by field_simp
  rw [he] at h1
  have h2 := congrArg (fun z : Circle => (z : ℂ)) h1
  simp only [Circle.coe_exp, Circle.coe_one] at h2
  rw [Complex.exp_pi_mul_I] at h2
  norm_num at h2

/-- An unramified `χ` is `e(⟨ℓ_w(·), m⟩)` for a unique `m ∈ 𝔱^∨`. -/
theorem exists_unique_m (χ : PontryaginDual Points) (hχ : ∀ k ∈ archimedeanMaxCompact, χ k = 1) :
    ∃! m : (ℝ × ℝ) →ₗ[ℝ] ℝ, m ∈ invariantDual ∧ IsExponential m χ := by
  obtain ⟨t, ht⟩ := exists_parameter χ hχ
  have hexp : IsExponential (functional t) χ := by
    intro x
    rw [ht x, archimedeanLog_eq, functional_apply]
    congr 1
    ring
  refine ⟨functional t, ⟨functional_mem t, hexp⟩, fun m' ⟨hm', hexp'⟩ => ?_⟩
  apply eq_of_invariant hm' (functional_mem t)
  apply sub_eq_zero.mp
  apply circle_exp_eq_one_forall
  intro c
  have h1 := hexp' (radialSection (-c))
  have h2 := hexp (radialSection (-c))
  rw [h1] at h2
  rw [archimedeanLog_eq, coordinate_radialSection, neg_neg] at h2
  have hsm : ∀ f : (ℝ × ℝ) →ₗ[ℝ] ℝ, f (c, c) = c * -f (-1, -1) := by
    intro f
    have : ((c : ℝ), (c : ℝ)) = (-c) • ((-1 : ℝ), (-1 : ℝ)) := by ext <;> simp
    rw [this, map_smul, smul_eq_mul]
    ring
  rw [hsm, hsm] at h2
  have : 2 * Real.pi * (c * (m' (-1, -1) - functional t (-1, -1))) =
      2 * Real.pi * (c * -functional t (-1, -1)) - 2 * Real.pi * (c * -m' (-1, -1)) := by ring
  rw [this, sub_eq_add_neg, Circle.exp_add, Circle.exp_neg, h2, mul_inv_cancel]

/-- `eqn:infiniteHeightFourierTransform`. -/
theorem fourier_eq_formula (χ : PontryaginDual Points) (m : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (hexp : IsExponential m χ) (s₀ σ : ℂ) (h₀ : 0 < s₀.re) (hσ : 0 < σ.re) :
    infiniteFourier s₀ σ χ = infiniteFormula s₀ σ m := by
  set t := m (-1, -1) with htdef
  have hχ : ∀ x, χ x = ArchimedeanFourier.character t (coordinate x) := by
    intro x
    rw [hexp x, archimedeanLog_eq, ArchimedeanFourier.character]
    have : ((-coordinate x : ℝ), (-coordinate x : ℝ)) = (coordinate x) • ((-1 : ℝ), (-1 : ℝ)) := by
      ext <;> simp
    rw [this, map_smul, smul_eq_mul, ← htdef]
    congr 1
    ring
  have hf : (fun x => infiniteIntegrand s₀ σ x * ((χ x : Circle) : ℂ)⁻¹) =
      (ArchimedeanFourier.integrand s₀ σ t) ∘ coordinate := by
    funext x
    rw [Function.comp_apply, infiniteIntegrand_eq, hχ x]
    rfl
  have hi : Integrable (ArchimedeanFourier.integrand s₀ σ t)
      (ArchimedeanHaar.measure.map coordinate) := by
    rw [ArchimedeanHaar.map_measure]
    exact ArchimedeanFourier.integrable s₀ σ t h₀ hσ
  have hint : infiniteFourier s₀ σ χ = ArchimedeanFourier.fourier s₀ σ t := by
    change (∫ x, infiniteIntegrand s₀ σ x * ((χ x : Circle) : ℂ)⁻¹ ∂ArchimedeanHaar.measure) = _
    rw [hf]
    change (∫ x, ArchimedeanFourier.integrand s₀ σ t (coordinate x) ∂ArchimedeanHaar.measure) = _
    rw [← integral_map continuous_coordinate.measurable.aemeasurable hi.aestronglyMeasurable,
      ArchimedeanHaar.map_measure]
    rfl
  rw [hint, ArchimedeanFourier.fourier_eq_paper_factor s₀ σ t h₀ hσ, infiniteFormula, ← htdef]
  ring_nf

end Cubic.PoissonSummation.ArchimedeanHeightFourier
