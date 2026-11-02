import CubicTargets.PoissonSummation.HeightFourierTransform
import Cubic.ToricHeights.BasicFacts
import Cubic.PoissonSummation.CountableQuotient
import Cubic.PoissonSummation.LatticeSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Local Fourier transforms at a finite place away from three

This file does the analysis for a finite place `w | v` with `v ≠ 3`, in a form that applies
to every such place. The inputs are:

* the exact sequence `1 → K_v^max → T(ℚ_v) → X_*(T_E)^{Γ(w/v)} → 0` of `prop:basicfacts`;
* the formula `H_v(x,-s) = q_v^{φ(ℓ_w(x))}`;
* the description `1_v^{D₀}(x) = 1 ⟺ ℓ_w(x) ∈ ℝ≥0 v₁ + ℝ≥0 v₂` of `prop:localIntegrality`.

The paper's proof has three steps.

1. Schur's lemma: if `χ` is ramified, the transform vanishes (`fourier_eq_zero_of_ramified`).
2. If `χ` is unramified, it factors through `ℓ_w` (`exists_unique_descends`).
3. `ℓ_w` pushes `d^×x_v` forward to counting measure on `N_w`, because `K_v^max` has mass one.
   So the integral is the lattice sum (`hasSum_lattice`, `hasSum_cone`).

Holomorphy is proved from the lattice sum. On `{Re σ > a}` its terms are dominated by the
summable `q_v^{-a(n₁+n₂)}`, so the sum converges locally uniformly (`differentiableOn_fourier`).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace Cubic.PoissonSummation.UnramifiedLocalFourier

open MeasureTheory
open Cubic.ToricHeights Cubic.OrbitParametrization
open CubicTargets.ToricHeights.BasicFacts
open CubicTargets.PoissonSummation.HeightFourierTransform

/-! ### The support function on the cone -/

/-- `n₁ + n₂`, the sum of the ray coordinates of `n`. -/
def degree (n : ℤ × ℤ) : ℤ := n.1 + n.2

theorem degree_nonneg {n : ℤ × ℤ} (hn : LatticeCone.InCone n) : 0 ≤ degree n := by
  have h := (LatticeCone.inCone_iff n).mp hn
  unfold degree
  omega

/-- On the cone, `φ(n) = -(n₁ + n₂) σ`, independently of `s₀`. -/
theorem supportFunction_cone (s₀ σ : ℂ) {n : ℤ × ℤ} (hn : LatticeCone.InCone n) :
    supportFunction s₀ σ (cocharacterEmbedding n) = -σ * (degree n : ℂ) := by
  obtain ⟨h1, h2⟩ := hn
  have h1' : (0 : ℝ) ≤ ((CocharacterLattice.coordinates n).1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ ((CocharacterLattice.coordinates n).2 : ℝ) := by exact_mod_cast h2
  have hmin : min (0 : ℝ) (min ((CocharacterLattice.coordinates n).1 : ℝ)
      ((CocharacterLattice.coordinates n).2 : ℝ)) = 0 := min_eq_left (le_min h1' h2')
  have hsum : ((CocharacterLattice.coordinates n).1 : ℝ) + ((CocharacterLattice.coordinates n).2 : ℝ)
      = (degree n : ℝ) := by
    simp only [CocharacterLattice.coordinates, LinearMap.coe_mk, AddHom.coe_mk, degree]
    push_cast
    ring
  simp only [supportFunction, cocharacterEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hmin]
  have hc : (((CocharacterLattice.coordinates n).1 : ℝ) : ℂ) +
      (((CocharacterLattice.coordinates n).2 : ℝ) : ℂ) = ((degree n : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hsum
  push_cast at hc ⊢
  rw [hc]
  ring

/-- `‖q^{-σ d}‖ = q^{-d Re σ}` for `q > 0`. -/
theorem norm_cpow_degree {q : ℕ} (hq : 0 < q) (σ : ℂ) (d : ℤ) :
    ‖(q : ℂ) ^ (-σ * (d : ℂ))‖ = (q : ℝ) ^ (-(σ.re) * d) := by
  rw [Complex.norm_natCast_cpow_of_pos hq]
  congr 1
  simp

/-- Summability of the dominating series `∑_{n ∈ cone} r^{n₁+n₂}` for `0 ≤ r < 1`. -/
theorem summable_cone_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : LatticeCone.ConePoint => r ^ LatticeCone.degree n) := by
  have hc := (LatticeSeries.hasSum_cone (r : ℂ) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).summable
  have : (fun n : LatticeCone.ConePoint => ((r ^ LatticeCone.degree n : ℝ) : ℂ)) =
      (fun n : LatticeCone.ConePoint => (r : ℂ) ^ LatticeCone.degree n) := by
    funext n; push_cast; rfl
  rw [← this] at hc
  exact Complex.summable_ofReal.mp hc

/-- The dominating series over any subgroup of the cocharacter lattice. -/
theorem summable_bound (L : AddSubgroup (ℤ × ℤ)) {q : ℕ} (hq : 1 < q) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : {n : L // LatticeCone.InCone n} =>
      (q : ℝ) ^ (-a * (degree (n.1 : ℤ × ℤ) : ℝ))) := by
  set r : ℝ := (q : ℝ) ^ (-a) with hr
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq' (by linarith)
  let i : {n : L // LatticeCone.InCone n} → LatticeCone.ConePoint := fun n => ⟨n.1.1, n.2⟩
  have hi : Function.Injective i := by
    intro x y h
    have h' : ((x.1 : L) : ℤ × ℤ) = ((y.1 : L) : ℤ × ℤ) := congrArg (fun z : LatticeCone.ConePoint => z.1) h
    exact Subtype.ext (Subtype.ext h')
  have hs := (summable_cone_pow hr0 hr1).comp_injective hi
  refine hs.congr fun n => ?_
  simp only [Function.comp_apply, i]
  have hd : (LatticeCone.degree ⟨n.1.1, n.2⟩ : ℤ) = degree (n.1 : ℤ × ℤ) := by
    rw [LatticeCone.degree_coe]; rfl
  rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  rw [← hd]
  push_cast
  ring

/-! ### A place `w | v` with `v ≠ 3` -/

section Place

attribute [local instance] Classical.propDecidable

variable {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- The inputs at a place `w | v`, `v ≠ 3`:
the normalized Haar measure, `K_v^max`, `Γ(w/v)`, `ℓ_w`, `q_v`, `H_v(·,-s)` and `1_v^{D₀}`. -/
structure PlaceHyp (μ : Measure G) (K : Subgroup G) (D : DecompositionGroup) (ℓ : G → ℤ × ℤ)
    (q : ℕ) (h : ℂ → ℂ → G → ℂ) (ind : G → ℝ) : Prop where
  isOpen : IsOpen (K : Set G)
  measure_K : μ K = 1
  map_mul : ∀ x y, ℓ (x * y) = ℓ x + ℓ y
  ker : ∀ x, ℓ x = 0 ↔ x ∈ K
  range : Set.range ℓ = (invariantLattice D : Set (ℤ × ℤ))
  one_lt : 1 < q
  height_eq : ∀ s₀ σ x, h s₀ σ x = (q : ℂ) ^ supportFunction s₀ σ (cocharacterEmbedding (ℓ x))
  indicator_eq : ∀ x, ind x = if LatticeCone.InCone (ℓ x) then 1 else 0

variable {μ : Measure G} {K : Subgroup G} {D : DecompositionGroup} {ℓ : G → ℤ × ℤ} {q : ℕ}
  {h : ℂ → ℂ → G → ℂ} {ind : G → ℝ}

/-- `x ↦ H_v(x,-s,D₀)`. -/
def integrand (h : ℂ → ℂ → G → ℂ) (ind : G → ℝ) (s₀ σ : ℂ) (x : G) : ℂ := h s₀ σ x * (ind x : ℂ)

theorem mem_range (H : PlaceHyp μ K D ℓ q h ind) (x : G) : ℓ x ∈ invariantLattice D := by
  rw [← SetLike.mem_coe, ← H.range]
  exact ⟨x, rfl⟩

/-- `ℓ_w : T(ℚ_v) → X_*(T_E)^{Γ(w/v)}`, written multiplicatively. -/
def valuation (H : PlaceHyp μ K D ℓ q h ind) : G →* Multiplicative (invariantLattice D) where
  toFun x := Multiplicative.ofAdd ⟨ℓ x, mem_range H x⟩
  map_one' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    exact Subtype.ext ((H.ker 1).mpr K.one_mem)
  map_mul' x y := by
    rw [← ofAdd_add]
    congr 1
    exact Subtype.ext (H.map_mul x y)

theorem valuation_apply (H : PlaceHyp μ K D ℓ q h ind) (x : G) :
    ((valuation H x).toAdd : ℤ × ℤ) = ℓ x := rfl

theorem valuation_surjective (H : PlaceHyp μ K D ℓ q h ind) :
    Function.Surjective (valuation H) := by
  intro n
  have hn : ((n.toAdd : invariantLattice D) : ℤ × ℤ) ∈ Set.range ℓ := by
    rw [H.range]; exact (n.toAdd).2
  obtain ⟨x, hx⟩ := hn
  refine ⟨x, ?_⟩
  show Multiplicative.ofAdd _ = n
  rw [← ofAdd_toAdd n]
  congr 1
  exact Subtype.ext hx

theorem valuation_ker (H : PlaceHyp μ K D ℓ q h ind) : (valuation H).ker = K := by
  ext x
  rw [MonoidHom.mem_ker, ← H.ker]
  constructor
  · intro hx
    have := congrArg (fun n : Multiplicative (invariantLattice D) => ((n.toAdd : _) : ℤ × ℤ)) hx
    simpa [valuation_apply] using this
  · intro hx
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    exact Subtype.ext hx

/-- Step 2: an unramified character is a character of `X_*(T_E)^{Γ(w/v)}`. -/
theorem exists_unique_descends (H : PlaceHyp μ K D ℓ q h ind) (χ : PontryaginDual G)
    (hχ : ∀ k ∈ K, χ k = 1) : ∃! ψ : Multiplicative (invariantLattice D) →* Circle, Descends D ℓ χ ψ := by
  let V := valuation H
  let e := QuotientGroup.quotientKerEquivOfSurjective V (valuation_surjective H)
  let χ' : G →* Circle := χ.toMonoidHom
  have hle : V.ker ≤ χ'.ker := by
    intro k hk
    rw [valuation_ker H] at hk
    exact hχ k hk
  let ψ := (QuotientGroup.lift V.ker χ' hle).comp e.symm.toMonoidHom
  have hψ : ∀ x, ψ (V x) = χ x := by
    intro x
    have he : e.symm (V x) = (x : G ⧸ V.ker) := (e.symm_apply_eq).mpr rfl
    simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he, QuotientGroup.lift_mk]
    rfl
  refine ⟨ψ, fun x n hn => ?_, fun ψ' hψ' => MonoidHom.ext fun n => ?_⟩
  · have : Multiplicative.ofAdd n = V x := by
      show _ = Multiplicative.ofAdd _
      congr 1
      exact Subtype.ext hn
    rw [this, hψ]
  · obtain ⟨x, hx⟩ := valuation_surjective H n
    have h1 : ((n.toAdd : invariantLattice D) : ℤ × ℤ) = ℓ x := by rw [← hx]; rfl
    have h2 := hψ' x n.toAdd h1
    rw [ofAdd_toAdd] at h2
    rw [← h2, ← hx, hψ]

/-- The terms `q_v^{φ(n)} 1_v^{D₀}(n) χ(n)^{-1}`, `n ∈ N_w`, of `eqn:localfourierassumovern`
(here `e_v = 1`). -/
def latticeTerm (D : DecompositionGroup) (q : ℕ) (s₀ σ : ℂ)
    (ψ : Multiplicative (invariantLattice D) →* Circle) (n : invariantLattice D) : ℂ :=
  (q : ℂ) ^ supportFunction s₀ σ (cocharacterEmbedding n) *
    (((if LatticeCone.InCone (n : ℤ × ℤ) then 1 else 0 : ℝ)) : ℂ) *
      ((ψ (Multiplicative.ofAdd n) : Circle) : ℂ)⁻¹

theorem norm_coneTerm (hq : 0 < q) (s₀ σ : ℂ) (ψ : Multiplicative (invariantLattice D) →* Circle)
    (n : {n : invariantLattice D // LatticeCone.InCone n}) :
    ‖coneTerm D q s₀ σ ψ n‖ = (q : ℝ) ^ (-(σ.re) * (degree (n.1 : ℤ × ℤ) : ℝ)) := by
  rw [coneTerm, supportFunction_cone s₀ σ n.2, norm_mul, norm_inv, Circle.norm_coe, inv_one,
    one_mul, norm_cpow_degree hq]

theorem summable_coneTerm (hq : 1 < q) (s₀ σ : ℂ) (hσ : 0 < σ.re)
    (ψ : Multiplicative (invariantLattice D) →* Circle) :
    Summable (coneTerm D q s₀ σ ψ) :=
  Summable.of_norm_bounded (summable_bound _ hq hσ)
    (fun n => (norm_coneTerm (by omega) s₀ σ ψ n).le)

theorem hasSum_latticeTerm_iff (s₀ σ : ℂ) (ψ : Multiplicative (invariantLattice D) →* Circle)
    (a : ℂ) : HasSum (latticeTerm D q s₀ σ ψ) a ↔ HasSum (coneTerm D q s₀ σ ψ) a := by
  have hsupp : Function.support (latticeTerm D q s₀ σ ψ) ⊆
      {n : invariantLattice D | LatticeCone.InCone (n : ℤ × ℤ)} := by
    intro n hn
    by_contra hc
    apply hn
    simp only [latticeTerm, Set.mem_setOf_eq] at hc ⊢
    rw [if_neg hc]
    simp
  rw [← hasSum_subtype_iff_of_support_subset hsupp]
  have he : (latticeTerm D q s₀ σ ψ ∘ (Subtype.val :
      {n : invariantLattice D | LatticeCone.InCone (n : ℤ × ℤ)} → invariantLattice D)) =
      coneTerm D q s₀ σ ψ := by
    funext n
    simp only [Function.comp_apply, latticeTerm, coneTerm]
    rw [if_pos (show LatticeCone.InCone ((n : invariantLattice D) : ℤ × ℤ) from n.2)]
    push_cast
    ring
  rw [he]
  exact Iff.rfl

/-- Step 3: for unramified `χ = ψ ∘ ℓ_w`, the integral converges absolutely and equals both
lattice sums of `eqn:localfourierassumovern`. Only `Re σ > 0` is needed. -/
theorem hasSum_lattice (H : PlaceHyp μ K D ℓ q h ind) [μ.IsHaarMeasure] (χ : PontryaginDual G)
    (ψ : Multiplicative (invariantLattice D) →* Circle) (hψ : Descends D ℓ χ ψ)
    (s₀ σ : ℂ) (hσ : 0 < σ.re) :
    Integrable (fun x => integrand h ind s₀ σ x * ((χ x : Circle) : ℂ)⁻¹) μ ∧
      HasSum (latticeTerm D q s₀ σ ψ) (characterIntegral μ (integrand h ind s₀ σ) χ) ∧
      HasSum (coneTerm D q s₀ σ ψ) (characterIntegral μ (integrand h ind s₀ σ) χ) := by
  let V := valuation H
  letI : MeasurableSpace (Multiplicative (invariantLattice D)) := ⊤
  haveI : Countable (Multiplicative (invariantLattice D)) :=
    Multiplicative.toAdd.injective.countable
  have hm : Measurable V := measurable_of_countable_ker V
    (by rw [valuation_ker H]; exact H.isOpen.measurableSet)
  have hv := measurePreserving_count_of_ker μ V hm (valuation_surjective H)
    (by rw [valuation_ker H]; exact H.measure_K)
  let g : Multiplicative (invariantLattice D) → ℂ := fun n => latticeTerm D q s₀ σ ψ n.toAdd
  have hL : Summable (latticeTerm D q s₀ σ ψ) :=
    ((hasSum_latticeTerm_iff s₀ σ ψ _).mpr (summable_coneTerm H.one_lt s₀ σ hσ ψ).hasSum).summable
  have hg : Summable g := (Multiplicative.toAdd.summable_iff (f := latticeTerm D q s₀ σ ψ)).mpr hL
  have hf : (fun x => integrand h ind s₀ σ x * ((χ x : Circle) : ℂ)⁻¹) = g ∘ V := by
    funext x
    have hχx : χ x = ψ (V x) := hψ x ⟨ℓ x, mem_range H x⟩ rfl
    simp only [integrand, Function.comp_apply, g, latticeTerm, H.height_eq, H.indicator_eq, hχx]
    rfl
  obtain ⟨hI, hE⟩ := integrable_and_integral_eq_tsum_of_count hv hg
  have hval : characterIntegral μ (integrand h ind s₀ σ) χ = ∑' n, latticeTerm D q s₀ σ ψ n := by
    change (∫ x, integrand h ind s₀ σ x * ((χ x : Circle) : ℂ)⁻¹ ∂μ) = _
    rw [hf]
    change (∫ x, g (V x) ∂μ) = _
    rw [hE]
    exact Multiplicative.toAdd.tsum_eq (latticeTerm D q s₀ σ ψ)
  have hsum : HasSum (latticeTerm D q s₀ σ ψ) (characterIntegral μ (integrand h ind s₀ σ) χ) := by
    rw [hval]; exact hL.hasSum
  exact ⟨hf ▸ hI, hsum, (hasSum_latticeTerm_iff s₀ σ ψ _).mp hsum⟩

/-- Step 1 (Schur's lemma): the integrand is `K_v^max`-invariant, so a ramified character
gives zero. This holds for every `s`. -/
theorem fourier_eq_zero_of_ramified (H : PlaceHyp μ K D ℓ q h ind) [μ.IsHaarMeasure]
    (χ : PontryaginDual G) (hχ : ∃ k ∈ K, χ k ≠ 1) (s₀ σ : ℂ) :
    characterIntegral μ (integrand h ind s₀ σ) χ = 0 := by
  obtain ⟨k, hk, hχk⟩ := hχ
  apply characterIntegral_eq_zero_of_invariant μ _ χ k _ hχk
  intro x
  have hℓ : ℓ (k * x) = ℓ x := by rw [H.map_mul, (H.ker k).mpr hk, zero_add]
  simp only [integrand, H.height_eq, H.indicator_eq, hℓ]

theorem continuous_character_inv (χ : PontryaginDual G) :
    Continuous (fun x => ((χ x : Circle) : ℂ)⁻¹) :=
  (continuous_subtype_val.comp χ.continuous).inv₀ fun _ => Circle.coe_ne_zero _

/-- Absolute convergence for every unitary `χ`, on `Re σ > 0`. -/
theorem integrable (H : PlaceHyp μ K D ℓ q h ind) [μ.IsHaarMeasure] (χ : PontryaginDual G)
    (s₀ σ : ℂ) (hσ : 0 < σ.re) :
    Integrable (fun x => integrand h ind s₀ σ x * ((χ x : Circle) : ℂ)⁻¹) μ := by
  have h1 : Descends D ℓ (1 : PontryaginDual G) (1 : Multiplicative (invariantLattice D) →* Circle) :=
    fun _ _ _ => rfl
  have hI := (hasSum_lattice H 1 1 h1 s₀ σ hσ).1
  have hone : ∀ x : G, ((((1 : PontryaginDual G) x : Circle) : ℂ))⁻¹ = 1 := by
    intro x
    change (((1 : Circle) : ℂ))⁻¹ = 1
    simp
  simp only [hone, mul_one] at hI
  refine hI.norm.mono' (hI.aestronglyMeasurable.mul
    (continuous_character_inv χ).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [norm_mul_character_inv]

/-- The lattice sum as a function of `σ` alone, on the cone. -/
def coneSeries (D : DecompositionGroup) (q : ℕ) (ψ : Multiplicative (invariantLattice D) →* Circle)
    (σ : ℂ) : ℂ :=
  ∑' n : {n : invariantLattice D // LatticeCone.InCone n},
    ((ψ (Multiplicative.ofAdd n.1) : Circle) : ℂ)⁻¹ * (q : ℂ) ^ (-σ * (degree (n.1 : ℤ × ℤ) : ℂ))

theorem tsum_coneTerm (s₀ σ : ℂ) (ψ : Multiplicative (invariantLattice D) →* Circle) :
    ∑' n, coneTerm D q s₀ σ ψ n = coneSeries D q ψ σ := by
  unfold coneSeries
  congr 1
  funext n
  rw [coneTerm, supportFunction_cone s₀ σ n.2]

/-- Locally uniform convergence makes the lattice sum holomorphic on `Re σ > 0`. -/
theorem differentiableOn_coneSeries (hq : 1 < q) (ψ : Multiplicative (invariantLattice D) →* Circle) :
    DifferentiableOn ℂ (coneSeries D q ψ) {σ | 0 < σ.re} := by
  intro σ₀ hσ₀
  have hσ₀' : 0 < σ₀.re := hσ₀
  set a := σ₀.re / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  let U : Set ℂ := {σ | a < σ.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hdiff : DifferentiableOn ℂ (coneSeries D q ψ) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm (summable_bound _ hq ha0) _ hU
    · intro n σ hσ
      have hσ' : a < σ.re := hσ
      rw [norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul,
        norm_cpow_degree (by omega)]
      apply Real.rpow_le_rpow_of_exponent_le hq1
      have hd : (0 : ℝ) ≤ (degree (n.1 : ℤ × ℤ) : ℝ) := by exact_mod_cast degree_nonneg n.2
      nlinarith
    · intro n
      apply Differentiable.differentiableOn
      apply Differentiable.const_mul
      exact (differentiable_id.neg.mul_const _).const_cpow (Or.inl hq0)
  have hmem : σ₀ ∈ U := by
    show a < σ₀.re
    rw [ha]; linarith
  exact (hdiff σ₀ hmem).differentiableAt (hU.mem_nhds hmem) |>.differentiableWithinAt

/-- Holomorphy of `s ↦ Ĥ_v(χ,-s,D₀)` on `{Re σ > 0}`, for every unitary `χ`. -/
theorem differentiableOn_fourier (H : PlaceHyp μ K D ℓ q h ind) [μ.IsHaarMeasure]
    (χ : PontryaginDual G) :
    DifferentiableOn ℂ (fun s : ℂ × ℂ => characterIntegral μ (integrand h ind s.1 s.2) χ)
      {s | 0 < s.2.re} := by
  by_cases hram : ∃ k ∈ K, χ k ≠ 1
  · apply (differentiableOn_const (0 : ℂ)).congr
    intro s _
    exact fourier_eq_zero_of_ramified H χ hram s.1 s.2
  · push_neg at hram
    obtain ⟨ψ, hψ, -⟩ := exists_unique_descends H χ hram
    have hG := (differentiableOn_coneSeries H.one_lt ψ).comp (f := Prod.snd)
      (s := {s : ℂ × ℂ | 0 < s.2.re}) differentiableOn_snd (fun s hs => hs)
    apply hG.congr
    intro s hs
    have h3 := (hasSum_lattice H χ ψ hψ s.1 s.2 hs).2.2
    rw [Function.comp_apply, ← tsum_coneTerm s.1, h3.tsum_eq]

/-- Every conclusion of `prop:heightFourierTransform` at the place `w`. -/
theorem placeConclusions (H : PlaceHyp μ K D ℓ q h ind) [μ.IsHaarMeasure] :
    PlaceConclusions K D ℓ q (fun s₀ σ χ => characterIntegral μ (integrand h ind s₀ σ) χ) where
  ramified χ hχ s₀ σ _ _ := fourier_eq_zero_of_ramified H χ hχ s₀ σ
  descends χ hχ := exists_unique_descends H χ hχ
  formula χ _ ψ hψ s₀ σ _ hσ := (hasSum_lattice H χ ψ hψ s₀ σ hσ).2.2

theorem convergesHolomorphically (H : PlaceHyp μ K D ℓ q h ind) [μ.IsHaarMeasure] :
    ConvergesHolomorphically μ (integrand h ind) :=
  fun χ => ⟨fun s₀ σ hσ => integrable H χ s₀ σ hσ, differentiableOn_fourier H χ⟩

end Place

end Cubic.PoissonSummation.UnramifiedLocalFourier
