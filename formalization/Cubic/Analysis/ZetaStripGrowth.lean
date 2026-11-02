import Cubic.Counting.QuadraticLApproximationIdentification
import Cubic.Counting.HeightCoefficientData
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Polynomial growth of `ζ` and `L(s, χ₋₃)` in the strip `1/4 ≤ Re s ≤ 3`

* For `ζ` we use the first-order Euler–Maclaurin approximants
  `A_m(s) = (s - 1) ∑_{n ≤ m+1} n^{-s} + (m+1)^{1-s}`.
  With `f(y) = y^{1-s}` the increment `A_{m+1}(s) - A_m(s)` equals
  `f(x+1) - f(x) - f'(x+1)` for `x = m + 1`, hence is bounded by
  `|s (s-1)| x^{-Re s - 1}`. The approximants therefore converge locally uniformly on
  `Re s > 0` to an entire-on-`Re s > 0` function which equals `(s-1) ζ(s)` for `Re s > 1`
  (where `(m+1)^{1-s} → 0`), and hence on `Re s > 0` by the identity theorem applied to
  the removable-singularity extension of `(s-1)ζ(s)` across `s = 1`.
* For `L(s, χ₋₃)` we use the existing continuation
  `L(s) = approximation 0 s + ∑ (increments)` on `Re s > -1` and its second-derivative
  increment bound.

In both cases the increment bounds are quadratic in `|s|`, giving `O((1 + |Im s|)^2)`.
We also record the elementary real bounds `ζ(σ) ≤ 1 + 1/(σ-1)` and `0 ≤ L(σ, χ₋₃) ≤ 1`
for `σ > 1`.
-/

noncomputable section

namespace Cubic.Analysis.ZetaStripGrowth

open Filter Set Complex
open scoped Topology
open Cubic.Counting.HeightCoefficientData Cubic.PoissonSummation

/-! ## The Euler–Maclaurin approximants of `(s - 1) ζ(s)` -/

/-- `A_m(s) = (s - 1) ∑_{k < m + 1} (k + 1)^{-s} + (m + 1)^{1 - s}`. -/
def zetaApprox (m : ℕ) (s : ℂ) : ℂ :=
  (s - 1) * (∑ k ∈ Finset.range (m + 1), ((k : ℂ) + 1) ^ (-s)) + ((m : ℂ) + 1) ^ (1 - s)

theorem zetaApprox_zero (s : ℂ) : zetaApprox 0 s = s := by
  simp [zetaApprox]

theorem zetaApprox_differentiable (m : ℕ) : Differentiable ℂ (zetaApprox m) := by
  intro s
  unfold zetaApprox
  have hpow (a : ℂ) (ha : a ≠ 0) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
      DifferentiableAt ℂ (fun s => a ^ g s) s :=
    ((hg s).const_cpow (Or.inl ha))
  refine ((differentiableAt_id.sub_const 1).mul ?_).add ?_
  · refine DifferentiableAt.fun_sum fun k _ => hpow _ ?_ _ differentiable_neg
    exact_mod_cast Nat.succ_ne_zero k
  · refine hpow _ ?_ _ (differentiable_const _ |>.sub differentiable_id)
    exact_mod_cast Nat.succ_ne_zero m

theorem zetaApprox_increment (m : ℕ) (s : ℂ) :
    zetaApprox (m + 1) s - zetaApprox m s =
      ((m : ℂ) + 2) ^ (1 - s) - ((m : ℂ) + 1) ^ (1 - s) + (s - 1) * ((m : ℂ) + 2) ^ (-s) := by
  simp only [zetaApprox, Finset.sum_range_succ (n := m + 1), Nat.cast_add, Nat.cast_one]
  rw [show (m : ℂ) + 1 + 1 = (m : ℂ) + 2 by ring]
  ring

/-- First-order Taylor remainder at the right endpoint of an interval of length one. -/
theorem right_remainder_bound {f f' f'' : ℝ → ℂ} {x M : ℝ}
    (h₁ : ∀ t ∈ Icc x (x + 1), HasDerivAt f (f' t) t)
    (h₂ : ∀ t ∈ Icc x (x + 1), HasDerivAt f' (f'' t) t)
    (hb : ∀ t ∈ Icc x (x + 1), ‖f'' t‖ ≤ M) :
    ‖f (x + 1) - f x - f' (x + 1)‖ ≤ M := by
  let R : ℝ → ℂ := fun t => f t - f x - ((t - x : ℝ) : ℂ) * f' t
  have hR (t : ℝ) (ht : t ∈ Icc x (x + 1)) :
      HasDerivAt R (-(((t - x : ℝ) : ℂ) * f'' t)) t := by
    have hl : HasDerivAt (fun y : ℝ => ((y - x : ℝ) : ℂ)) 1 t := by
      simpa using ((hasDerivAt_id' t).sub_const x).ofReal_comp
    have h := ((h₁ t ht).sub_const (f x)).fun_sub (hl.mul (h₂ t ht))
    convert h using 1
    ring
  have hRb (t : ℝ) (ht : t ∈ Ico x (x + 1)) : ‖-(((t - x : ℝ) : ℂ) * f'' t)‖ ≤ M := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ht.1])]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hb t (Ico_subset_Icc_self ht))
    have := hb t (Ico_subset_Icc_self ht)
    nlinarith [ht.2, norm_nonneg (f'' t)]
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hR t ht).hasDerivWithinAt) hRb (x + 1) (by constructor <;> linarith)
  simp only [R, sub_self, Complex.ofReal_zero, zero_mul, sub_zero,
    show x + 1 - x = 1 by ring, Complex.ofReal_one, one_mul, mul_one] at h
  simpa using h

theorem zetaApprox_increment_bound (m : ℕ) (s : ℂ) (σ B : ℝ) (hσ : 0 ≤ σ)
    (hs : σ ≤ s.re) (hB : ‖s * (s - 1)‖ ≤ B) :
    ‖zetaApprox (m + 1) s - zetaApprox m s‖ ≤ B * ((m : ℝ) + 1) ^ (-σ - 1) := by
  set x : ℝ := (m : ℝ) + 1 with hxdef
  have hx : 1 ≤ x := by simp [x]
  have hx0 : 0 < x := by linarith
  let f : ℝ → ℂ := fun y => (y : ℂ) ^ (1 - s)
  let f' : ℝ → ℂ := fun y => (1 - s) * (y : ℂ) ^ (-s)
  let f'' : ℝ → ℂ := fun y => (1 - s) * (-s * (y : ℂ) ^ (-s - 1))
  have h₁ (t : ℝ) (ht : t ∈ Icc x (x + 1)) : HasDerivAt f (f' t) t := by
    have h := Cubic.Counting.QuadraticLIncrementBound.power_derivative (1 - s) t
      (by linarith [ht.1])
    simpa only [f', show 1 - s - 1 = -s by ring] using h
  have h₂ (t : ℝ) (ht : t ∈ Icc x (x + 1)) : HasDerivAt f' (f'' t) t :=
    (Cubic.Counting.QuadraticLIncrementBound.power_derivative (-s) t
      (by linarith [ht.1])).const_mul (1 - s)
  have hb (t : ℝ) (ht : t ∈ Icc x (x + 1)) : ‖f'' t‖ ≤ B * x ^ (-σ - 1) := by
    have ht0 : 0 < t := by linarith [ht.1]
    have he : f'' t = s * (s - 1) * (t : ℂ) ^ (-s - 1) := by simp only [f'']; ring
    rw [he, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    calc _ ≤ ‖s * (s - 1)‖ * x ^ (-s.re - 1) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact Real.rpow_le_rpow_of_nonpos hx0 ht.1 (by linarith)
      _ ≤ B * x ^ (-σ - 1) := by
          exact mul_le_mul hB (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
            (Real.rpow_nonneg hx0.le _) ((norm_nonneg _).trans hB)
  have h := right_remainder_bound h₁ h₂ hb
  rw [zetaApprox_increment]
  convert h using 1
  simp only [f, f', x]
  push_cast
  rw [show (m : ℂ) + 1 + 1 = (m : ℂ) + 2 by ring]
  ring_nf

theorem zeta_summable_majorant (σ B : ℝ) (hσ : 0 < σ) :
    Summable (fun m : ℕ => B * ((m : ℝ) + 1) ^ (-σ - 1)) := by
  have h := (Real.summable_nat_rpow.mpr (show -σ - 1 < -1 by linarith))
  have ht := (summable_nat_add_iff 1).mpr h
  simpa only [Nat.cast_add, Nat.cast_one] using ht.mul_left B

/-- The locally uniform limit of the approximants. -/
def zetaLimit (s : ℂ) : ℂ :=
  zetaApprox 0 s + ∑' m : ℕ, (zetaApprox (m + 1) s - zetaApprox m s)

theorem zeta_telescoping (N : ℕ) (s : ℂ) : zetaApprox 0 s +
    ∑ n ∈ Finset.range N, (zetaApprox (n + 1) s - zetaApprox n s) = zetaApprox N s := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ← add_assoc, ih]; ring

theorem zeta_locally_uniform : TendstoLocallyUniformlyOn zetaApprox zetaLimit atTop
    {s : ℂ | 0 < s.re} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)]
  intro K hK hcompact
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨s₀, hs₀, hmin⟩ := hcompact.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨s₁, _, hmax⟩ := hcompact.exists_isMaxOn hne
    (show ContinuousOn (fun s : ℂ => ‖s * (s - 1)‖) K by fun_prop)
  have hsum := tendstoUniformlyOn_tsum_nat
    (zeta_summable_majorant s₀.re ‖s₁ * (s₁ - 1)‖ (hK hs₀))
    (fun n s hs => zetaApprox_increment_bound n s s₀.re ‖s₁ * (s₁ - 1)‖
      (hK hs₀).le (hmin hs) (hmax hs))
  have hconst : TendstoUniformlyOn (fun _ : ℕ => zetaApprox 0) (zetaApprox 0) atTop K := by
    exact Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun n s hs => by
      simpa using hε
  have h := hconst.add hsum
  change TendstoUniformlyOn (fun n s => zetaApprox 0 s +
    ∑ k ∈ Finset.range n, (zetaApprox (k + 1) s - zetaApprox k s)) zetaLimit atTop K at h
  simpa only [zeta_telescoping] using h

theorem zetaLimit_differentiableOn : DifferentiableOn ℂ zetaLimit {s : ℂ | 0 < s.re} :=
  zeta_locally_uniform.differentiableOn
    (Eventually.of_forall fun n => (zetaApprox_differentiable n).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem zetaApprox_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun m => zetaApprox m s) atTop (𝓝 ((s - 1) * riemannZeta s)) := by
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hsummable : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h := (Complex.summable_one_div_nat_cpow.mpr hs)
    exact_mod_cast (summable_nat_add_iff 1).mpr h
  have hsum := (hsummable.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  rw [← hz] at hsum
  have htail : Tendsto (fun m : ℕ => ((m : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have h := (tendsto_rpow_neg_atTop (show 0 < s.re - 1 by linarith)).comp ht
    convert h using 1
    ext m
    have he : (m : ℂ) + 1 = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp
  have h := (hsum.const_mul (s - 1)).add htail
  simp only [add_zero] at h
  convert h using 2 with m
  simp only [zetaApprox, Function.comp_apply, Complex.cpow_neg, one_div]

/-- `(s - 1) ζ(s)`, extended by its limit `1` at `s = 1`. -/
def zetaResidueFree : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

theorem zetaResidueFree_differentiable : Differentiable ℂ zetaResidueFree := by
  have hc : ContinuousAt zetaResidueFree 1 := by
    unfold zetaResidueFree
    exact continuousAt_update_same.mpr riemannZeta_residue_one
  have hd : DifferentiableOn ℂ zetaResidueFree (univ \ {1}) := by
    intro z hz
    have hz1 : z ≠ 1 := hz.2
    have he : zetaResidueFree =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
      filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
      simp [zetaResidueFree, Function.update_of_ne hw]
    exact ((((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hz1))).congr_of_eventuallyEq he).differentiableWithinAt
  have h := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (s := univ) (c := (1 : ℂ)) univ_mem).mp ⟨hd, hc⟩
  exact fun z => (h z (mem_univ z)).differentiableAt univ_mem

theorem zetaLimit_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaLimit s = (s - 1) * riemannZeta s := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconvex : Convex ℝ {s : ℂ | 0 < s.re} := convex_halfSpace_gt Complex.reLm.isLinear 0
  have he : zetaLimit =ᶠ[𝓝 (2 : ℂ)] zetaResidueFree := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz1 : z ≠ 1 := by rintro rfl; norm_num at hz
    rw [zetaResidueFree, Function.update_of_ne hz1]
    exact tendsto_nhds_unique (zeta_locally_uniform.tendsto_at (by linarith : 0 < z.re))
      (zetaApprox_tendsto hz)
  have h := (zetaLimit_differentiableOn.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (zetaResidueFree_differentiable.differentiableOn.analyticOnNhd hopen)
    hconvex.isPreconnected (by norm_num : (2 : ℂ) ∈ {s : ℂ | 0 < s.re}) he hs
  rw [h, zetaResidueFree, Function.update_of_ne hs1]

/-! ## Growth in the strip -/

theorem norm_le_of_strip (s : ℂ) (a : ℝ) (ha : 0 ≤ a) (hlo : -a ≤ s.re) (hhi : s.re ≤ a) :
    ‖s‖ ≤ (a + 1) * (1 + |s.im|) := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  have hre : |s.re| ≤ a := abs_le.mpr ⟨hlo, hhi⟩
  nlinarith [abs_nonneg s.im]

/-- The majorant constant `S = ∑_{m ≥ 0} (m + 1)^{-5/4}`. -/
def zetaMajorantSum : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) ^ (-(1 / 4 : ℝ) - 1)

theorem zetaMajorantSum_nonneg : 0 ≤ zetaMajorantSum :=
  tsum_nonneg fun m => Real.rpow_nonneg (by positivity) _

theorem zetaLimit_norm_le {s : ℂ} (hlo : (1 / 4 : ℝ) ≤ s.re) (hhi : s.re ≤ 3) :
    ‖zetaLimit s‖ ≤ (4 + 12 * zetaMajorantSum) * (1 + |s.im|) ^ 2 := by
  set u : ℝ := 1 + |s.im| with hu
  have hu1 : 1 ≤ u := by simp [u]
  have hs : ‖s‖ ≤ 4 * u := by
    have := norm_le_of_strip s 3 (by norm_num) (by linarith) hhi; linarith
  have hs1 : ‖s - 1‖ ≤ 3 * u := by
    have := norm_le_of_strip (s - 1) 2 (by norm_num) (by simp; linarith) (by simp; linarith)
    rw [show (s - 1).im = s.im by simp] at this
    simp only [u]; linarith
  set B : ℝ := 12 * u ^ 2 with hB
  have hBs : ‖s * (s - 1)‖ ≤ B := by
    rw [norm_mul]
    nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
  have hmaj := (zeta_summable_majorant (1 / 4) B (by norm_num)).hasSum
  have htsum : ‖∑' m : ℕ, (zetaApprox (m + 1) s - zetaApprox m s)‖ ≤ B * zetaMajorantSum := by
    rw [zetaMajorantSum, ← tsum_mul_left]
    exact tsum_of_norm_bounded hmaj fun m =>
      zetaApprox_increment_bound m s (1 / 4) B (by norm_num) hlo hBs
  have hS := zetaMajorantSum_nonneg
  unfold zetaLimit
  rw [zetaApprox_zero]
  calc _ ≤ ‖s‖ + ‖∑' m : ℕ, (zetaApprox (m + 1) s - zetaApprox m s)‖ := norm_add_le _ _
    _ ≤ 4 * u + 12 * u ^ 2 * zetaMajorantSum := add_le_add hs htsum
    _ ≤ _ := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u - 1) (by linarith : (0:ℝ) ≤ u)]

theorem riemannZeta_growth : ∃ C : ℝ, ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 3 →
    ‖(s - 1) * riemannZeta s‖ ≤ C * (1 + |s.im|) ^ 2 := by
  refine ⟨4 + 12 * zetaMajorantSum, fun s hlo hhi => ?_⟩
  by_cases hs1 : s = 1
  · subst hs1
    simp only [sub_self, zero_mul, norm_zero]
    have := zetaMajorantSum_nonneg
    positivity
  · rw [← zetaLimit_eq (by linarith) hs1]
    exact zetaLimit_norm_le hlo hhi

/-! ## The quadratic L-function -/

open Cubic.Counting.QuadraticLDerivativeApproximation Cubic.Counting.QuadraticLIncrementBound
  Cubic.Counting.QuadraticLApproximationConvergence
  Cubic.Counting.QuadraticLApproximationIdentification

theorem norm_real_cpow_neg_le_one {s : ℂ} (hs : 0 ≤ s.re) (x : ℝ) (hx : 1 ≤ x) :
    ‖(x : ℂ) ^ (-s)‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hx (by simp; linarith)

theorem approximation_zero_norm_le {s : ℂ} (hs : 0 ≤ s.re) : ‖approximation 0 s‖ ≤ 5 := by
  have hk : ∀ k ∈ Finset.range 2,
      ‖(3 * (k : ℂ) + 1) ^ (-s) - (3 * (k : ℂ) + 2) ^ (-s)‖ ≤ 2 := by
    intro k _
    have e1 : (3 * (k : ℂ) + 1) = ((3 * (k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    have e2 : (3 * (k : ℂ) + 2) = ((3 * (k : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 := norm_real_cpow_neg_le_one hs (3 * (k : ℝ) + 1) (by linarith)
    have h2 := norm_real_cpow_neg_le_one hs (3 * (k : ℝ) + 2) (by linarith)
    exact (norm_sub_le _ _).trans (by linarith)
  have hsum : ‖∑ k ∈ Finset.range 2,
      ((3 * (k : ℂ) + 1) ^ (-s) - (3 * (k : ℂ) + 2) ^ (-s))‖ ≤ 4 := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hk).trans ?_
    norm_num
  have e3 : 3 * (((0 : ℕ) : ℂ) + 1) = ((3 : ℝ) : ℂ) := by push_cast; ring
  have htail : ‖(3 * (((0 : ℕ) : ℂ) + 1)) ^ (-s) / 3‖ ≤ 1 := by
    rw [e3, norm_div, Complex.norm_ofNat]
    have := norm_real_cpow_neg_le_one hs 3 (by norm_num)
    linarith
  unfold approximation
  exact (norm_add_le _ _).trans (by simpa using add_le_add hsum htail |>.trans (by norm_num))

/-- The majorant constant `∑_{n ≥ 0} (n + 1)^{-2}`. -/
def LMajorantSum : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(0 : ℝ) - 2)

theorem LMajorantSum_nonneg : 0 ≤ LMajorantSum :=
  tsum_nonneg fun m => Real.rpow_nonneg (by positivity) _

theorem LFunction_growth : ∃ C : ℝ, ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 3 →
    ‖DirichletCharacter.LFunction QuadraticDirichletCharacter.character s‖ ≤
      C * (1 + |s.im|) ^ 2 := by
  refine ⟨5 + 1500 * LMajorantSum, fun s hlo hhi => ?_⟩
  rw [← limit_eq_L (by linarith)]
  set u : ℝ := 1 + |s.im| with hu
  have hu1 : 1 ≤ u := by simp [u]
  have hs : ‖s‖ ≤ 4 * u := by
    have := norm_le_of_strip s 3 (by norm_num) (by linarith) hhi; linarith
  have hs1 : ‖s + 1‖ ≤ 5 * u := by
    have := norm_le_of_strip (s + 1) 4 (by norm_num) (by simp; linarith) (by simp; linarith)
    rw [show (s + 1).im = s.im by simp] at this
    simp only [u]; linarith
  set B : ℝ := 20 * u ^ 2 with hB
  have hBs : ‖s * (s + 1)‖ ≤ B := by
    rw [norm_mul]
    nlinarith [norm_nonneg s, norm_nonneg (s + 1)]
  have hmaj := (summable_majorant 0 B (by norm_num)).hasSum
  have htsum : ‖∑' n : ℕ, (approximation (n + 1) s - approximation n s)‖ ≤
      75 * B * LMajorantSum := by
    rw [LMajorantSum, ← tsum_mul_left]
    exact tsum_of_norm_bounded hmaj fun n =>
      increment_bound n s 0 B (by norm_num) (by linarith) hBs
  have hS := LMajorantSum_nonneg
  have h0 := approximation_zero_norm_le (s := s) (by linarith)
  unfold limit
  calc _ ≤ ‖approximation 0 s‖ + ‖∑' n : ℕ, (approximation (n + 1) s - approximation n s)‖ :=
        norm_add_le _ _
    _ ≤ 5 + 75 * (20 * u ^ 2) * LMajorantSum := add_le_add h0 htsum
    _ ≤ _ := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u - 1) (by linarith : (0:ℝ) ≤ u)]

theorem zetaE_growth : ∃ C : ℝ, ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 3 →
    ‖(s - 1) * zetaE s‖ ≤ C * (1 + |s.im|) ^ 4 := by
  obtain ⟨C₁, h₁⟩ := riemannZeta_growth
  obtain ⟨C₂, h₂⟩ := LFunction_growth
  have hC₁ : 0 ≤ C₁ := by
    have := h₁ 2 (by norm_num) (by norm_num)
    simpa using (norm_nonneg _).trans this
  refine ⟨C₁ * C₂, fun s hlo hhi => ?_⟩
  rw [zetaE, ← mul_assoc, norm_mul]
  have hA := h₁ s hlo hhi
  have hL := h₂ s hlo hhi
  calc _ ≤ (C₁ * (1 + |s.im|) ^ 2) * (C₂ * (1 + |s.im|) ^ 2) :=
        mul_le_mul hA hL (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-! ## Bounds on the real axis to the right of `1` -/

theorem riemannZeta_real_le (σ : ℝ) (hσ : 1 < σ) : ‖riemannZeta σ‖ ≤ 1 + 1 / (σ - 1) := by
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow (s := (σ : ℂ)) (by simpa using hσ)
  have hterm : ∀ n : ℕ, 1 / ((n : ℂ) + 1) ^ (σ : ℂ) = ((1 / ((n : ℝ) + 1) ^ σ : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [hz]
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun n => by positivity)]
  have h := ZetaAsymptotics.zeta_limit_aux1 hσ
  have ht : 0 ≤ ZetaAsymptotics.term_tsum σ :=
    tsum_nonneg fun n => ZetaAsymptotics.term_nonneg _ _
  nlinarith

theorem LFunction_real_le (σ : ℝ) (hσ : 1 < σ) :
    ‖DirichletCharacter.LFunction QuadraticDirichletCharacter.character σ‖ ≤ 1 := by
  have h := paired_hasSum (s := (σ : ℂ)) (by simpa using hσ)
  let a : ℕ → ℝ := fun k => (3 * (k : ℝ) + 1) ^ (-σ) - (3 * (k : ℝ) + 2) ^ (-σ)
  have hterm : ∀ k : ℕ, (3 * (k : ℂ) + 1) ^ (-(σ : ℂ)) - (3 * (k : ℂ) + 2) ^ (-(σ : ℂ)) =
      (a k : ℂ) := by
    intro k
    simp only [a, Complex.ofReal_sub]
    rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  simp_rw [hterm] at h
  have hσ0 : -σ ≤ 0 := by linarith
  have ha : ∀ k, 0 ≤ a k := fun k => sub_nonneg.mpr
    (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hσ0)
  have hstep : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), a k ≤ 1 - (3 * (N : ℝ) + 2) ^ (-σ) := by
    intro N
    induction N with
    | zero => simp [a]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have e1 : 3 * ((N + 1 : ℕ) : ℝ) + 1 = 3 * (N : ℝ) + 4 := by push_cast; ring
      have e2 : 3 * ((N + 1 : ℕ) : ℝ) + 2 = 3 * (N : ℝ) + 5 := by push_cast; ring
      simp only [a, e1, e2]
      have hle : (3 * (N : ℝ) + 4) ^ (-σ) ≤ (3 * (N : ℝ) + 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hσ0
      simp only [a] at ih
      linarith
  have hP : ∀ N : ℕ, |∑ k ∈ Finset.range N, a k| ≤ 1 := by
    intro N
    rw [abs_of_nonneg (Finset.sum_nonneg fun k _ => ha k)]
    cases N with
    | zero => simp
    | succ N =>
      have := hstep N
      have : 0 ≤ (3 * (N : ℝ) + 2) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      linarith
  refine le_of_tendsto' h.tendsto_sum_nat.norm fun N => ?_
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  exact hP N

end Cubic.Analysis.ZetaStripGrowth
