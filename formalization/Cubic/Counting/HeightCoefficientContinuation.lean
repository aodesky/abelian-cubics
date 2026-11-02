import Cubic.Counting.HeightCoefficientData
import Cubic.PoissonSummation.LeadingTerms
import Cubic.PoissonSummation.LeadingTermsCorrection
import Cubic.PoissonSummation.HeightCountingSeries
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Convex

/-!
# The continuation of `Z₀(s)` and its Laurent expansion at `s = 1`

The internal `𝒵(s)` is the current paper's `Z₀(s)=(1−3⁻ˢ)²ξ(s)²R(s)`.
The calculation from `prop:leadingTerms` uses the Laurent
expansion `𝒵(s) = A(s-1)^{-2} + B(s-1)^{-1} + O(1)` with `A = c₂/4`, `B = c₁/2`.
It also uses that the Dirichlet coefficients are real, so `𝒵(s̄) = conj 𝒵(s)`.

The identification of the height series with `ξ(s)² LeadingTermsData.correction(2s)` is the content of
`prop:leadingTerms`, which is proved relative to the Poisson summation input `PoissonWithDualMeasure.BlackBox`.
The identification `LSeries_eq` therefore takes a witness
`hE : Expansion D F γ c₂ c₁` of `prop:leadingTerms`, exactly as the paper cites it.

The continuation, differentiability and reflection statements for `calZ` are proved
directly: the identity theorem is applied on the connected set `{Re s > 1/2} \ {1}`.
-/

noncomputable section

namespace Cubic.Counting.HeightCoefficientContinuation

open Cubic.Counting.HeightCoefficientData Cubic.PoissonSummation
  CubicTargets.PoissonSummation.LeadingTerms
open Complex Filter Asymptotics
open scoped Topology

/-! ## The domain `{Re s > 1/2} \ {1}` -/

/-- The punctured half-plane `{Re s > 1/2} \ {1}`. -/
def domain : Set ℂ := {s : ℂ | (1 / 2 : ℝ) < s.re} \ {1}

theorem isOpen_domain : IsOpen domain :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton

/-- The punctured half-plane is the union of four convex pieces, chained by common points. -/
theorem isPreconnected_domain : IsPreconnected domain := by
  set V₁ : Set ℂ := {z | (1 / 2 : ℝ) < z.re} ∩ {z | z.re < 1}
  set V₂ : Set ℂ := {z | (1 / 2 : ℝ) < z.re} ∩ {z | 0 < z.im}
  set V₃ : Set ℂ := {z | (1 / 2 : ℝ) < z.re} ∩ {z | z.im < 0}
  set V₄ : Set ℂ := {z | 1 < z.re}
  have h₁ : IsPreconnected V₁ :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).isPreconnected
  have h₂ : IsPreconnected V₂ :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)).isPreconnected
  have h₃ : IsPreconnected V₃ :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt _)).isPreconnected
  have h₄ : IsPreconnected V₄ := (convex_halfSpace_re_gt _).isPreconnected
  have h₁₂ : IsPreconnected (V₁ ∪ V₂) :=
    h₁.union (⟨3 / 4, 1⟩ : ℂ) (by simp [V₁]; norm_num) (by simp [V₂]; norm_num) h₂
  have h₁₂₃ : IsPreconnected (V₁ ∪ V₂ ∪ V₃) :=
    h₁₂.union (⟨3 / 4, -1⟩ : ℂ) (Or.inl (by simp [V₁]; norm_num)) (by simp [V₃]; norm_num) h₃
  have h₁₂₃₄ : IsPreconnected (V₁ ∪ V₂ ∪ V₃ ∪ V₄) :=
    h₁₂₃.union (⟨2, 1⟩ : ℂ) (Or.inl (Or.inr (by simp [V₂]; norm_num))) (by simp [V₄]) h₄
  convert h₁₂₃₄ using 1
  ext z
  simp only [domain, V₁, V₂, V₃, V₄, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Set.mem_union, Set.mem_inter_iff]
  constructor
  · rintro ⟨hre, hz⟩
    rcases lt_trichotomy z.im 0 with him | him | him
    · exact Or.inl (Or.inr ⟨hre, him⟩)
    · rcases lt_trichotomy z.re 1 with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hre, h⟩))
      · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hz
      · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inr ⟨hre, him⟩))
  · rintro (((⟨hre, h⟩ | ⟨hre, h⟩) | ⟨hre, h⟩) | h)
    · exact ⟨hre, fun he => by simp [he] at h⟩
    · exact ⟨hre, fun he => by simp [he] at h⟩
    · exact ⟨hre, fun he => by simp [he] at h⟩
    · exact ⟨by linarith, fun he => by simp [he] at h⟩

theorem two_mem_domain : (2 : ℂ) ∈ domain := by
  simp only [domain, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  norm_num

/-- Near `2`, points have real part greater than `1`. -/
theorem eventually_one_lt_re_near_two : ∀ᶠ s in 𝓝 (2 : ℂ), 1 < s.re :=
  (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (1 : ℝ) < (2 : ℂ).re by simp)

/-! ## Differentiability -/

theorem zetaE_differentiableAt {s : ℂ} (h1 : s ≠ 1) : DifferentiableAt ℂ zetaE s :=
  (differentiableAt_riemannZeta h1).mul
    (QuadraticDirichletCharacter.differentiable_LFunction s)

theorem zetaE_differentiableOn : DifferentiableOn ℂ zetaE domain :=
  fun _ hs => (zetaE_differentiableAt hs.2).differentiableWithinAt

theorem calZ_differentiableAt {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) (h1 : s ≠ 1) :
    DifferentiableAt ℂ calZ s := by
  have hre : 1 < (2 * s).re := by simp; linarith
  have hc : DifferentiableAt ℂ LeadingTermsData.correction (2 * s) :=
    LeadingTermsCorrection.differentiableOn_correction.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre)
  exact ((zetaE_differentiableAt h1).pow 2).mul
    (hc.comp s ((differentiableAt_id.const_mul 2)))

theorem calZ_differentiableOn : DifferentiableOn ℂ calZ ({s : ℂ | (1 / 2 : ℝ) < s.re} \ {1}) :=
  fun _ hs => (calZ_differentiableAt hs.1 hs.2).differentiableWithinAt

/-! ## Agreement with `prop:leadingTerms` -/

/-- Any continuation in `prop:leadingTerms` agrees with `ζ_E` on `Re s > 1/2`, `s ≠ 1`. -/
theorem dedekind_eq {D F : ℂ → ℂ} {γ c₂ c₁ : ℂ} (hE : Expansion D F γ c₂ c₁)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s ≠ 1) : D s = zetaE s := by
  have hD : AnalyticOnNhd ℂ D domain := fun u hu => hE.dedekind_analytic u hu.1 hu.2
  have hZ : AnalyticOnNhd ℂ zetaE domain := zetaE_differentiableOn.analyticOnNhd isOpen_domain
  have he : D =ᶠ[𝓝 (2 : ℂ)] zetaE := by
    filter_upwards [eventually_one_lt_re_near_two] with u hu
    rw [hE.dedekind_agrees u hu, QuadraticDedekindFactorization.factorization u hu, zetaE]
  exact hD.eqOn_of_preconnected_of_eventuallyEq hZ isPreconnected_domain two_mem_domain he
    ⟨hs, h1⟩

theorem calZ_eq {D F : ℂ → ℂ} {γ c₂ c₁ : ℂ} (hE : Expansion D F γ c₂ c₁)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s ≠ 1) : calZ s = F (2 * s) := by
  have hre : 1 < (2 * s).re := by simp; linarith
  have h2 : 2 * s ≠ 2 := fun he => h1 (by linear_combination he / 2)
  rw [hE.factorization (2 * s) hre h2, mul_div_cancel_left₀ s two_ne_zero,
    dedekind_eq hE s hs h1, calZ]

/-! ## The Dirichlet series -/

theorem d_cast (n : ℕ) : (d n : ℂ) = (HeightCountingData.count n : ℂ) := by
  simp [d]

theorem LSeries_summable (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (fun n => (d n : ℂ)) s := by
  have h := HeightCountingSeries.absolute (2 * s) (by simp; linarith)
  rw [mul_div_cancel_left₀ s two_ne_zero] at h
  simpa only [d_cast] using h

/-- `𝒵(s) = Σ d_n n^{-s}` for `Re s > 1`. The identification of the height series with
`ζ_E² E` is `prop:leadingTerms`, supplied through its witness `hE`. -/
theorem LSeries_eq {D F : ℂ → ℂ} {γ c₂ c₁ : ℂ} (hE : Expansion D F γ c₂ c₁)
    (s : ℂ) (hs : 1 < s.re) : LSeries (fun n => (d n : ℂ)) s = calZ s := by
  have hre : 2 < (2 * s).re := by simp; linarith
  have h := HeightCountingSeries.heightZeta_eq_LSeries (2 * s) hre
  rw [mul_div_cancel_left₀ s two_ne_zero] at h
  have h1 : s ≠ 1 := fun he => by simp [he] at hs
  simp only [d_cast]
  rw [← h, calZ_eq hE s (by linarith) h1, hE.continuation_agrees (2 * s) hre]
  rfl

/-! ## Reflection: the Dirichlet coefficients are real -/

/-- `conj (n^w) = n^(conj w)` for a natural number `n`. -/
theorem conj_natCast_cpow (n : ℕ) (w : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ w) = (n : ℂ) ^ ((starRingEnd ℂ) w) := by
  have hn : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ hn, Complex.conj_natCast]

/-- A Dirichlet series with real coefficients commutes with conjugation. -/
theorem conj_LSeries {f : ℕ → ℂ} (hf : ∀ n, (starRingEnd ℂ) (f n) = f n) (s : ℂ) :
    (starRingEnd ℂ) (LSeries f ((starRingEnd ℂ) s)) = LSeries f s := by
  rw [LSeries, Complex.conj_tsum]
  congr 1
  funext n
  simp only [LSeries.term_def]
  split_ifs
  · simp
  · rw [map_div₀, hf, conj_natCast_cpow, Complex.conj_conj]

theorem conj_character (n : ℕ) :
    (starRingEnd ℂ) (QuadraticDirichletCharacter.character n) =
      QuadraticDirichletCharacter.character n := by
  rw [QuadraticDirichletCharacter.character_of_mod]
  have h := Nat.mod_lt n (show 0 < 3 by norm_num)
  interval_cases (n % 3) <;> simp

theorem conj_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) s)) = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs, ← LSeries_one_eq_riemannZeta (by simpa using hs)]
  exact conj_LSeries (fun n => by simp) s

theorem conj_LFunction {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (DirichletCharacter.LFunction QuadraticDirichletCharacter.character
      ((starRingEnd ℂ) s)) =
      DirichletCharacter.LFunction QuadraticDirichletCharacter.character s := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs,
    DirichletCharacter.LFunction_eq_LSeries _ (by simpa using hs)]
  exact conj_LSeries conj_character s

theorem conj_zetaE {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (zetaE ((starRingEnd ℂ) s)) = zetaE s := by
  rw [zetaE, map_mul, conj_riemannZeta hs, conj_LFunction hs, zetaE]

theorem conj_tprod {ι : Type*} (f : ι → ℂ) :
    (starRingEnd ℂ) (∏' i, f i) = ∏' i, (starRingEnd ℂ) (f i) :=
  Function.LeftInverse.map_tprod f Complex.continuous_conj Complex.continuous_conj
    Complex.conj_conj

theorem conj_value (z : ℂ) :
    (starRingEnd ℂ) (HeightZetaCorrectionProduct.value ((starRingEnd ℂ) z)) =
      HeightZetaCorrectionProduct.value z := by
  simp only [HeightZetaCorrectionProduct.value, HeightZetaCorrectionProduct.inert,
    HeightZetaCorrectionProduct.split, map_mul, conj_tprod, map_sub, map_add, map_one,
    map_ofNat, conj_natCast_cpow, map_neg, Complex.conj_conj]

theorem conj_correction (w : ℂ) :
    (starRingEnd ℂ) (LeadingTermsData.correction ((starRingEnd ℂ) w)) =
      LeadingTermsData.correction w := by
  have hv := conj_value (w / 2)
  simp only [map_div₀, map_ofNat] at hv
  have h3 := conj_natCast_cpow 3 (-((starRingEnd ℂ) w / 2))
  simp only [map_neg, map_div₀, map_ofNat, Complex.conj_conj, Nat.cast_ofNat] at h3
  simp only [LeadingTermsData.correction, map_mul, map_pow, map_sub, map_one, h3, hv]

theorem conj_calZ_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (calZ ((starRingEnd ℂ) s)) = calZ s := by
  have h2 : (2 : ℂ) * (starRingEnd ℂ) s = (starRingEnd ℂ) (2 * s) := by
    rw [map_mul, map_ofNat]
  rw [calZ, h2, map_mul, map_pow, conj_zetaE hs, conj_correction, calZ]

theorem calZ_conj (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s ≠ 1) :
    calZ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (calZ s) := by
  have hmem : ∀ {u : ℂ}, u ∈ domain → (starRingEnd ℂ) u ∈ domain := by
    intro u hu
    refine ⟨by simpa using hu.1, fun he => hu.2 ?_⟩
    simpa using congrArg (starRingEnd ℂ) (Set.mem_singleton_iff.mp he)
  have hg : DifferentiableOn ℂ (fun u => (starRingEnd ℂ) (calZ ((starRingEnd ℂ) u))) domain := by
    intro u hu
    have h := (calZ_differentiableAt (hmem hu).1 (hmem hu).2).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have he : (fun u => (starRingEnd ℂ) (calZ ((starRingEnd ℂ) u))) =ᶠ[𝓝 (2 : ℂ)] calZ := by
    filter_upwards [eventually_one_lt_re_near_two] with u hu
    exact conj_calZ_of_one_lt hu
  have hEq := (hg.analyticOnNhd isOpen_domain).eqOn_of_preconnected_of_eventuallyEq
    (calZ_differentiableOn.analyticOnNhd isOpen_domain) isPreconnected_domain two_mem_domain he
    ⟨hs, h1⟩
  simp only at hEq
  rw [← hEq, Complex.conj_conj]

/-! ## Laurent expansion at `s = 1` -/

theorem calZ_laurent {D F : ℂ → ℂ} {γ c₂ c₁ : ℂ} (hE : Expansion D F γ c₂ c₁) :
    (fun s => calZ s - (c₂ / 4) / (s - 1) ^ 2 - (c₁ / 2) / (s - 1)) =O[𝓝[≠] (1 : ℂ)]
      (fun _ => (1 : ℂ)) := by
  have ht : Tendsto (fun s : ℂ => 2 * s) (𝓝[≠] (1 : ℂ)) (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := ((continuous_mul_left (2 : ℂ)).tendsto (1 : ℂ))
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact fun he => hs (Set.mem_singleton_iff.mpr
        (by linear_combination (Set.mem_singleton_iff.mp he) / 2))
  have h := hE.laurent.comp_tendsto ht
  refine h.congr' ?_ EventuallyEq.rfl
  have hre : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (1 / 2 : ℝ) < s.re :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num))
  filter_upwards [self_mem_nhdsWithin, hre] with s hs1 hs
  have h1 : s ≠ 1 := hs1
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  simp only [Function.comp_apply]
  rw [calZ_eq hE s hs h1]
  have e : 2 * s - 2 = 2 * (s - 1) := by ring
  rw [e]
  field_simp
  ring

end Cubic.Counting.HeightCoefficientContinuation
