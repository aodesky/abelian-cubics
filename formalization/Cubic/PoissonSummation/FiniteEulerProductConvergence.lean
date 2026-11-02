import Cubic.PoissonSummation.FiniteEulerProduct
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Convergence and boundedness of the explicit finite Euler product

These prove the absolute and locally uniform convergence clauses and the closed
half-plane bound of `lemma:finiteFourierProduct`. The identification with local
Fourier integrals is made in the proof of `lemma:finiteFourierProduct`.
-/

noncomputable section

namespace Cubic.PoissonSummation.FiniteEulerProduct

private theorem norm_split_deviation_le (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    ‖(1 + 2 * x) / (1 - x) ^ 2 - 1‖ ≤ 20 * ‖x‖ := by
  have hd : 1 / 2 ≤ ‖1 - x‖ := by
    have := norm_sub_norm_le (1 : ℂ) x
    simp only [norm_one] at this
    linarith
  have hne : 1 - x ≠ 0 := norm_pos_iff.mp (by linarith)
  have heq : (1 + 2 * x) / (1 - x) ^ 2 - 1 = (4 * x - x ^ 2) / (1 - x) ^ 2 := by
    field_simp
    ring
  rw [heq, norm_div, norm_pow]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < ‖1 - x‖))).mpr
  have hn : ‖4 * x - x ^ 2‖ ≤ 4 * ‖x‖ + ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖4 * x‖ + ‖x ^ 2‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_pow]; norm_num
  have hsq : 1 / 4 ≤ ‖1 - x‖ ^ 2 := by nlinarith
  have hx0 := norm_nonneg x
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 20 * ‖x‖)
  nlinarith

private theorem norm_inert_deviation_le (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    ‖(1 - x ^ 2)⁻¹ - 1‖ ≤ 2 * ‖x‖ := by
  have hx0 := norm_nonneg x
  have hsq : ‖x‖ ^ 2 ≤ 1 / 4 := by nlinarith
  have hd : 3 / 4 ≤ ‖1 - x ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (x ^ 2)
    simp only [norm_one, norm_pow] at this
    linarith
  have hne : 1 - x ^ 2 ≠ 0 := norm_pos_iff.mp (by linarith)
  have heq : (1 - x ^ 2)⁻¹ - 1 = x ^ 2 / (1 - x ^ 2) := by field_simp; ring
  rw [heq, norm_div, norm_pow]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 - x ^ 2‖)).mpr
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * ‖x‖)
  nlinarith

/-- The split-factor deviations are bounded by a summable prime power. -/
theorem split_deviation_le (p : SplitPrimes) {z : ℂ} (hz : 1 < z.re) :
    ‖splitFactor p z - 1‖ ≤ 20 * ‖(p.1 : ℂ) ^ (-z)‖ :=
  norm_split_deviation_le _ (Complex.norm_prime_cpow_le_one_half p.1 hz)

/-- The inert-factor deviations satisfy the same type of prime-power bound. -/
theorem inert_deviation_le (p : InertPrimes) {z : ℂ} (hz : 1 < z.re) :
    ‖inertFactor p z - 1‖ ≤ 2 * ‖(p.1 : ℂ) ^ (-z)‖ := by
  have heq : (p.1 : ℂ) ^ (-(2 * z)) = ((p.1 : ℂ) ^ (-z)) ^ 2 := by
    rw [neg_mul_eq_mul_neg, ← Complex.cpow_nat_mul]
    norm_num
  simpa [inertFactor, heq] using
    norm_inert_deviation_le _ (Complex.norm_prime_cpow_le_one_half p.1 hz)

theorem summable_prime_power {z : ℂ} (hz : 1 < z.re) :
    Summable (fun p : Nat.Primes => ‖(p : ℂ) ^ (-z)‖) := by
  have h := (Complex.summable_one_div_nat_cpow.mpr hz).norm.subtype Nat.Prime
  simpa only [one_div, Complex.cpow_neg] using h

/-- The exact absolute-convergence clause for the split-prime product. -/
theorem absolute_split (z : ℂ) (hz : 1 < z.re) :
    Summable (fun p : SplitPrimes => ‖splitFactor p z - 1‖) := by
  exact (((summable_prime_power hz).subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 20).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p => split_deviation_le p hz)

/-- The exact absolute-convergence clause for the inert-prime product. -/
theorem absolute_inert (z : ℂ) (hz : 1 < z.re) :
    Summable (fun p : InertPrimes => ‖inertFactor p z - 1‖) := by
  exact (((summable_prime_power hz).subtype (fun p => (p : ℕ) % 3 = 2)).mul_left 2).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p => inert_deviation_le p hz)

/-- Existence of the split-prime product, independent of totalized `tprod`. -/
theorem convergent_split (z : ℂ) (hz : 1 < z.re) :
    Multipliable (fun p : SplitPrimes => splitFactor p z) := by
  simpa using multipliable_one_add_of_summable (absolute_split z hz)

/-- Existence of the inert-prime product, independent of totalized `tprod`. -/
theorem convergent_inert (z : ℂ) (hz : 1 < z.re) :
    Multipliable (fun p : InertPrimes => inertFactor p z) := by
  simpa using multipliable_one_add_of_summable (absolute_inert z hz)

/-- The prime-power majorant is uniform on a closed right half-plane. -/
theorem prime_power_le {p : Nat.Primes} {z : ℂ} {τ : ℝ} (hz : τ ≤ z.re) :
    ‖(p : ℂ) ^ (-z)‖ ≤ ‖(p : ℂ) ^ (-(τ : ℂ))‖ := by
  apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.prop.pos
  simpa using neg_le_neg hz

private theorem continuous_split (p : SplitPrimes) :
    ContinuousOn (splitFactor p) {z : ℂ | 1 < z.re} := by
  have hc : Continuous (fun z : ℂ => (p.1 : ℂ) ^ (-z)) :=
    continuous_id.neg.const_cpow (.inl (by exact_mod_cast p.1.prop.ne_zero))
  exact (continuous_const.add (continuous_const.mul hc)).continuousOn.div
    ((continuous_const.sub hc).pow 2).continuousOn
    (fun z hz => pow_ne_zero _ (Complex.one_sub_prime_cpow_ne_zero p.1.prop hz))

private theorem continuous_inert (p : InertPrimes) :
    ContinuousOn (inertFactor p) {z : ℂ | 1 < z.re} := by
  have hc : Continuous (fun z : ℂ => (p.1 : ℂ) ^ (-(2 * z))) :=
    (continuous_const.mul continuous_id).neg.const_cpow
      (.inl (by exact_mod_cast p.1.prop.ne_zero))
  apply (continuous_const.sub hc).continuousOn.inv₀
  intro z hz
  apply Complex.one_sub_prime_cpow_ne_zero p.1.prop
  change 1 < (2 * z).re
  change 1 < z.re at hz
  norm_num [Complex.mul_re]
  linarith

theorem locally_uniform_of_majorants (a : ℝ) {ι : Type*} (f : ι → ℂ → ℂ)
    (u : ℝ → ι → ℝ) (hsum : ∀ τ, a < τ → Summable (u τ))
    (hbound : ∀ τ, a < τ → ∀ i z, τ ≤ z.re → ‖f i z - 1‖ ≤ u τ i)
    (hcont : ∀ i, ContinuousOn (f i) {z : ℂ | a < z.re}) :
    HasProdLocallyUniformlyOn f (fun z => ∏' i, f i z) {z : ℂ | a < z.re} := by
  apply hasProdLocallyUniformlyOn_of_forall_compact (isOpen_lt continuous_const Complex.continuous_re)
  intro K hK hcompact
  rcases K.eq_empty_or_nonempty with rfl | hne
  · rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    exact tendstoUniformlyOn_empty
  obtain ⟨z₀, hz₀, hmin⟩ := hcompact.exists_isMinOn hne Complex.continuous_re.continuousOn
  have hτ : a < z₀.re := hK hz₀
  have h := (hsum z₀.re hτ).hasProdUniformlyOn_one_add hcompact
    (f := fun i z => f i z - 1)
    (Filter.Eventually.of_forall (fun i z hz => hbound z₀.re hτ i z (hmin hz)))
    (fun i => ((hcont i).mono hK).sub continuousOn_const)
  simpa only [add_sub_cancel] using h

/-- Local uniform convergence on the full open half-plane, for the exact split factors. -/
theorem locally_uniform_split : HasProdLocallyUniformlyOn splitFactor
    (fun z => ∏' p : SplitPrimes, splitFactor p z) {z : ℂ | 1 < z.re} := by
  apply locally_uniform_of_majorants 1 splitFactor (fun τ p => 20 * ‖(p.1 : ℂ) ^ (-(τ : ℂ))‖)
  · intro τ hτ
    exact ((summable_prime_power hτ).subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 20
  · intro τ hτ p z hz
    exact (split_deviation_le p (hτ.trans_le hz)).trans
      (mul_le_mul_of_nonneg_left (prime_power_le hz) (by norm_num))
  · exact continuous_split

/-- Local uniform convergence on the full open half-plane, for the exact inert factors. -/
theorem locally_uniform_inert : HasProdLocallyUniformlyOn inertFactor
    (fun z => ∏' p : InertPrimes, inertFactor p z) {z : ℂ | 1 < z.re} := by
  apply locally_uniform_of_majorants 1 inertFactor (fun τ p => 2 * ‖(p.1 : ℂ) ^ (-(τ : ℂ))‖)
  · intro τ hτ
    exact ((summable_prime_power hτ).subtype (fun p => (p : ℕ) % 3 = 2)).mul_left 2
  · intro τ hτ p z hz
    exact (inert_deviation_le p (hτ.trans_le hz)).trans
      (mul_le_mul_of_nonneg_left (prime_power_le hz) (by norm_num))
  · exact continuous_inert

/-- Continuity follows from the locally uniform products, and supplies measurability
when the product is integrated along the spectral line. -/
theorem continuousOn_value : ContinuousOn value {z : ℂ | 1 < z.re} := by
  have hs : ContinuousOn (fun z => ∏' p : SplitPrimes, splitFactor p z) {z : ℂ | 1 < z.re} := by
    apply TendstoLocallyUniformlyOn.continuousOn locally_uniform_split
    exact (Filter.Eventually.of_forall
      (fun s => continuousOn_finset_prod s (fun p _ => continuous_split p))).frequently
  have hi : ContinuousOn (fun z => ∏' p : InertPrimes, inertFactor p z) {z : ℂ | 1 < z.re} := by
    apply TendstoLocallyUniformlyOn.continuousOn locally_uniform_inert
    exact (Filter.Eventually.of_forall
      (fun s => continuousOn_finset_prod s (fun p _ => continuous_inert p))).frequently
  exact (continuousOn_const.mul hi).mul hs

theorem continuous_value_spectralParameter (σ : ℂ) (hσ : 1 < σ.re) :
    Continuous (fun t : ℝ => value (spectralParameter σ t)) := by
  apply continuousOn_value.comp_continuous (by unfold spectralParameter; fun_prop)
  intro t
  simpa using hσ

private theorem norm_tprod_le_exp_majorant {ι : Type*} {f : ι → ℂ} {u : ι → ℝ}
    (hf : Multipliable f) (hu : Summable u) (hbound : ∀ i, ‖f i - 1‖ ≤ u i) :
    ‖∏' i, f i‖ ≤ Real.exp (∑' i, u i) := by
  have hu0 : ∀ i, 0 ≤ u i := fun i => (norm_nonneg _).trans (hbound i)
  have hfactor : ∀ i, ‖f i‖ ≤ Real.exp (u i) := by
    intro i
    calc
      ‖f i‖ = ‖(f i - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖f i - 1‖ + 1 := by simpa using norm_add_le (f i - 1) 1
      _ ≤ u i + 1 := by linarith [hbound i]
      _ ≤ Real.exp (u i) := Real.add_one_le_exp _
  apply le_of_tendsto hf.hasProd.norm
  apply Filter.Eventually.of_forall
  intro s
  calc
    ∏ i ∈ s, ‖f i‖ ≤ ∏ i ∈ s, Real.exp (u i) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hfactor i)
    _ = Real.exp (∑ i ∈ s, u i) := (Real.exp_sum s u).symm
    _ ≤ Real.exp (∑' i, u i) := Real.exp_le_exp.mpr (hu.sum_le_tsum s (fun i _ => hu0 i))

/-- A uniform finite bound on every closed half-plane strictly to the right of one. -/
theorem half_plane_bound (τ : ℝ) (hτ : 1 < τ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, τ ≤ z.re → ‖value z‖ ≤ C := by
  let A := ∑' p : SplitPrimes, 20 * ‖(p.1 : ℂ) ^ (-(τ : ℂ))‖
  let B := ∑' p : InertPrimes, 2 * ‖(p.1 : ℂ) ^ (-(τ : ℂ))‖
  refine ⟨(1 / 6) * Real.exp B * Real.exp A, by positivity, ?_⟩
  intro z hz
  have hs : ‖∏' p : SplitPrimes, splitFactor p z‖ ≤ Real.exp A := by
    apply norm_tprod_le_exp_majorant (convergent_split z (hτ.trans_le hz))
      (((summable_prime_power hτ).subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 20)
    intro p
    exact (split_deviation_le p (hτ.trans_le hz)).trans
      (mul_le_mul_of_nonneg_left (prime_power_le hz) (by norm_num))
  have hi : ‖∏' p : InertPrimes, inertFactor p z‖ ≤ Real.exp B := by
    apply norm_tprod_le_exp_majorant (convergent_inert z (hτ.trans_le hz))
      (((summable_prime_power hτ).subtype (fun p => (p : ℕ) % 3 = 2)).mul_left 2)
    intro p
    exact (inert_deviation_le p (hτ.trans_le hz)).trans
      (mul_le_mul_of_nonneg_left (prime_power_le hz) (by norm_num))
  calc
    ‖value z‖ = (1 / 6) * ‖∏' p : InertPrimes, inertFactor p z‖ *
        ‖∏' p : SplitPrimes, splitFactor p z‖ := by simp [value]
    _ ≤ (1 / 6) * Real.exp B * Real.exp A :=
      mul_le_mul (mul_le_mul_of_nonneg_left hi (by norm_num)) hs (norm_nonneg _) (by positivity)

end Cubic.PoissonSummation.FiniteEulerProduct
