import Cubic.PoissonSummation.FiniteEulerProductConvergence

/-!
# Domination of the explicit Euler product

This is the comparison at real parameters required by `lemma:finiteFourierProduct`,
for the displayed product. Applying it to the Fourier transform still requires
identifying the actual local integrals with these factors.
-/

noncomputable section

namespace Cubic.PoissonSummation.FiniteEulerProduct

open scoped ComplexOrder

private theorem prime_cpow_re (p : Nat.Primes) (z : ℂ) :
    (p : ℂ) ^ (-(z.re : ℂ)) = (‖(p : ℂ) ^ (-z)‖ : ℂ) := by
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
  simpa using (Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ)) (-z.re)).symm

private theorem split_at_re (p : SplitPrimes) (z : ℂ) :
    splitFactor p (z.re : ℂ) =
      (((1 + 2 * ‖(p.1 : ℂ) ^ (-z)‖) / (1 - ‖(p.1 : ℂ) ^ (-z)‖) ^ 2 : ℝ) : ℂ) := by
  rw [splitFactor, prime_cpow_re]
  push_cast
  rfl

private theorem inert_eq (p : InertPrimes) (z : ℂ) :
    inertFactor p z = (1 - ((p.1 : ℂ) ^ (-z)) ^ 2)⁻¹ := by
  unfold inertFactor
  rw [neg_mul_eq_mul_neg, ← Complex.cpow_nat_mul]
  norm_num

private theorem inert_at_re (p : InertPrimes) (z : ℂ) :
    inertFactor p (z.re : ℂ) =
      (((1 - ‖(p.1 : ℂ) ^ (-z)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [inert_eq, prime_cpow_re]
  push_cast
  rfl

private theorem split_nonneg (p : SplitPrimes) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ splitFactor p (σ : ℂ) := by
  change 0 ≤ splitFactor p (((σ : ℂ).re : ℝ) : ℂ)
  rw [split_at_re]
  have h := Complex.norm_prime_cpow_le_one_half p.1 (s := (σ : ℂ)) hσ
  apply Complex.nonneg_iff.mpr
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨by positivity, trivial⟩

private theorem inert_nonneg (p : InertPrimes) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ inertFactor p (σ : ℂ) := by
  change 0 ≤ inertFactor p (((σ : ℂ).re : ℝ) : ℂ)
  rw [inert_at_re]
  have h := Complex.norm_prime_cpow_le_one_half p.1 (s := (σ : ℂ)) hσ
  have h0 := norm_nonneg ((p.1 : ℂ) ^ (-(σ : ℂ)))
  apply Complex.nonneg_iff.mpr
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨inv_nonneg.mpr (by nlinarith), trivial⟩

private theorem split_norm_le_real (p : SplitPrimes) {z : ℂ} (hz : 1 < z.re) :
    ‖splitFactor p z‖ ≤ ‖splitFactor p (z.re : ℂ)‖ := by
  let x := (p.1 : ℂ) ^ (-z)
  have hx : ‖x‖ ≤ 1 / 2 := Complex.norm_prime_cpow_le_one_half p.1 hz
  have hx0 := norm_nonneg x
  have hd : 1 - ‖x‖ ≤ ‖1 - x‖ := by simpa using norm_sub_norm_le (1 : ℂ) x
  have hnum : ‖1 + 2 * x‖ ≤ 1 + 2 * ‖x‖ := by simpa using norm_add_le (1 : ℂ) (2 * x)
  rw [split_at_re, Complex.norm_of_nonneg (by positivity), splitFactor, norm_div, norm_pow]
  apply div_le_div₀ (by positivity) hnum (sq_pos_of_pos (by linarith : 0 < 1 - ‖x‖))
  nlinarith [norm_nonneg (1 - x)]

private theorem inert_norm_le_real (p : InertPrimes) {z : ℂ} (hz : 1 < z.re) :
    ‖inertFactor p z‖ ≤ ‖inertFactor p (z.re : ℂ)‖ := by
  let x := (p.1 : ℂ) ^ (-z)
  have hx : ‖x‖ ≤ 1 / 2 := Complex.norm_prime_cpow_le_one_half p.1 hz
  have hx0 := norm_nonneg x
  have hd : 1 - ‖x‖ ^ 2 ≤ ‖1 - x ^ 2‖ := by
    calc
      _ = ‖(1 : ℂ)‖ - ‖x ^ 2‖ := by rw [norm_one, norm_pow]
      _ ≤ _ := norm_sub_norm_le _ _
  have hpos : 0 < 1 - ‖x‖ ^ 2 := by nlinarith
  rw [inert_at_re, Complex.norm_of_nonneg (inv_nonneg.mpr hpos.le), inert_eq, norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le hpos hd

private theorem norm_tprod_mono {ι : Type*} {f g : ι → ℂ}
    (hf : Multipliable f) (hg : Multipliable g) (hle : ∀ i, ‖f i‖ ≤ ‖g i‖) :
    ‖∏' i, f i‖ ≤ ‖∏' i, g i‖ := by
  apply le_of_tendsto_of_tendsto' hf.hasProd.norm hg.hasProd.norm
  intro s
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hle i)

private theorem tprod_nonneg {ι : Type*} {f : ι → ℂ}
    (hf : Multipliable f) (h0 : ∀ i, 0 ≤ f i) : 0 ≤ ∏' i, f i := by
  apply ge_of_tendsto hf.hasProd
  exact Filter.Eventually.of_forall (fun s => Finset.prod_nonneg (fun i _ => h0 i))

/-- At real parameters the full product is real and nonnegative. -/
theorem value_nonneg (σ : ℝ) (hσ : 1 < σ) : 0 ≤ value (σ : ℂ) := by
  exact mul_nonneg (mul_nonneg (by norm_num [Complex.nonneg_iff])
    (tprod_nonneg (convergent_inert σ hσ) (fun p => inert_nonneg p hσ)))
    (tprod_nonneg (convergent_split σ hσ) (fun p => split_nonneg p hσ))

/-- Domination by the real-parameter value, for the exact displayed Euler product. -/
theorem norm_value_le_real (z : ℂ) (hz : 1 < z.re) :
    ‖value z‖ ≤ (value (z.re : ℂ)).re := by
  rw [Complex.re_eq_norm.mpr (value_nonneg z.re hz)]
  have hs := norm_tprod_mono (convergent_split z hz) (convergent_split z.re hz)
    (fun p => split_norm_le_real p hz)
  have hi := norm_tprod_mono (convergent_inert z hz) (convergent_inert z.re hz)
    (fun p => inert_norm_le_real p hz)
  simp only [value, norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hi (norm_nonneg _)) hs (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end Cubic.PoissonSummation.FiniteEulerProduct
