import Cubic.BoxAsymptotic.AngularCorrectionProduct
import Cubic.PoissonSummation.HeightZetaEulerExtraction
import Cubic.Analysis.ZetaStripGrowth
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-! The uniform correction-product bound in the proof of `lem:moment`.
The quadratic terms are dominated by the cube of the Riemann-zeta Euler
product; the cubic terms give one absolute, frequency-independent constant.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularCorrectionBounds

open Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.BoxAsymptotic.AngularCorrectionProduct

def primePower (p : Nat.Primes) (σ : ℝ) : ℝ := (p : ℝ) ^ (-σ)

theorem primePower_nonneg (p : Nat.Primes) (σ : ℝ) : 0 ≤ primePower p σ :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem primePower_lt_one (p : Nat.Primes) {σ : ℝ} (hσ : 0 < σ) : primePower p σ < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (neg_neg_of_pos hσ)

theorem norm_primePower (p : Nat.Primes) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = primePower p s.re := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
  rfl

theorem primePower_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => primePower p σ) := by
  simpa only [norm_primePower, Complex.ofReal_re] using
    (summable_prime_power (z := (σ : ℂ)) hσ)

theorem norm_zetaFactor (p : Nat.Primes) {σ : ℝ} (hσ : 0 < σ) :
    ‖(1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹‖ = (1 - primePower p σ)⁻¹ := by
  have he : (p : ℂ) ^ (-(σ : ℂ)) = (primePower p σ : ℂ) := by
    simp only [primePower, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg,
      Complex.ofReal_natCast]
  rw [he, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_pos (inv_pos.mpr (sub_pos.mpr (primePower_lt_one p hσ)))

def primeFactor (k : ℤ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  if h : (p : ℕ) % 3 = 1 then split k ⟨p, h⟩ s
  else if h : (p : ℕ) % 3 = 2 then Cubic.PoissonSummation.HeightZetaCorrectionProduct.inert ⟨p, h⟩ s
  else 1

theorem primeFactor_split (k : ℤ) (p : SplitPrimes) (s : ℂ) :
    primeFactor k p.1 s = split k p s := by simp only [primeFactor, p.2, ↓reduceDIte]

theorem primeFactor_inert (k : ℤ) (p : InertPrimes) (s : ℂ) :
    primeFactor k p.1 s = Cubic.PoissonSummation.HeightZetaCorrectionProduct.inert p s := by
  simp [primeFactor, p.2]

theorem value_hasProd (k : ℤ) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    HasProd (fun p => primeFactor k p s) (value k s) := by
  have hi := Cubic.PoissonSummation.HeightZetaCorrectionProduct.convergent_inert s hs
  have ht := Cubic.PoissonSummation.hasProd_primes_mod_three
    (f := fun p => primeFactor k p s)
    (by simpa only [primeFactor_inert] using hi.hasProd)
    (by simpa only [primeFactor_split] using (convergent_split k s hs).hasProd)
  simpa [primeFactor, primeThree, AngularCorrectionProduct.value] using ht

theorem primeFactor_norm_le (k : ℤ) (p : Nat.Primes) {s : ℂ}
    (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖primeFactor k p s‖ ≤ 1 + 3 * primePower p (2 * s.re) + 2 * primePower p (3 / 2) := by
  have htwo : ‖(p : ℂ) ^ (-(2 * s))‖ = primePower p (2 * s.re) := by
    rw [norm_primePower]
    norm_num [Complex.mul_re]
  have hthree : ‖(p : ℂ) ^ (-(3 * s))‖ ≤ primePower p (3 / 2) := by
    have he : ‖(p : ℂ) ^ (-(3 / 2 : ℂ))‖ = primePower p (3 / 2) := by
      rw [norm_primePower]
      norm_num
    rw [← he]
    apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.2.pos
    norm_num [Complex.mul_re]
    linarith
  have hx := primePower_nonneg p (2 * s.re)
  have hr := primePower_nonneg p (3 / 2)
  unfold primeFactor
  split_ifs with h h'
  · have hb := split_deviation k ⟨p, h⟩ s
    have hn := norm_add_le (split k ⟨p, h⟩ s - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at hn
    rw [htwo] at hb
    linarith
  · have hn := norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-(2 * s)))
    rw [norm_one, htwo] at hn
    change ‖1 - (p : ℂ) ^ (-(2 * s))‖ ≤ _
    linarith
  · rw [norm_one]
    linarith

theorem elementary_majorant {x r : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hr : 0 ≤ r) :
    1 + 3 * x + 2 * r ≤ ((1 - x)⁻¹) ^ 3 * Real.exp (2 * r) := by
  have hi : 1 + x ≤ (1 - x)⁻¹ := by
    rw [← one_div, le_div_iff₀ (sub_pos.mpr hx1)]
    nlinarith [sq_nonneg x]
  have hp : 1 + 3 * x ≤ ((1 - x)⁻¹) ^ 3 := by
    calc
      _ ≤ (1 + x) ^ 3 := by nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) hx]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hi 3
  have he : 1 + 2 * r ≤ Real.exp (2 * r) := by simpa [add_comm] using Real.add_one_le_exp (2 * r)
  calc
    _ ≤ (1 + 3 * x) * (1 + 2 * r) := by nlinarith
    _ ≤ _ := mul_le_mul hp he (by positivity)
      (pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hx1.le)) 3)

def absoluteConstant : ℝ := Real.exp (∑' p : Nat.Primes, 2 * primePower p (3 / 2))

theorem absoluteConstant_pos : 0 < absoluteConstant := Real.exp_pos _

theorem value_bound (k : ℤ) {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    ‖value k s‖ ≤ ‖riemannZeta (2 * s.re : ℝ)‖ ^ 3 * absoluteConstant := by
  have hσ : 1 < (2 * s.re : ℝ) := by linarith
  have hz := (riemannZeta_eulerProduct_hasProd (s := ((2 * s.re : ℝ) : ℂ)) hσ).norm.pow 3
  have he := ((primePower_summable (σ := 3 / 2) (by norm_num)).mul_left 2).hasSum.rexp
  have hprod := hz.mul he
  apply le_of_tendsto_of_tendsto (value_hasProd k s hs).norm hprod
  apply Filter.Eventually.of_forall
  intro S
  dsimp only [Function.comp_apply]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro p _hp
  rw [norm_zetaFactor p (by linarith : (0 : ℝ) < 2 * s.re)]
  exact (primeFactor_norm_le k p hs.le).trans
    (elementary_majorant (primePower_nonneg _ _) (primePower_lt_one _ (by linarith))
      (primePower_nonneg _ _))

theorem value_eta_bound (k : ℤ) (t : ℝ) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    ‖value k ((1 / 2 + η : ℝ) + t * Complex.I)‖ ≤ absoluteConstant * η⁻¹ ^ 4 := by
  have hre : (((1 / 2 + η : ℝ) : ℂ) + t * Complex.I).re = 1 / 2 + η := by simp
  have hv := value_bound k (s := ((1 / 2 + η : ℝ) + t * Complex.I)) (by rw [hre]; linarith)
  have he : 2 * (1 / 2 + η) = 1 + 2 * η := by ring
  rw [hre, he] at hv
  have hz := Cubic.Analysis.ZetaStripGrowth.riemannZeta_real_le (1 + 2 * η) (by linarith)
  have hi : 2 ≤ η⁻¹ := by
    rw [← one_div, le_div_iff₀ hη]
    linarith
  have hh : 1 / (1 + 2 * η - 1) = (1 / 2) * η⁻¹ := by field_simp; ring
  rw [hh] at hz
  have hz' : ‖riemannZeta ((1 + 2 * η : ℝ) : ℂ)‖ ≤ η⁻¹ := by linarith
  calc
    _ ≤ ‖riemannZeta ((1 + 2 * η : ℝ) : ℂ)‖ ^ 3 * absoluteConstant := hv
    _ ≤ η⁻¹ ^ 3 * absoluteConstant :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz' 3) absoluteConstant_pos.le
    _ ≤ η⁻¹ ^ 4 * absoluteConstant :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith : 1 ≤ η⁻¹) (by decide : 3 ≤ 4))
        absoluteConstant_pos.le
    _ = _ := mul_comm _ _

end Cubic.BoxAsymptotic.AngularCorrectionBounds
