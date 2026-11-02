import Cubic.BoxAsymptotic.AngularIdeals
import Cubic.PoissonSummation.HeightZetaCorrectionProduct
import Cubic.PoissonSummation.QuadraticIdealSplitting

/-! The correction product `R_k` in `eq:Dk`, formed from the actual ideal
characters. Absolute and locally uniform convergence are proved independently
of the still-separate Euler identity with `D_k`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularCorrectionProduct

open Cubic.PoissonSummation Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.AngularIdeals

theorem exists_split_prime (p : SplitPrimes) :
    (Ideal.primesOver (QuadraticIdealSplitting.rationalPrime p.1) Integers).Nonempty := by
  have h : 0 < (Ideal.primesOver (QuadraticIdealSplitting.rationalPrime p.1) Integers).ncard := by
    rw [QuadraticIdealSplitting.split_count p]
    norm_num
  exact (Set.ncard_pos (Set.finite_of_ncard_pos h)).mp h

/-- Choose one of the two genuine prime ideals above a split rational prime.
The displayed correction factor is symmetric in the two character values. -/
def splitPrime (p : SplitPrimes) : Ideal Integers := (exists_split_prime p).choose

theorem splitPrime_mem (p : SplitPrimes) :
    splitPrime p ∈ Ideal.primesOver (QuadraticIdealSplitting.rationalPrime p.1) Integers :=
  (exists_split_prime p).choose_spec

theorem norm_splitPrime (p : SplitPrimes) : Ideal.absNorm (splitPrime p) = (p.1 : ℕ) := by
  letI := (splitPrime_mem p).1
  letI := (splitPrime_mem p).2
  exact QuadraticIdealSplitting.split_norm p (splitPrime p)

def splitPhase (k : ℤ) (p : SplitPrimes) : ℂ := psi k (splitPrime p)

theorem norm_splitPhase (k : ℤ) (p : SplitPrimes) : ‖splitPhase k p‖ = 1 := by
  apply norm_psi
  rw [norm_splitPrime]
  intro h
  have hz := Nat.mod_eq_zero_of_dvd h
  have := p.2
  omega

def quadraticCoefficient (k : ℤ) (p : SplitPrimes) : ℂ :=
  splitPhase k p ^ 2 + 1 + (splitPhase k p)⁻¹ ^ 2

def cubicCoefficient (k : ℤ) (p : SplitPrimes) : ℂ :=
  splitPhase k p + (splitPhase k p)⁻¹

theorem norm_quadraticCoefficient (k : ℤ) (p : SplitPrimes) :
    ‖quadraticCoefficient k p‖ ≤ 3 := by
  calc
    _ ≤ (‖splitPhase k p ^ 2‖ + ‖(1 : ℂ)‖) + ‖(splitPhase k p)⁻¹ ^ 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by norm_num [norm_pow, norm_inv, norm_splitPhase]

theorem norm_cubicCoefficient (k : ℤ) (p : SplitPrimes) :
    ‖cubicCoefficient k p‖ ≤ 2 := by
  calc
    _ ≤ ‖splitPhase k p‖ + ‖(splitPhase k p)⁻¹‖ := norm_add_le _ _
    _ = _ := by norm_num [norm_inv, norm_splitPhase]

def split (k : ℤ) (p : SplitPrimes) (s : ℂ) : ℂ :=
  1 - quadraticCoefficient k p * (p.1 : ℂ) ^ (-(2 * s)) +
    cubicCoefficient k p * (p.1 : ℂ) ^ (-(3 * s))

def value (k : ℤ) (s : ℂ) : ℂ :=
  (∏' q : InertPrimes, HeightZetaCorrectionProduct.inert q s) *
    ∏' p : SplitPrimes, split k p s

theorem split_deviation (k : ℤ) (p : SplitPrimes) (s : ℂ) :
    ‖split k p s - 1‖ ≤ 3 * ‖(p.1 : ℂ) ^ (-(2 * s))‖ +
      2 * ‖(p.1 : ℂ) ^ (-(3 * s))‖ := by
  have he : split k p s - 1 =
      -(quadraticCoefficient k p * (p.1 : ℂ) ^ (-(2 * s))) +
        cubicCoefficient k p * (p.1 : ℂ) ^ (-(3 * s)) := by unfold split; ring
  rw [he]
  calc
    _ ≤ ‖quadraticCoefficient k p‖ * ‖(p.1 : ℂ) ^ (-(2 * s))‖ +
        ‖cubicCoefficient k p‖ * ‖(p.1 : ℂ) ^ (-(3 * s))‖ := by
      simpa only [norm_neg, norm_mul] using norm_add_le
        (-(quadraticCoefficient k p * (p.1 : ℂ) ^ (-(2 * s))))
        (cubicCoefficient k p * (p.1 : ℂ) ^ (-(3 * s)))
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (norm_quadraticCoefficient k p) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (norm_cubicCoefficient k p) (norm_nonneg _))

theorem split_deviation_le (k : ℤ) (p : SplitPrimes) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖split k p s - 1‖ ≤ 5 * ‖(p.1 : ℂ) ^ (-(2 * s))‖ := by
  have h : ‖(p.1 : ℂ) ^ (-(3 * s))‖ ≤ ‖(p.1 : ℂ) ^ (-(2 * s))‖ := by
    apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.1.2.pos
    norm_num [Complex.mul_re]
    linarith
  have := split_deviation k p s
  linarith

theorem absolute_split (k : ℤ) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun p : SplitPrimes => ‖split k p s - 1‖) := by
  have hs2 : 1 < (2 * s).re := by norm_num [Complex.mul_re]; linarith
  apply (((summable_prime_power hs2).subtype
    (fun p => (p : ℕ) % 3 = 1)).mul_left 5).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  exact split_deviation_le k p (by linarith)

theorem convergent_split (k : ℤ) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Multipliable (fun p : SplitPrimes => split k p s) := by
  simpa using multipliable_one_add_of_summable (absolute_split k s hs)

theorem differentiable_split (k : ℤ) (p : SplitPrimes) : Differentiable ℂ (split k p) := by
  have hp : (p.1 : ℂ) ≠ 0 := by exact_mod_cast p.1.2.ne_zero
  have h (n : ℂ) : Differentiable ℂ (fun s : ℂ => (p.1 : ℂ) ^ (-(n * s))) :=
    ((differentiable_const _).mul differentiable_id).neg.const_cpow (.inl hp)
  exact ((differentiable_const _).sub ((differentiable_const _).mul (h 2))).add
    ((differentiable_const _).mul (h 3))

/-- A summable majorant uniform in the angular frequency on each closed
half-plane to the right of one half. -/
theorem uniform_majorant (τ : ℝ) (hτ : (1 / 2 : ℝ) < τ) :
    Summable (fun p : SplitPrimes => 5 * ‖(p.1 : ℂ) ^ (-(2 * (τ : ℂ)))‖) ∧
    ∀ k p s, τ ≤ s.re →
      ‖split k p s - 1‖ ≤ 5 * ‖(p.1 : ℂ) ^ (-(2 * (τ : ℂ)))‖ := by
  constructor
  · have hs2 : 1 < (2 * (τ : ℂ)).re := by norm_num [Complex.mul_re]; linarith
    exact ((summable_prime_power hs2).subtype (fun p => (p : ℕ) % 3 = 1)).mul_left 5
  · intro k p s hs
    apply (split_deviation_le k p (by linarith)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 5)
    apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.1.2.pos
    norm_num [Complex.mul_re]
    linarith

theorem locally_uniform_split (k : ℤ) : HasProdLocallyUniformlyOn (split k)
    (fun s => ∏' p : SplitPrimes, split k p s) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  apply locally_uniform_of_majorants (1 / 2) (split k)
    (fun τ p => 5 * ‖(p.1 : ℂ) ^ (-(2 * (τ : ℂ)))‖)
  · intro τ hτ
    exact (uniform_majorant τ hτ).1
  · intro τ hτ p s hs
    exact (uniform_majorant τ hτ).2 k p s hs
  · intro p
    exact (differentiable_split k p).continuous.continuousOn

theorem differentiableOn_value (k : ℤ) :
    DifferentiableOn ℂ (value k) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  have hi := HeightZetaCorrectionProduct.locally_uniform_inert.differentiableOn
    (Filter.Eventually.of_forall fun S => DifferentiableOn.fun_finset_prod
      fun q _ => (HeightZetaCorrectionProduct.differentiable_inert q).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
  have hs := (locally_uniform_split k).differentiableOn
    (Filter.Eventually.of_forall fun S => DifferentiableOn.fun_finset_prod
      fun p _ => (differentiable_split k p).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
  exact hi.mul hs

end Cubic.BoxAsymptotic.AngularCorrectionProduct
