import Mathlib.Analysis.PSeriesComplex

/-!
# The explicit product appearing in `lemma:finiteFourierProduct`

These definitions describe the right-hand side of `eqn:finiteSpectralProduct`.
They do not define the finite Fourier transform. The target connecting that transform
to this product lives in `CubicTargets.PoissonSummation.FiniteFourierProduct`.
In particular, a `tprod` definition alone asserts no convergence.
-/

noncomputable section

namespace Cubic.PoissonSummation.FiniteEulerProduct

/-- Rational primes split in `ℚ(√-3)`, indexed by the residue class used in the paper. -/
abbrev SplitPrimes := {p : Nat.Primes // (p : ℕ) % 3 = 1}

/-- Rational primes inert in `ℚ(√-3)`, indexed by the residue class used in the paper. -/
abbrev InertPrimes := {p : Nat.Primes // (p : ℕ) % 3 = 2}

/-- The exceptional finite prime. -/
def primeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- The spectral parameter `λ = σ - π i t`. -/
def spectralParameter (σ : ℂ) (t : ℝ) : ℂ := σ - Real.pi * Complex.I * t

@[simp]
theorem spectralParameter_re (σ : ℂ) (t : ℝ) : (spectralParameter σ t).re = σ.re := by
  simp [spectralParameter, Complex.mul_re, Complex.mul_im]

@[simp]
theorem spectralParameter_zero (σ : ℂ) : spectralParameter σ 0 = σ := by
  simp [spectralParameter]

/-- The displayed split Euler factor. -/
def splitFactor (p : SplitPrimes) (z : ℂ) : ℂ :=
  (1 + 2 * (p.1 : ℂ) ^ (-z)) / (1 - (p.1 : ℂ) ^ (-z)) ^ 2

/-- The displayed inert Euler factor. -/
def inertFactor (p : InertPrimes) (z : ℂ) : ℂ :=
  (1 - (p.1 : ℂ) ^ (-(2 * z)))⁻¹

/-- The right-hand side of `eqn:finiteSpectralProduct`, including the factor at 3. -/
def value (z : ℂ) : ℂ :=
  (1 / 6) * (∏' q : InertPrimes, inertFactor q z) *
    (∏' p : SplitPrimes, splitFactor p z)

end Cubic.PoissonSummation.FiniteEulerProduct
