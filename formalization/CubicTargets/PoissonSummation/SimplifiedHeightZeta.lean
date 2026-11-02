import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.PoissonSummation.HeightZetaFormulaData
import Cubic.QuadraticCorrespondence.CyclotomicField
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Analysis.Meromorphic.Basic
import Cubic.PoissonSummation.HeightZetaCorrectionProduct

/-!
# Full concrete target for `lemma:simplifiedZ(s)`

The height zeta function `Z(s)` is the original adelic height series
`AdelicHeightZetaData.heightZeta s₀ σ` at the invariant parameter
`s = (s₀, σ, σ)`, i.e. `s₁ = s₂ = σ` (the paper writes `s₁=s₂=σ` and
`z = s₀/2 + σ = (s₀+s₁+s₂)/2`; this is `HeightZetaFormulaData.parameter`).
The paper's region `Re(s₀+s₁+s₂) > 1` is `Re(s₀+2σ) > 1`, equivalently
`Re z > 1/2`.

`ζ_{ℚ(√-3)}` is mathlib's genuine ideal-counting `NumberField.dedekindZeta` of
`E = CyclotomicField 3 ℚ`, the project's model of `ℚ(√-3)`. Mathlib defines it
by its Dirichlet series, which is meaningful only for `Re z > 1`; so the
displayed formula is asserted with the genuine function on the convergence
region `Re(s₀+2σ) > 2` of the original series (`Re z > 1`), and the continuation
is asserted through a meromorphic function `D` anchored to `dedekindZeta` on
`Re z > 1`. The continuation of `Z` is the displayed right side with `ζ_E`
replaced by `D`; it depends only on `z`, as in the paper, and agrees with the
original series on its whole convergence region.

Both displayed Euler products are asserted to converge absolutely throughout
`Re z > 1/2`, so the formula is meaningful on the whole continuation region
despite Lean's totalized `tprod`.

The target also records the proof's local uniform convergence and holomorphy
of the correction product. These follow directly from summable majorants for
the deviations of its Euler factors from one.
-/

namespace CubicTargets.PoissonSummation.SimplifiedHeightZeta

open Filter Asymptotics
open scoped Topology
open Cubic.PoissonSummation
open AdelicHeightZetaData HeightZetaFormulaData FiniteEulerProduct

/-- The right side of the lemma, with a given function `D` in place of `ζ_{ℚ(√-3)}`. -/
noncomputable def simplified (D : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 - (3 : ℂ) ^ (-z)) ^ 2 * D z ^ 2 *
    (∏' q : InertPrimes, (1 - (q.1 : ℂ) ^ (-(2 * z)))) *
    (∏' p : SplitPrimes,
      (1 - 3 * (p.1 : ℂ) ^ (-(2 * z)) + 2 * (p.1 : ℂ) ^ (-(3 * z))))

structure Claim : Prop where
  /-- The height series defining `Z(s)` converges absolutely on its region. -/
  series_absolute : ∀ s₀ σ : ℂ, 2 < (s₀ + 2 * σ).re →
    Summable (fun P : IntegralRationalPoints => ‖zetaTerm s₀ σ P‖)
  inert_product_absolute : ∀ z : ℂ, (1 / 2 : ℝ) < z.re →
    Summable (fun q : InertPrimes => ‖(1 - (q.1 : ℂ) ^ (-(2 * z))) - 1‖)
  split_product_absolute : ∀ z : ℂ, (1 / 2 : ℝ) < z.re →
    Summable (fun p : SplitPrimes =>
      ‖(1 - 3 * (p.1 : ℂ) ^ (-(2 * z)) + 2 * (p.1 : ℂ) ^ (-(3 * z))) - 1‖)
  inert_product_locally_uniform :
    HasProdLocallyUniformlyOn HeightZetaCorrectionProduct.inert
      (fun z => ∏' q : InertPrimes, HeightZetaCorrectionProduct.inert q z)
      {z : ℂ | (1 / 2 : ℝ) < z.re}
  split_product_locally_uniform :
    HasProdLocallyUniformlyOn HeightZetaCorrectionProduct.split
      (fun z => ∏' p : SplitPrimes, HeightZetaCorrectionProduct.split p z)
      {z : ℂ | (1 / 2 : ℝ) < z.re}
  correction_holomorphic :
    DifferentiableOn ℂ HeightZetaCorrectionProduct.value {z : ℂ | (1 / 2 : ℝ) < z.re}
  /-- The displayed formula with the genuine Dedekind zeta function. -/
  formula : ∀ s₀ σ : ℂ, 2 < (s₀ + 2 * σ).re →
    heightZeta s₀ σ =
      simplified (NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E)
        (parameter s₀ σ)
  /-- Meromorphic continuation to `Re(s₀+s₁+s₂) > 1`, given by the same formula
  with the continuation `D` of the Dedekind zeta function. -/
  meromorphic_continuation : ∃ D : ℂ → ℂ,
    (∀ u : ℂ, 1 < u.re →
      D u = NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E u) ∧
    MeromorphicOn D {u : ℂ | (1 / 2 : ℝ) < u.re} ∧
    MeromorphicOn (simplified D) {z : ℂ | (1 / 2 : ℝ) < z.re} ∧
    ∀ s₀ σ : ℂ, 2 < (s₀ + 2 * σ).re → heightZeta s₀ σ = simplified D (parameter s₀ σ)

end CubicTargets.PoissonSummation.SimplifiedHeightZeta
