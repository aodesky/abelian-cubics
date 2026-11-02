import Cubic.PoissonSummation.HeightCountingIdentification
import Cubic.PoissonSummation.HeightDivisorNormalization
import Cubic.PoissonSummation.IntegralPointComparison
import Cubic.PoissonSummation.LeadingTerms
import CubicTargets.PoissonSummation.HeightZetaCountingFormula

/-!
# `thm:heightZetaFunctionFormula`: the introductory height-zeta and counting formula

The paper first combines the simplified Dedekind-zeta expression and the
leading-terms proposition. The latter's full proved target supplies those
ingredients, including agreement with the genuine ideal-counting zeta.
Its continuation agrees with the independently defined original point sum.

The integral Cartier quotient is computed from the original character lattice
and fan. Its primitive strictly convex generator is the anticanonical class.
`HeightDivisorNormalization` descends the actual height to its complexification
and identifies the paper's scalar coordinate with the `s D₀` height line.
This comparison is an explicit conclusion of the assembled target.
`IntegralPointComparison` also identifies the finite cutoff with integrality
of every original affine invariant polynomial, as required by the introduction.

For the counting assertion, `HeightCountingIdentification` follows the
split/inert/ramified coefficient comparison, with actual height fibers,
proved finiteness and absolute convergence, and Dirichlet-series uniqueness.
The only explicit hypothesis is the approved general Poisson package.
-/

namespace Cubic.PoissonSummation

theorem «thm:heightZetaFunctionFormula»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.PoissonSummation.HeightZetaCountingFormula.Claim := by
  obtain ⟨D, F, γ, c₂, c₁, h⟩ := leadingTerms_expansion hPoisson
  refine {
    integral_point_comparison := IntegralPointComparison.integralPoint_iff
    height_normalization := HeightDivisorNormalization.normalizedHeight_eq
    series_absolute := fun s hs => HeightZetaFullRegion.series_absolute s 0 (by simpa using hs)
    euler_formula := ?_
    inert_product_absolute := h.inert_absolute
    split_product_absolute := h.split_absolute
    continuation := ⟨F, h.continuation_agrees, h.meromorphic, h.analytic_away_two, h.pole_order⟩
    fiber_finite := HeightCountingSeries.fiber_finite
    point_count := fun n _ hn => HeightCountingIdentification.point_count hPoisson n hn
  }
  intro s hs
  have hs1 : 1 < s.re := by linarith
  have hs2 : s ≠ 2 := by intro he; simp [he] at hs
  have hh : 1 < (s / 2).re := by
    norm_num [Complex.div_re]
    linarith
  change LeadingTermsData.heightZeta s = _
  rw [← h.continuation_agrees s hs, h.factorization s hs1 hs2, h.dedekind_agrees _ hh]

end Cubic.PoissonSummation
