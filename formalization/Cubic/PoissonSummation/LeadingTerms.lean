import Cubic.PoissonSummation.LeadingTermsAssembly
import Cubic.PoissonSummation.QuadraticDedekindFactorization
import Cubic.PoissonSummation.Z0Laurent
import CubicTargets.PoissonSummation.LeadingTermsNormalized

/-!
# `prop:leadingTerms`: the pole and both Laurent coefficients

Follow the paper's factorization through the genuine Dedekind zeta function.
The ideal-counting series has its proved Euler product, whose actual split,
inert and ramified factors identify it with `ζ L`. The class-number-formula
residue and the defining Euler–Kronecker limit then identify the constants
in the Laurent expansion of the original height series. The assembly also
supplies both explicit convergent product/sum formulas, with derivatives in `s`.

The only explicit hypothesis is the general Poisson summation input
`PoissonWithDualMeasure.BlackBox`. The arithmetic factorization is proved here,
not assumed.
-/

namespace Cubic.PoissonSummation

theorem leadingTerms_expansion
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.PoissonSummation.LeadingTerms.Claim :=
  LeadingTermsAssembly.claim_of_dedekindFactorization hPoisson
    QuadraticDedekindFactorization.factorization

/-- The same continuation in the current paper's variable `z`, with its explicit
Laurent expansion in `α`, `β` and the Euler–Kronecker constant. -/
theorem «prop:leadingTerms»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.PoissonSummation.LeadingTermsNormalized.Claim := by
  obtain ⟨D, F, μ, c₂, c₁, h⟩ := leadingTerms_expansion hPoisson
  refine ⟨D, fun z => F (2 * z), μ,
    ⟨h.dedekind_agrees, h.dedekind_analytic, h.euler_kronecker⟩, ?_, ?_, ?_, ?_,
    Z0Laurent.«eqn:Z0Laurent» D F μ c₂ c₁ h⟩
  · intro z hz
    exact h.continuation_agrees (2 * z) (by norm_num [Complex.mul_re]; linarith)
  · intro z hz
    change (1 / 2 : ℝ) < z.re at hz
    exact (h.meromorphic (2 * z) (by
      change 1 < (2 * z).re
      norm_num [Complex.mul_re]
      linarith)).comp_analyticAt (by fun_prop)
  · intro z hz hne
    have h2 : 2 * z ≠ 2 := by
      intro he
      apply hne
      linear_combination he / 2
    exact (h.analytic_away_two (2 * z) (by
      norm_num [Complex.mul_re]; linarith) h2).comp (by fun_prop)
  · have hd : deriv (fun z : ℂ => 2 * z) 1 = 2 := by
      simpa using ((hasDerivAt_id (1 : ℂ)).const_mul 2).deriv
    have he := meromorphicOrderAt_comp_of_deriv_ne_zero (f := F)
      (x := (1 : ℂ)) (g := fun z : ℂ => 2 * z) (by fun_prop) (by rw [hd]; norm_num)
    simpa only [Function.comp_def, mul_one, h.pole_order] using he

end Cubic.PoissonSummation
