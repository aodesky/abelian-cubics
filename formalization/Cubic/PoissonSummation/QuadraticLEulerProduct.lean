import Cubic.PoissonSummation.HeightZetaEulerExtraction
import Cubic.PoissonSummation.QuadraticDirichletCharacter

/-!
# Euler product of the actual quadratic Dirichlet L-function

This is independent of the height continuation, so that the paper's
factorization through `L(2z,χ)` can be used to construct that continuation.
-/

noncomputable section

namespace Cubic.PoissonSummation.QuadraticLEulerProduct

open FiniteEulerProduct HeightZetaFormulaData HeightZetaEulerExtraction
open QuadraticDirichletCharacter

theorem product (z : ℂ) (hz : 1 < z.re) :
    DirichletCharacter.LFunction character z =
      (∏' q : InertPrimes, inertCorrection q z) *
        ∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-z))⁻¹ := by
  have hi : HasProd
      (fun q : InertPrimes => (1 - character (q.1 : ℕ) * (q.1 : ℂ) ^ (-z))⁻¹)
      (∏' q : InertPrimes, inertCorrection q z) := by
    simpa only [character_inert, neg_one_mul, sub_neg_eq_add, inertCorrection] using
      (inert_product_multipliable z hz).hasProd
  have hs : HasProd
      (fun p : SplitPrimes => (1 - character (p.1 : ℕ) * (p.1 : ℂ) ^ (-z))⁻¹)
      (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-z))⁻¹) := by
    simpa only [character_split, one_mul] using (zeta_split_multipliable z hz).hasProd
  have hp := hasProd_primes_mod_three
    (f := fun p : Nat.Primes => (1 - character (p : ℕ) * (p : ℂ) ^ (-z))⁻¹) hi hs
  have he := hp.unique (DirichletCharacter.LSeries_eulerProduct_hasProd character hz)
  rw [← DirichletCharacter.LFunction_eq_LSeries character hz] at he
  simpa only [primeThree, character_three, zero_mul, sub_zero, inv_one, one_mul] using he.symm

end Cubic.PoissonSummation.QuadraticLEulerProduct
