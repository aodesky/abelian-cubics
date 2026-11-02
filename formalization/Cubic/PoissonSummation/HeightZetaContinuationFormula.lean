import Cubic.PoissonSummation.HeightZetaContinuation
import Cubic.PoissonSummation.HeightZetaEulerExtraction

/-!
# Identifying the continuation with the original convergent Euler expression

This is the direct Euler-factor comparison in `lemma:simplifiedZ(s)`,
expressed using `ζ L` before the genuine Dedekind-zeta identification.
Mathlib supplies the genuine Dirichlet L-function and its Euler product.
All products below have proved convergence in `Re z>1`; the resulting expression
continues meromorphically to `Re z>1/2` by `HeightZetaContinuation`.
The remaining equality with the original height series requires Poisson and
the contour argument. No ideal-counting Dedekind-zeta identity is asserted here.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightZetaContinuationFormula

open FiniteEulerProduct HeightZetaFormulaData HeightZetaEulerExtraction
open QuadraticDirichletCharacter

theorem LFunction_product (z : ℂ) (hz : 1 < z.re) :
    DirichletCharacter.LFunction character z =
      (∏' q : InertPrimes, inertCorrection q z) *
        ∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-z))⁻¹ := by
  have hi : HasProd (fun q : InertPrimes => (1 - character (q.1 : ℕ) * (q.1 : ℂ) ^ (-z))⁻¹)
      (∏' q : InertPrimes, inertCorrection q z) := by
    simpa only [character_inert, neg_one_mul, sub_neg_eq_add, inertCorrection] using
      (inert_product_multipliable z hz).hasProd
  have hs : HasProd (fun p : SplitPrimes => (1 - character (p.1 : ℕ) * (p.1 : ℂ) ^ (-z))⁻¹)
      (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-z))⁻¹) := by
    simpa only [character_split, one_mul] using (zeta_split_multipliable z hz).hasProd
  have hp := hasProd_primes_mod_three
    (f := fun p : Nat.Primes => (1 - character (p : ℕ) * (p : ℂ) ^ (-z))⁻¹) hi hs
  have he := hp.unique (DirichletCharacter.LSeries_eulerProduct_hasProd character hz)
  rw [← DirichletCharacter.LFunction_eq_LSeries character hz] at he
  simpa only [primeThree, character_three, zero_mul, sub_zero, inv_one, one_mul] using he.symm

/-- The exceptional prime is removed before squaring the `ζ L` product. -/
theorem zeta_L_without_three (z : ℂ) (hz : 1 < z.re) :
    (1 - (3 : ℂ) ^ (-z)) * riemannZeta z * DirichletCharacter.LFunction character z =
      (∏' q : InertPrimes, inertFactor q z) *
        (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-z))⁻¹) ^ 2 := by
  have hi : (∏' q : InertPrimes, (1 - (q.1 : ℂ) ^ (-z))⁻¹) *
      (∏' q : InertPrimes, inertCorrection q z) = ∏' q : InertPrimes, inertFactor q z := by
    rw [← (zeta_inert_multipliable z hz).tprod_mul (inert_product_multipliable z hz)]
    exact tprod_congr fun q => (inert_factor q z).symm
  rw [← zeta_without_three z hz, LFunction_product z hz, ← hi]
  ring

private theorem inert_cancel (q : InertPrimes) (z : ℂ) (hz : 1 < z.re) :
    inertFactor q z * inertFactor q z * HeightZetaCorrectionProduct.inert q z = inertFactor q z := by
  have h2 : 1 < (2 * z).re := by norm_num [Complex.mul_re]; linarith
  have hn := Complex.one_sub_prime_cpow_ne_zero q.1.2 h2
  unfold inertFactor HeightZetaCorrectionProduct.inert
  field_simp

private theorem split_cancel (p : SplitPrimes) (z : ℂ) (hz : 1 < z.re) :
    (1 - (p.1 : ℂ) ^ (-z))⁻¹ * (1 - (p.1 : ℂ) ^ (-z))⁻¹ *
        (1 - (p.1 : ℂ) ^ (-z))⁻¹ * (1 - (p.1 : ℂ) ^ (-z))⁻¹ *
          HeightZetaCorrectionProduct.split p z = splitFactor p z := by
  have hn := Complex.one_sub_prime_cpow_ne_zero p.1.2 hz
  rw [HeightZetaCorrectionProduct.split_eq_polynomial, splitCorrection_factor]
  unfold splitFactor
  field_simp

private theorem inert_product_cancel (z : ℂ) (hz : 1 < z.re) :
    (∏' q : InertPrimes, inertFactor q z) ^ 2 *
      (∏' q : InertPrimes, HeightZetaCorrectionProduct.inert q z) =
        ∏' q : InertPrimes, inertFactor q z := by
  have hf := (FiniteEulerProduct.convergent_inert z hz).hasProd
  have hc := (HeightZetaCorrectionProduct.convergent_inert z (by linarith)).hasProd
  have hp := ((hf.mul hf).mul hc).congr_fun (fun q => (inert_cancel q z hz).symm)
  simpa only [pow_two] using hp.unique hf

private theorem split_product_cancel (z : ℂ) (hz : 1 < z.re) :
    (∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-z))⁻¹) ^ 4 *
      (∏' p : SplitPrimes, HeightZetaCorrectionProduct.split p z) =
        ∏' p : SplitPrimes, splitFactor p z := by
  have hf := (zeta_split_multipliable z hz).hasProd
  have hc := (HeightZetaCorrectionProduct.convergent_split z (by linarith)).hasProd
  have hp := ((((hf.mul hf).mul hf).mul hf).mul hc).congr_fun
    (fun p => (split_cancel p z hz).symm)
  have he := hp.unique (FiniteEulerProduct.convergent_split z hz).hasProd
  convert he using 1
  ring

/-- The explicit meromorphic function equals the exact displayed Euler expression
throughout its convergence half-plane. This is independent of a height-series formula. -/
theorem continuation_eq_eulerExpression (z : ℂ) (hz : 1 < z.re) :
    HeightZetaContinuation.value z = eulerExpression z := by
  rw [HeightZetaContinuation.value, zeta_L_without_three z hz,
    HeightZetaCorrectionProduct.value, eulerExpression_eq_unscaled_product z hz]
  calc
    _ = ((∏' q : InertPrimes, inertFactor q z) ^ 2 *
          (∏' q : InertPrimes, HeightZetaCorrectionProduct.inert q z)) *
        ((∏' p : SplitPrimes, (1 - (p.1 : ℂ) ^ (-z))⁻¹) ^ 4 *
          (∏' p : SplitPrimes, HeightZetaCorrectionProduct.split p z)) := by ring
    _ = _ := by rw [inert_product_cancel z hz, split_product_cancel z hz]

end Cubic.PoissonSummation.HeightZetaContinuationFormula
