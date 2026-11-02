import Cubic.PoissonSummation.HeightCountingSeries
import Cubic.PoissonSummation.HeightCountingEulerProduct
import Cubic.PoissonSummation.HeightZetaFunctionFormula
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Identifying the arithmetic coefficients with actual point counts

The two independently defined coefficient sequences have absolutely
convergent Dirichlet series and agree on a common right half-plane by the
proved height Euler formula. Mathlib's coefficient uniqueness therefore
identifies them. The general Poisson input enters only through the height
Euler formula. In particular neither finiteness nor the height normalization
is a consequence of an assumed counting formula.
-/

namespace Cubic.PoissonSummation.HeightCountingIdentification

open Filter AdelicHeightZetaData HeightCountingData HeightCountingCoefficients

theorem counts_eq_coefficient
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) (n : ℕ) :
    (count n : ℤ) = coefficient n := by
  by_cases hn : n = 0
  · subst n
    simp [HeightCountingSeries.count_zero]
  have hc : LSeries.abscissaOfAbsConv (fun n => (count n : ℂ)) < ⊤ :=
    (HeightCountingSeries.absolute 4 (by norm_num)).abscissaOfAbsConv_le.trans_lt (by simp)
  have ha : LSeries.abscissaOfAbsConv (fun n => (coefficient n : ℂ)) < ⊤ :=
    (series_summable 4 (by norm_num)).abscissaOfAbsConv_le.trans_lt (by simp)
  have he : (fun x : ℝ => LSeries (fun n => (count n : ℂ)) x) =ᶠ[atTop]
      fun x : ℝ => LSeries (fun n => (coefficient n : ℂ)) x := by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hs : 2 < ((2 : ℂ) * x).re := by simp; linarith
    calc
      _ = heightZeta (2 * (x : ℂ)) 0 := by
        simpa using (HeightCountingSeries.heightZeta_eq_LSeries (2 * (x : ℂ)) hs).symm
      _ = HeightZetaFormulaData.eulerExpression x := by
        simpa [HeightZetaFormulaData.parameter] using
          («thm:heightZetaFunctionFormula2» hPoisson).euler_formula (2 * (x : ℂ)) 0
            (by simpa using hs)
      _ = _ := (HeightCountingEulerProduct.euler_product (x : ℂ) (by simp; linarith)).symm
  have h := LSeries.eq_of_LSeries_eventually_eq hc ha he hn
  exact_mod_cast h

theorem point_count
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (n : ℕ) (hn : ¬ 3 ∣ n) : (count n : ℤ) = divisorFormula n := by
  rw [counts_eq_coefficient hPoisson, away_three n hn]

end Cubic.PoissonSummation.HeightCountingIdentification
