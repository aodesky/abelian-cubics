import Cubic.SurfaceGeometry.RationalDiagonalization
import Cubic.ToricHeights.HeightFormula

noncomputable section

namespace Cubic.SurfaceGeometry.DiagonalCubicGeneration

open MvPolynomial DiagonalCubicData
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.ToricHeights

theorem monomial_normalForm (d : Fin 3 →₀ ℕ) (r : E)
    (h01 : d 0 % 3 = d 1 % 3) (h12 : d 1 % 3 = d 2 % 3) :
    monomial d r = C r * ((X 0^3)^(d 0/3) * (X 1^3)^(d 1/3) *
      (X 2^3)^(d 2/3) * (X 0*X 1*X 2)^(d 0%3)) := by
  simp only [mul_pow,X_pow_eq_monomial,monomial_pow,monomial_mul,one_pow,
    mul_one,C_mul_monomial]
  apply congrArg (fun e : Fin 3 →₀ ℕ => monomial e r)
  ext i
  fin_cases i <;> simp <;> omega

theorem exponents_congruent {p : CubicTargets.ToricHeights.HeightFormula.Poly} {n : ℕ}
    (hp : p.IsHomogeneous (3*n))
    (hinv : HeightFormula.diagShift p = p) (d : ZMod 3 →₀ ℕ) (hd : coeff d p ≠ 0) :
    d 0%3=d 1%3 ∧ d 1%3=d 2%3 := by
  have hdeg : d 0+d 1+d 2=3*n := by
    by_contra h
    exact hd (hp.coeff_eq_zero (by rw [← HeightFormula.mono_self d,HeightFormula.mono_degree]; exact h))
  have h := HeightFormula.coeff_diagShift p (d 0) (d 1) (d 2)
  rw [HeightFormula.mono_self,hinv] at h
  have hpow : zeta^(2*d 1+d 2)=1 :=
    mul_right_cancel₀ hd (h.symm.trans (one_mul _).symm)
  exact (RationalDiagonalization.invariant_exponents _ _ _).mp
    ⟨⟨n,hdeg⟩,(zeta_primitive.pow_eq_one_iff_dvd _).mp hpow⟩

theorem monomial_mem_range (d : Fin 3 →₀ ℕ) (r : E)
    (h01 : d 0%3=d 1%3) (h12 : d 1%3=d 2%3) :
    monomial d r ∈ substitution.range := by
  refine ⟨C r * (X 1^(d 0/3) * X 2^(d 1/3) * X 3^(d 2/3) * X 0^(d 0%3)),?_⟩
  change substitution _ = _
  rw [monomial_normalForm d r h01 h12]
  simp only [map_mul,map_pow,substitution,aeval_X,aeval_C,algebraMap_eq,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons]

theorem homogeneous_generation {p : CubicTargets.ToricHeights.HeightFormula.Poly} {n : ℕ}
    (hp : p.IsHomogeneous (3*n))
    (hinv : HeightFormula.diagShift p=p) : p ∈ substitution.range := by
  rw [← support_sum_monomial_coeff p]
  apply Subalgebra.sum_mem
  intro d hd
  have hc := exponents_congruent hp hinv d (mem_support_iff.mp hd)
  exact monomial_mem_range d (coeff d p) hc.1 hc.2

/-- Every original invariant of degree 3n is a polynomial in the four
diagonal cubics after the paper's invertible linear substitution. -/
theorem original_homogeneous_generation {p : CubicTargets.ToricHeights.HeightFormula.Poly} {n : ℕ}
    (hp : p.IsHomogeneous (3*n))
    (hinv : CubicTargets.ToricHeights.HeightFormula.cyclicShift p=p) :
    ∃ q : FourVariables, HeightFormula.toEigen (substitution q)=p := by
  have hd : HeightFormula.diagShift (HeightFormula.fromEigen p) = HeightFormula.fromEigen p := by
    have h := DFunLike.congr_fun HeightFormula.cyclicShift_toEigen (HeightFormula.fromEigen p)
    simp only [AlgHom.comp_apply,HeightFormula.toEigen_fromEigen_apply,hinv] at h
    have he := congrArg HeightFormula.fromEigen h
    rw [HeightFormula.fromEigen_toEigen_apply] at he
    exact he.symm
  obtain ⟨q,hq⟩ := homogeneous_generation (HeightFormula.fromEigen_homogeneous hp) hd
  change substitution q = HeightFormula.fromEigen p at hq
  exact ⟨q,by rw [hq,HeightFormula.toEigen_fromEigen_apply]⟩

end Cubic.SurfaceGeometry.DiagonalCubicGeneration
