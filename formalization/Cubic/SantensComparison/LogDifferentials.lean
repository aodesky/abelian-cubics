import Cubic.SantensComparison.SantensLocalHeight
import Cubic.QuadraticCorrespondence.CyclotomicRamifiedIntegers
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Coefficients of the actual logarithmic character differentials. The
determinant is their wedge in the coordinate basis, not a stipulated volume.
The real residue measure is defined by pushing forward `dφ` along the circle
parameter; its total mass is computed separately. -/

noncomputable section

namespace Cubic.SantensComparison.LogDifferentials

open MvPolynomial MeasureTheory

section Quadratic

variable {k : Type*} [Field k]

def characterPolynomial (z : k) : MvPolynomial (Fin 2) k := X 0 + C z * X 1

def logJacobian (z z' : k) (x : Fin 2 → k) : Matrix (Fin 2) (Fin 2) k :=
  fun i j =>
    eval x (pderiv j (characterPolynomial (![z,z'] i))) /
      eval x (characterPolynomial (![z,z'] i))

theorem character_value (z : k) (x : Fin 2 → k) :
    eval x (characterPolynomial z) = x 0 + z * x 1 := by
  simp [characterPolynomial]

theorem character_derivative (z : k) :
    (fun j => pderiv j (characterPolynomial z)) = ![1,C z] := by
  ext j
  fin_cases j <;> simp [characterPolynomial]

theorem log_wedge (z z' : k) (x : Fin 2 → k) :
    Matrix.det (logJacobian z z' x) =
      (z'-z) / ((x 0 + z*x 1)*(x 0 + z'*x 1)) := by
  simp [logJacobian, Matrix.det_fin_two, characterPolynomial, div_eq_mul_inv]
  ring

theorem cyclotomic_log_wedge (z : k) (hz : z^2+z+1=0) (x : Fin 2 → k) :
    Matrix.det (logJacobian z (-1-z) x) =
      -(2*z+1) / (x 0^2-x 0*x 1+x 1^2) := by
  rw [log_wedge z (-1-z) x]
  have hn : (x 0+z*x 1)*(x 0+(-1-z)*x 1)=x 0^2-x 0*x 1+x 1^2 := by
    linear_combination -(x 1)^2 * hz
  rw [hn]
  congr 1
  ring

end Quadratic

theorem ramified_differential_norm :
    ‖2*Cubic.QuadraticCorrespondence.CyclotomicRamifiedField.zeta+1‖ =
      1 / Real.sqrt 3 := by
  have h := Cubic.QuadraticCorrespondence.CyclotomicRamifiedField.norm_root_difference_sq
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  apply (mul_left_inj' hp.ne').mp
  have hn := norm_nonneg (2*Cubic.QuadraticCorrespondence.CyclotomicRamifiedField.zeta+1)
  field_simp
  nlinarith [mul_nonneg hn hp.le]

theorem complex_log_wedge (x y : ℝ) :
    Matrix.det (logJacobian Complex.I (-Complex.I) ![(x:ℂ),(y:ℂ)]) =
      -2*Complex.I / ((x:ℂ)^2+(y:ℂ)^2) := by
  rw [log_wedge]
  have hn : ((x:ℂ)+Complex.I*y)*((x:ℂ)-Complex.I*y)=(x:ℂ)^2+(y:ℂ)^2 := by
    ring_nf
    simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul, ← sub_eq_add_neg]
  rw [hn]
  congr 1
  ring

/-- The boundary coordinates `u=ν⁻¹`, `w=ν/ν̄` are a unimodular monomial
change: `du/u ∧ dw/w = dν/ν ∧ dν̄/ν̄`. -/
theorem boundary_log_basis :
    Matrix.det (!![-1,0;1,-1] : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  norm_num [Matrix.det_fin_two]

/-- Fixed boundary points satisfy conjugate(w)=w⁻¹; this is precisely the
unit circle, including its point w=1. -/
theorem boundary_real_locus (w : ℂˣ) :
    star (w : ℂ) = (w : ℂ)⁻¹ ↔ ‖(w : ℂ)‖ = 1 := by
  rw [← mul_eq_one_iff_eq_inv₀ w.ne_zero]
  change (starRingEnd ℂ) (w:ℂ) * (w:ℂ) = 1 ↔ _
  rw [Complex.conj_mul']
  constructor
  · intro h
    have hh : ‖(w:ℂ)‖^2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg (w : ℂ)]
  · intro h
    rw [h]
    norm_num

scoped instance : MeasurableSpace Circle := borel Circle
scoped instance : BorelSpace Circle := ⟨rfl⟩

theorem boundary_parameter_derivative (φ : ℝ) :
    HasDerivAt (fun t : ℝ => (Circle.exp t : ℂ))
      ((Circle.exp φ : ℂ)*Complex.I) φ := by
  have h : HasDerivAt (fun t : ℝ => (t:ℂ)*Complex.I) Complex.I φ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := φ)).mul_const Complex.I
  exact h.cexp

/-- Multiplying the logarithmic residue by i makes it real; its coefficient
in the angular coordinate is −1, hence its absolute density is one. -/
theorem boundary_residue_density (φ : ℝ) :
    ‖Complex.I * deriv (fun t : ℝ => (Circle.exp t : ℂ)) φ / (Circle.exp φ : ℂ)‖ = 1 := by
  rw [(boundary_parameter_derivative φ).deriv]
  have h : (Circle.exp φ : ℂ) ≠ 0 := by rw [Circle.coe_exp]; exact Complex.exp_ne_zero _
  have he : Complex.I * ((Circle.exp φ : ℂ)*Complex.I) / (Circle.exp φ : ℂ) = -1 := by
    field_simp
    exact Complex.I_sq
  rw [he, norm_neg, norm_one]

def boundaryResidueMeasure : Measure Circle :=
  Measure.map Circle.exp (volume.restrict (Set.Ioc 0 (2*Real.pi)))

theorem boundary_residue_mass : boundaryResidueMeasure.real Set.univ = 2*Real.pi := by
  rw [boundaryResidueMeasure, Measure.real, Measure.map_apply Circle.exp.continuous.measurable
    MeasurableSet.univ]
  simp [Measure.restrict_apply, Real.volume_Ioc, Real.pi_nonneg]

end Cubic.SantensComparison.LogDifferentials
