import Cubic.ToricHeights.SupportFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Degree and ramification factors in local heights

Keep the ramification index `e`, residue degree `f`, number of places `g`,
and global degree `D` separate. The algebraic hypotheses `e*f*g=D` and
positivity are explicit; this file does not compute arithmetic indices of
number-field places. It checks the local regrouping used in
`eqn:heightforrationaladeles`, before any infinite product is taken.

Complex heights are expressed by dividing the exponent of the positive real
base. Taking a principal complex `D`th root of an already complex height
would introduce branch issues and is not the operation used here.
-/

noncomputable section

namespace Cubic.ToricHeights.LocalDegreeNormalization

/-- The vector `ell_w/e_v`, before multiplication by `log q_v`. -/
def normalizedValuation (e : ℕ) (n : ℝ × ℝ) : ℝ × ℝ :=
  ((e : ℝ)⁻¹ * n.1, (e : ℝ)⁻¹ * n.2)

theorem supportFunction_normalizedValuation (e : ℕ) (s₀ σ : ℂ) (n : ℝ × ℝ) :
    supportFunction s₀ σ (normalizedValuation e n) = supportFunction s₀ σ n / e := by
  rw [normalizedValuation, supportFunction_nonneg_smul s₀ σ n (inv_nonneg.mpr (Nat.cast_nonneg e))]
  push_cast
  ring

/-- The `g` places and their residue degree `f` cancel against the global degree.
The ramification factor survives. -/
theorem degree_cancellation (e f g D : ℕ) (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hD : D = e * f * g) :
    (g : ℝ) * f / D = 1 / (e : ℝ) := by
  subst D
  push_cast
  field_simp

/-- Regroup the `g` equal local height factors with residue cardinality `q^f`.
This is a finite identity, not a rearrangement of the adelic product. -/
theorem grouped_height (q e f g D : ℕ) (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hD : D = e * f * g) (s₀ σ : ℂ) (n : ℝ × ℝ) :
    (((q : ℂ) ^ f) ^ (-supportFunction s₀ σ n / (D : ℂ))) ^ g =
      (q : ℂ) ^ (-supportFunction s₀ σ (normalizedValuation e n)) := by
  rw [← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_mul_nat,
    supportFunction_normalizedValuation]
  congr 1
  subst D
  have he' : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he
  have hf' : (f : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hf
  have hg' : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  push_cast
  field_simp

/-- Divisor negation gives the reciprocal local height, with the same `1/e`.
The Fourier integrand therefore uses `q^(φ/e)`, not `q^(-φ/e)`. -/
theorem negative_parameters_height (q e : ℕ) (s₀ σ : ℂ) (n : ℝ × ℝ) :
    (q : ℂ) ^ (-supportFunction (-s₀) (-σ) (normalizedValuation e n)) =
      ((q : ℂ) ^ (-supportFunction s₀ σ (normalizedValuation e n)))⁻¹ := by
  rw [supportFunction_neg, neg_neg, Complex.cpow_neg, inv_inv]

/-- For the inverse height, normalization and the sign change commute. -/
theorem inverseHeight_exponent (q e : ℕ) (s₀ σ : ℂ) (n : ℝ × ℝ) :
    (q : ℂ) ^ supportFunction s₀ σ (normalizedValuation e n) =
      (q : ℂ) ^ (supportFunction s₀ σ n / e) := by
  rw [supportFunction_normalizedValuation]

/-- At a split place the two conjugates, each weighted by `1/2`, contribute
one height factor. Support values are evaluated before averaging. -/
theorem split_height_product (q : ℕ) (s₀ σ : ℂ) (n : ℝ × ℝ) :
    (q : ℂ) ^ (-supportFunction s₀ σ n / 2) *
      (q : ℂ) ^ (-supportFunction s₀ σ n.swap / 2) =
        (q : ℂ) ^ (-supportFunction s₀ σ n) := by
  rw [supportFunction_swap, ← pow_two]
  simpa [normalizedValuation] using grouped_height q 1 1 2 2 (by decide) (by decide)
    (by decide) (by decide) s₀ σ n

end Cubic.ToricHeights.LocalDegreeNormalization
