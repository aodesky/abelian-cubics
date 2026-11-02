import Cubic.OrbitParametrization.SplitAutomorphisms
import Cubic.Counting.Normality

/-!
# Normality from real conjugates (`lemma:cubicimpliesnormal`, core step)

The paper's proof: the roots are real; the three real embeddings identify
`ℚ(x) ⊗ ℝ` with `ℝ³`, the columns being the images of `x, σx, σ²x`, so `x` is normal
iff the circulant determinant is nonzero; it is `-(x+y+z)/2 · Σ(x-y)²`, nonzero
since the trace is nonzero and the roots are distinct.

Here: a `ℚ`-relation `Σ cᵢ σⁱx = 0`, conjugated by `σʰ` and mapped to `ℝ`, says that
`Σ cᵢ · rowᵢ = 0` for the rows of the real circulant matrix of `(x, σx, σ²x)`.
After scaling to trace one, `Normality.linearIndependent_conjugates_of_trace_one`
gives `c = 0`.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open Cubic.Counting

/-- A `C₃`-algebra element with real, distinct conjugates and nonzero trace is normal. -/
theorem normal_of_real (K : C3Alg) (ι : K.carrier →+* ℝ) (x : K.carrier)
    (htr : ι (traceSum K x) ≠ 0) (hne : ι x ≠ ι (K.act σ x)) : IsNormal K x := by
  rw [IsNormal, Fintype.linearIndependent_iff]
  intro c hc
  rw [sum_C3, show (Multiplicative.ofAdd (2 : ZMod 3)) = σ ^ 2 by decide, map_one] at hc
  have hR : algebraMap ℚ K.carrier (c 1) * x + algebraMap ℚ K.carrier (c σ) * K.act σ x +
      algebraMap ℚ K.carrier (c (σ ^ 2)) * K.act (σ ^ 2) x = 0 := by
    simpa [Algebra.smul_def] using hc
  have hR1 := congrArg (K.act σ) hR
  have hR2 := congrArg (K.act (σ ^ 2)) hR
  simp only [map_add, map_mul, AlgEquiv.commutes, map_zero, act_σ_σ, act_σ_σ2, act_σ2_σ,
    act_σ2_σ2] at hR1 hR2
  -- real values of the three conjugates, scaled to trace one
  set a := ι x
  set b := ι (K.act σ x)
  set d := ι (K.act (σ ^ 2) x)
  have hs : a + b + d ≠ 0 := by
    rw [traceSum_eq, map_add, map_add] at htr
    exact htr
  set s := a + b + d
  have hq : ∀ q : ℚ, ι (algebraMap ℚ K.carrier q) = (q : ℝ) := fun q => by
    rw [← RingHom.comp_apply, eq_ratCast]
  have e0 := congrArg ι hR
  have e1 := congrArg ι hR1
  have e2 := congrArg ι hR2
  simp only [map_add, map_mul, map_zero, hq] at e0 e1 e2
  have hli := linearIndependent_conjugates_of_trace_one (a / s) (b / s) (d / s)
    (by rw [← add_div, ← add_div, div_self hs]) (by
      intro h
      apply hne
      have := congrArg (· * s) h
      simpa [div_mul_cancel₀ _ hs] using this)
  rw [Fintype.linearIndependent_iff] at hli
  have hsum : ∑ i : Fin 3, (fun k : Fin 3 => ![(c 1 : ℝ), (c σ : ℝ), (c (σ ^ 2) : ℝ)] k) i •
      conjugates (a / s) (b / s) (d / s) i = 0 := by
    ext j
    fin_cases j <;>
    simp [Fin.sum_univ_three, conjugates, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    field_simp <;>
    linarith
  have hc0 := hli _ hsum
  intro g
  have hg : g = 1 ∨ g = σ ∨ g = σ ^ 2 := by revert g; decide
  rcases hg with rfl | rfl | rfl
  · exact_mod_cast (by simpa using hc0 0 : (c 1 : ℝ) = 0)
  · exact_mod_cast (by simpa using hc0 1 : (c σ : ℝ) = 0)
  · exact_mod_cast (by simpa using hc0 2 : (c (σ ^ 2) : ℝ) = 0)

end Cubic.OrbitParametrization.C3Algebra
