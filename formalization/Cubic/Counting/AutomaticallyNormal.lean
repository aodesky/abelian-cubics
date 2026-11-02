import CubicTargets.Counting.AutomaticallyNormal
import Cubic.Counting.CubicImpliesNormalProof
import Cubic.Counting.CyclicCubicField
import Cubic.Counting.Normality
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Proof of `cor:automaticallyNormal`

The paper's proof: "Apply the preceding two lemmas, noting that the rational roots of a
monic integral polynomial are integers."

* Galois group `C₃`: `f = t³−t²+at+b` is irreducible over `ℚ`
  (`CyclicCubicField.irreducible_of_cyclic`) and has `t²`-coefficient `−1`, so
  `lemma:cubicimpliesnormal` applies to each complex root.
* Split: if `f = (t−α)(t−β)(t−γ)` over `ℚ`, then `α, β, γ` are integers by the integral
  root theorem (`exists_integer_of_is_root_of_monic`), and `α+β+γ = 1` by comparing
  `t²`-coefficients; `lemma:integralTraceOneImpliesNormal` applies.
-/

noncomputable section

namespace Cubic.Counting.AutomaticallyNormalProof

open Polynomial
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open Cubic.Counting.PolynomialCountData
open CubicTargets.Counting.AutomaticallyNormal

theorem traceOneCubic_monic (a b : ℤ) : (traceOneCubic a b).Monic := by
  unfold traceOneCubic
  monicity!

theorem map_traceOneCubic (a b : ℤ) :
    (traceOneCubic a b).map (Int.castRingHom ℚ) = cubic (a : ℚ) (b : ℚ) := by
  simp [traceOneCubic, cubic]

theorem cubic_coeff_two (a b : ℚ) : (cubic a b).coeff 2 = -1 := by
  simp [cubic, coeff_X_pow]

theorem aeval_map_int {A : Type*} [CommRing A] [Algebra ℚ A] (f : ℤ[X]) (y : A) :
    aeval y (f.map (Int.castRingHom ℚ)) = aeval y f := by
  rw [← algebraMap_int_eq, aeval_map_algebraMap]

/-- A rational root of a monic integral polynomial is an integer. -/
theorem exists_int_of_root (a b : ℤ) (r : ℚ) (hr : aeval r (traceOneCubic a b) = 0) :
    ∃ n : ℤ, r = n := by
  obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic (traceOneCubic_monic a b) hr
  exact ⟨n, hn⟩

theorem prod_coeff_two (α β γ : ℚ) :
    ((X - C α) * (X - C β) * (X - C γ)).coeff 2 = -(α + β + γ) := by
  have h : (X - C α) * (X - C β) * (X - C γ) =
      X ^ 3 - C (α + β + γ) * X ^ 2 + C (α * β + β * γ + γ * α) * X - C (α * β * γ) := by
    simp only [map_add, map_mul]
    ring
  rw [h]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- `cor:automaticallyNormal`. -/
theorem «cor:automaticallyNormal» : CubicTargets.Counting.AutomaticallyNormal.Claim := by
  rintro f ⟨⟨a, b, rfl⟩, hc | hs⟩
  · -- Galois group `C₃`: `lemma:cubicimpliesnormal`
    refine Or.inl ⟨hc, fun x hx => ?_⟩
    rw [map_traceOneCubic] at hc
    exact CubicImpliesNormalProof.«lemma:cubicimpliesnormal» (cubic (a : ℚ) (b : ℚ)) x
      (CyclicCubicField.irreducible_of_cyclic _ _ hc) hc (cubic_coeff_two _ _)
      (by rw [← map_traceOneCubic, aeval_map_int]; exact hx)
  · -- split: the roots are integers with sum one; `lemma:integralTraceOneImpliesNormal`
    refine Or.inr ⟨hs, fun α β γ hfac => ?_⟩
    have hroot : ∀ r : ℚ, (r = α ∨ r = β ∨ r = γ) → aeval r (traceOneCubic a b) = 0 := by
      intro r hr
      rw [← aeval_map_int, hfac, coe_aeval_eq_eval]
      rcases hr with rfl | rfl | rfl <;> simp
    obtain ⟨p, rfl⟩ := exists_int_of_root a b α (hroot α (Or.inl rfl))
    obtain ⟨q, rfl⟩ := exists_int_of_root a b β (hroot β (Or.inr (Or.inl rfl)))
    obtain ⟨s, rfl⟩ := exists_int_of_root a b γ (hroot γ (Or.inr (Or.inr rfl)))
    have htrace : (p : ℚ) + q + s = 1 := by
      have h := congrArg (fun g => g.coeff 2) hfac
      simp only [map_traceOneCubic, cubic_coeff_two, prod_coeff_two] at h
      linarith
    exact «lemma:integralTraceOneImpliesNormal» p q s (by exact_mod_cast htrace)

end Cubic.Counting.AutomaticallyNormalProof
