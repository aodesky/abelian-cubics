import Cubic.ToricHeights.TernaryCyclicInvariants
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fintype.Perm

/-!
# Every `C₃`-invariant of `ℤ[X,Y,Z]` is `S + B·δ` with `S,B` symmetric

This is the matrix argument of Campbell–Wehlau [Example 4.6] for `A₃ ≤ S₃`, with the
secondary invariants `1, δ` (`δ = X²Y+Y²Z+Z²X`, the orbit sum `Z(m)` of `m = X²Y`).
For a `C₃`-invariant `f` and the transposition `τ = (X Y)`,
`(f, τf) = [[1, δ], [1, τδ]] · (S, B)` must be solved for symmetric `S, B`; the determinant is
`τδ - δ = (X-Y)(Y-Z)(Z-X)`, the Vandermonde product, whose content is one. Over `ℤ` the
solution exists because `f - τf` is divisible by the Vandermonde product. That divisibility
is proved here by successive substitutions: `p - p|_{X_i ↦ X_j}` is always divisible by
`X_i - X_j`, and `f - τf` vanishes under each of the three substitutions (using the
`C₃`-invariance of `f`).
-/

noncomputable section

namespace Cubic.ToricHeights.CyclicSymmetricDecomposition

open MvPolynomial TernaryCyclicInvariants

/-- `X_i - X_j` divides `p - p(X_i ↦ X_j)`. -/
theorem X_sub_X_dvd_sub_rename {σ : Type*} [DecidableEq σ] (i j : σ) (p : MvPolynomial σ ℤ) :
    (X i - X j) ∣ p - rename (fun k => if k = i then j else k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have h := dvd_add hp hq
    rw [map_add]
    convert h using 1
    ring
  | mul_X p k hp =>
    have hk : (X i - X j : MvPolynomial σ ℤ) ∣ X k - X (if k = i then j else k) := by
      by_cases h : k = i
      · subst h; simp
      · simp [h]
    have h := dvd_add (dvd_mul_of_dvd_left hp (X k))
      (dvd_mul_of_dvd_right hk (rename (fun k => if k = i then j else k) p))
    rw [map_mul, rename_X]
    convert h using 1
    ring

/-- If `p(X_i ↦ X_j) = 0` then `X_i - X_j` divides `p`. -/
theorem X_sub_X_dvd_of_rename_eq_zero {σ : Type*} [DecidableEq σ] (i j : σ)
    (p : MvPolynomial σ ℤ) (hp : rename (fun k => if k = i then j else k) p = 0) :
    (X i - X j) ∣ p := by
  simpa [hp] using X_sub_X_dvd_sub_rename i j p

theorem X_sub_X_ne_zero {i j : Fin 3} (h : i ≠ j) : (X i - X j : TernaryRing) ≠ 0 :=
  sub_ne_zero.mpr fun h' => h (X_injective h')

/-- The transposition `X ↔ Y`. -/
abbrev swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The Vandermonde product `(X-Y)(Y-Z)(Z-X)`. -/
def vandermonde : TernaryRing := (X 0 - X 1) * (X 1 - X 2) * (X 2 - X 0)

theorem vandermonde_ne_zero : vandermonde ≠ 0 :=
  mul_ne_zero (mul_ne_zero (X_sub_X_ne_zero (by decide)) (X_sub_X_ne_zero (by decide)))
    (X_sub_X_ne_zero (by decide))

theorem rename_swap01_vandermonde : rename swap01 vandermonde = -vandermonde := by
  have h0 : swap01 0 = 1 := by decide
  have h1 : swap01 1 = 0 := by decide
  have h2 : swap01 2 = 2 := by decide
  simp only [vandermonde, map_mul, map_sub, rename_X, h0, h1, h2]
  ring

theorem rename_cycle_vandermonde : rename (finRotate 3) vandermonde = vandermonde := by
  have h0 : finRotate 3 0 = 1 := by decide
  have h1 : finRotate 3 1 = 2 := by decide
  have h2 : finRotate 3 2 = 0 := by decide
  simp only [vandermonde, map_mul, map_sub, rename_X, h0, h1, h2]
  ring

theorem rename_cycle_delta : rename (finRotate 3) delta = delta := by
  have h0 : finRotate 3 0 = 1 := by decide
  have h1 : finRotate 3 1 = 2 := by decide
  have h2 : finRotate 3 2 = 0 := by decide
  simp only [delta, map_mul, map_add, map_pow, rename_X, h0, h1, h2]
  ring

/-- `δ - τδ = -(X-Y)(Y-Z)(Z-X)`. -/
theorem delta_sub_swap : delta - rename swap01 delta = -vandermonde := by
  have h0 : swap01 0 = 1 := by decide
  have h1 : swap01 1 = 0 := by decide
  have h2 : swap01 2 = 2 := by decide
  simp only [delta, vandermonde, map_mul, map_add, map_pow, rename_X, h0, h1, h2]
  ring

/-- The difference `f - τf` of a `C₃`-invariant is divisible by the Vandermonde product. -/
theorem vandermonde_dvd (f : TernaryRing) (hf : rename (finRotate 3) f = f) :
    vandermonde ∣ f - rename swap01 f := by
  -- the three substitutions `X ↦ Y`, `Y ↦ Z`, `Z ↦ X` all kill `f - τf`
  have e1 : (fun k : Fin 3 => if k = 0 then (1 : Fin 3) else k) ∘ swap01 =
      fun k : Fin 3 => if k = 0 then (1 : Fin 3) else k := by decide
  have g1 : rename (fun k : Fin 3 => if k = 0 then (1 : Fin 3) else k)
      (f - rename swap01 f) = 0 := by
    rw [map_sub, rename_rename, e1, sub_self]
  have e2 : (fun k : Fin 3 => if k = 1 then (2 : Fin 3) else k) ∘ (finRotate 3 ∘ finRotate 3) =
      (fun k : Fin 3 => if k = 1 then (2 : Fin 3) else k) ∘ swap01 := by decide
  have g2 : rename (fun k : Fin 3 => if k = 1 then (2 : Fin 3) else k)
      (f - rename swap01 f) = 0 := by
    have : rename (fun k : Fin 3 => if k = 1 then (2 : Fin 3) else k) f =
        rename (fun k : Fin 3 => if k = 1 then (2 : Fin 3) else k) (rename swap01 f) := by
      conv_lhs => rw [← hf, ← hf]
      rw [rename_rename, rename_rename, rename_rename, ← e2]
      rfl
    rw [map_sub, this, sub_self]
  have e3 : (fun k : Fin 3 => if k = 2 then (0 : Fin 3) else k) ∘ finRotate 3 =
      (fun k : Fin 3 => if k = 2 then (0 : Fin 3) else k) ∘ swap01 := by decide
  have g3 : rename (fun k : Fin 3 => if k = 2 then (0 : Fin 3) else k)
      (f - rename swap01 f) = 0 := by
    have : rename (fun k : Fin 3 => if k = 2 then (0 : Fin 3) else k) f =
        rename (fun k : Fin 3 => if k = 2 then (0 : Fin 3) else k) (rename swap01 f) := by
      conv_lhs => rw [← hf]
      rw [rename_rename, rename_rename, e3]
    rw [map_sub, this, sub_self]
  -- peel off the three linear factors
  obtain ⟨h, hh⟩ := X_sub_X_dvd_of_rename_eq_zero 0 1 _ g1
  rw [hh] at g2 g3 ⊢
  have h2 : rename (fun k : Fin 3 => if k = 1 then (2 : Fin 3) else k) h = 0 := by
    rw [map_mul] at g2
    simp only [map_sub, rename_X] at g2
    have hne : (X 0 - X 2 : TernaryRing) ≠ 0 := X_sub_X_ne_zero (by decide)
    simpa [hne] using g2
  obtain ⟨k, rfl⟩ := X_sub_X_dvd_of_rename_eq_zero 1 2 h h2
  have h3 : rename (fun k : Fin 3 => if k = 2 then (0 : Fin 3) else k) k = 0 := by
    rw [map_mul, map_mul] at g3
    simp only [map_sub, rename_X] at g3
    have hne : ((X 0 - X 1) * (X 1 - X 0) : TernaryRing) ≠ 0 :=
      mul_ne_zero (X_sub_X_ne_zero (by decide)) (X_sub_X_ne_zero (by decide))
    rw [← mul_assoc] at g3
    simpa [hne] using g3
  obtain ⟨m, rfl⟩ := X_sub_X_dvd_of_rename_eq_zero 2 0 k h3
  exact ⟨m, by simp only [vandermonde]; ring⟩

/-- Invariance under the generators `X ↦ Y ↦ Z ↦ X` and `X ↔ Y` of `S₃` is symmetry. -/
theorem isSymmetric_of_cycle_swap (p : TernaryRing) (hc : rename (finRotate 3) p = p)
    (hs : rename swap01 p = p) : p.IsSymmetric := by
  have hall : ∀ e : Equiv.Perm (Fin 3), e = 1 ∨ e = finRotate 3 ∨
      e = finRotate 3 * finRotate 3 ∨ e = swap01 ∨ e = finRotate 3 * swap01 ∨
      e = finRotate 3 * finRotate 3 * swap01 := by decide
  intro e
  rcases hall e with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Equiv.Perm.coe_mul, Equiv.Perm.coe_one, ← rename_rename, rename_id_apply, hc, hs]

/-- The decomposition `f = S + B·δ` of a `C₃`-invariant with `S, B` symmetric. -/
theorem exists_symmetric_decomposition (f : TernaryRing) (hf : rename (finRotate 3) f = f) :
    ∃ S B : TernaryRing, S.IsSymmetric ∧ B.IsSymmetric ∧ f = S + B * delta := by
  obtain ⟨m, hm⟩ := vandermonde_dvd f hf
  have hττ : ∀ p : TernaryRing, rename swap01 (rename swap01 p) = p := fun p => by
    rw [rename_rename]
    have : (swap01 : Fin 3 → Fin 3) ∘ swap01 = id := by decide
    rw [this, rename_id_apply]
  have hcτ : rename (finRotate 3) (rename swap01 f) = rename swap01 f := by
    have e : (finRotate 3 : Fin 3 → Fin 3) ∘ swap01 = swap01 ∘ (finRotate 3 ∘ finRotate 3) := by
      decide
    conv_rhs => rw [← hf, ← hf]
    rw [rename_rename, rename_rename, rename_rename, e]
    rfl
  -- `m` is symmetric
  have hmτ : rename swap01 m = m := by
    have h := congrArg (rename swap01) hm
    rw [map_sub, hττ, map_mul, rename_swap01_vandermonde] at h
    have h' : vandermonde * (rename swap01 m) = vandermonde * m := by
      linear_combination h + hm
    exact mul_left_cancel₀ vandermonde_ne_zero h'
  have hmc : rename (finRotate 3) m = m := by
    have h := congrArg (rename (finRotate 3)) hm
    rw [map_sub, hf, hcτ, map_mul, rename_cycle_vandermonde] at h
    exact mul_left_cancel₀ vandermonde_ne_zero (h.symm.trans hm)
  refine ⟨f + m * delta, -m, ?_, ?_, by ring⟩
  · apply isSymmetric_of_cycle_swap
    · rw [map_add, map_mul, hf, hmc, rename_cycle_delta]
    · have hd := delta_sub_swap
      rw [map_add, map_mul, hmτ]
      linear_combination -hm - m * hd
  · apply isSymmetric_of_cycle_swap
    · rw [map_neg, hmc]
    · rw [map_neg, hmτ]

end Cubic.ToricHeights.CyclicSymmetricDecomposition
