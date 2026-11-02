import Cubic.OrbitParametrization.ModularInterpretation
import Cubic.OrbitParametrization.SplitAlgebra

/-!
# Equivariant automorphisms of the split algebra

In the proof of `lemma:reducibles`: the `C₃`-equivariant automorphisms of the
split algebra form the centralizer of `C₃` in `S₃`, which is `C₃` itself. We prove
this directly: a `ℚ`-algebra map `ℚ³ → ℚ` is evaluation at a coordinate, so an
automorphism permutes coordinates, and equivariance forces a translation. Hence
two pairs `(ℚ³,x)`, `(ℚ³,x')` are equivalent exactly when `x'` is a cyclic shift of
`x`.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

/-- A `ℚ`-algebra map from `ℚ³` to `ℚ` is evaluation at some coordinate. -/
theorem algHom_eq_eval (φ : (ZMod 3 → ℚ) →ₐ[ℚ] ℚ) : ∃ k : ZMod 3, ∀ f, φ f = f k := by
  classical
  have hidem : ∀ h : ZMod 3, φ (Pi.single h 1) = 0 ∨ φ (Pi.single h 1) = 1 := by
    intro h
    have h2 : φ (Pi.single h 1) * φ (Pi.single h 1) = φ (Pi.single h 1) := by
      rw [← map_mul]
      congr 1
      ext i
      by_cases hi : i = h
      · subst hi; simp
      · simp [hi]
    exact IsIdempotentElem.iff_eq_zero_or_one.mp h2
  have hsum : ∑ h : ZMod 3, φ (Pi.single h 1) = 1 := by
    rw [← map_sum, ← map_one φ]
    congr 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hortho : ∀ h h' : ZMod 3, h ≠ h' → φ (Pi.single h 1) * φ (Pi.single h' 1) = 0 := by
    intro h h' hne
    rw [← map_mul, ← map_zero φ]
    congr 1
    ext i
    by_cases hi : i = h
    · subst hi; simp [hne]
    · simp [Pi.single_apply, hi]
  obtain ⟨k, hk⟩ : ∃ k : ZMod 3, φ (Pi.single k 1) = 1 := by
    by_contra hno
    push_neg at hno
    have : ∀ h, φ (Pi.single h 1) = 0 := fun h => (hidem h).resolve_right (hno h)
    rw [Finset.sum_eq_zero (fun h _ => this h)] at hsum
    exact zero_ne_one hsum
  refine ⟨k, fun f => ?_⟩
  have hf : f = ∑ h : ZMod 3, f h • Pi.single h 1 := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hzero : ∀ h, h ≠ k → φ (Pi.single h 1) = 0 := by
    intro h hne
    have := hortho h k hne
    rw [hk, mul_one] at this
    exact this
  conv_lhs => rw [hf]
  rw [map_sum, Finset.sum_eq_single k]
  · rw [map_smul, hk, smul_eq_mul, mul_one]
  · intro h _ hne
    rw [map_smul, hzero h hne, smul_zero]
  · simp

/-- Equivariant automorphisms of the split algebra are translations. -/
theorem split_equivariant_translation (e : (ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ))
    (he : ∀ (g : C3) (y : ZMod 3 → ℚ), e (splitAct g y) = splitAct g (e y)) :
    ∃ c : ZMod 3, ∀ (y : ZMod 3 → ℚ) (h : ZMod 3), e y h = y (h + c) := by
  classical
  have hev : ∀ h : ZMod 3, ∃ k : ZMod 3, ∀ y, e y h = y k := fun h =>
    algHom_eq_eval ((Pi.evalAlgHom ℚ (fun _ => ℚ) h).comp e.toAlgHom)
  choose π hπ using hev
  refine ⟨π 0, fun y h => ?_⟩
  have hshift : π h = h + π 0 := by
    -- test equivariance on the indicator of `π h`
    have := congrFun (he (Multiplicative.ofAdd h) (Pi.single (π h) 1)) 0
    change e (fun i => (Pi.single (π h) (1 : ℚ) : ZMod 3 → ℚ) (i + h)) 0 =
      e (Pi.single (π h) 1) (0 + h) at this
    rw [zero_add, hπ, hπ] at this
    simp only [Pi.single_apply] at this
    by_contra hne
    have h1 : π 0 + h ≠ π h := fun heq => hne (by rw [← heq, add_comm])
    rw [if_neg h1] at this
    exact zero_ne_one this
  rw [hπ, hshift]

/-- Split pairs are equivalent exactly when their elements differ by a cyclic shift. -/
theorem split_equivalent_iff (x y : ZMod 3 → ℚ) (hxn : IsNormal splitAlg x)
    (hxt : HasTraceOne splitAlg x) (hyn : IsNormal splitAlg y) (hyt : HasTraceOne splitAlg y) :
    Equivalent ⟨splitAlg, x, hxn, hxt⟩ ⟨splitAlg, y, hyn, hyt⟩ ↔
      ∃ c : ZMod 3, ∀ h : ZMod 3, y h = x (h + c) := by
  constructor
  · rintro ⟨e, he, hexy⟩
    obtain ⟨c, hc⟩ := split_equivariant_translation e he
    have hexy' : e x = y := hexy
    exact ⟨c, fun h => by rw [← hexy']; exact hc x h⟩
  · rintro ⟨c, hc⟩
    refine ⟨shift c, fun g z => ?_, ?_⟩
    · refine funext fun h => ?_
      change z (h + c + Multiplicative.toAdd g) = z (h + Multiplicative.toAdd g + c)
      congr 1
      abel
    · exact funext fun h => (hc h).symm

end Cubic.OrbitParametrization.C3Algebra
