import CubicTargets.OrbitParametrization.SplitNormalElements
import Cubic.OrbitParametrization.SplitAlgebraTwist
import Cubic.OrbitParametrization.ModularInterpretation
import Cubic.Counting.NormalityDeterminant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `example:splitAlgebraNormalElement`

The paper gives only the parenthetical hint. The argument formalized here:

* Normality. The conjugates of `x ∈ ℚ³` are the rows of the circulant matrix
  `conjugates x₀ x₁ x₂`, whose determinant is `-(x₀+x₁+x₂)/2 · Σ(xᵢ-xⱼ)²`
  (`conjugates_det_sum_squares`), the negative of `eqn:normalityDeterminant`.
  So `x` is normal iff its trace is nonzero and its
  coordinates are not all equal (`isNormal_split_iff`). For trace one, this is "distinct or
  exactly two identical coordinates". The paper now includes this trace condition;
  `literal_statement_false` records why it cannot be dropped.
* Equivalence. A `C₃`-equivariant isomorphism `ℚ³ → ℚ³'` composed with the reflection
  `h ↦ -h` is an equivariant automorphism of `ℚ³`, hence a translation
  (`split_equivariant_translation`). So `(K_spl,x) ∼ (K_spl',x)` iff `x(c-h) = x(h)` for
  some `c` and all `h`. The reflection `h ↦ c - h` fixes one coordinate and swaps the other
  two, so this holds iff two coordinates of `x` agree (the swap of the two identical
  coordinates is the isomorphism, as the paper says). For normal `x`, not all three agree.
* Points. By `thm:modularInterpretation` (`equivalent_of_point_eq`), equal points give
  equivalent pairs; so for distinct coordinates the points differ. `K_spl ≅ K_spl'` by
  `example:splitAlgebra` (any transposition).
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open CubicTargets.OrbitParametrization.SplitNormalElements

theorem zmod3_cases (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide

/-- The conjugates of `x` are the rows of the circulant matrix. -/
theorem split_conjugates_eq (x : ZMod 3 → ℚ) :
    (fun g : C3 => splitAlg.act g x) =
      (Matrix.row (conjugates (x 0) (x 1) (x 2))) ∘ (Multiplicative.toAdd : C3 ≃ ZMod 3) := by
  funext g h
  obtain ⟨i, rfl⟩ := Multiplicative.ofAdd.surjective g
  change x (h + i) = conjugates (x 0) (x 1) (x 2) i h
  rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases h with rfl | rfl | rfl <;> rfl

theorem allEqual_iff (x : ZMod 3 → ℚ) : (∀ i j : ZMod 3, x i = x j) ↔ x 0 = x 1 ∧ x 1 = x 2 := by
  refine ⟨fun h => ⟨h 0 1, h 1 2⟩, fun ⟨h01, h12⟩ => ?_⟩
  have h0 : ∀ i, x i = x 0 := by
    intro i
    rcases zmod3_cases i with rfl | rfl | rfl
    · rfl
    · exact h01.symm
    · rw [← h12, ← h01]
  exact fun i j => by rw [h0 i, h0 j]

/-- Normality in the split `C₃`-algebra: nonzero trace and not all coordinates equal. -/
theorem isNormal_split_iff (x : ZMod 3 → ℚ) :
    IsNormal splitAlg x ↔ x 0 + x 1 + x 2 ≠ 0 ∧ ¬ ∀ i j : ZMod 3, x i = x j := by
  rw [IsNormal, split_conjugates_eq]
  refine (linearIndependent_equiv (Multiplicative.toAdd : C3 ≃ Fin 3)).trans ?_
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    (Cubic.Counting.conjugates_det_sum_squares (x 0) (x 1) (x 2)).2.2, allEqual_iff]
  constructor
  · intro h
    refine ⟨fun hs => h (by rw [hs]; ring), fun ⟨h01, h12⟩ => h (by rw [h01, h12]; ring)⟩
  · rintro ⟨hs, hne⟩ h
    rcases mul_eq_zero.mp h with h | h
    · exact hs (by linarith)
    · apply hne
      have h1 : (x 0 - x 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 0)]
      have h2 : (x 1 - x 2) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 0)]
      exact ⟨sub_eq_zero.mp (eq_zero_of_pow_eq_zero h1), sub_eq_zero.mp (eq_zero_of_pow_eq_zero h2)⟩

/-- Every coordinate of the sum of the conjugates is the trace `x₀+x₁+x₂`. -/
theorem split_traceSum_apply (x : ZMod 3 → ℚ) (h : ZMod 3) :
    (∑ g : C3, splitAlg.act g x) h = x 0 + x 1 + x 2 := by
  rw [Finset.sum_apply]
  change ∑ g : C3, x (h + Multiplicative.toAdd g) = _
  rw [← Equiv.sum_comp Multiplicative.ofAdd]
  simp only [toAdd_ofAdd]
  rw [show (∑ j : ZMod 3, x (h + j)) = ∑ j, x j from Equiv.sum_comp (Equiv.addLeft h) x]
  exact Fin.sum_univ_three x

theorem hasTraceOne_split_iff (x : ZMod 3 → ℚ) :
    HasTraceOne splitAlg x ↔ x 0 + x 1 + x 2 = 1 := by
  rw [HasTraceOne]
  constructor
  · intro h
    rw [← split_traceSum_apply x 0, h]
    rfl
  · intro h
    funext k
    rw [split_traceSum_apply, h]
    rfl

/-- The former unrestricted first sentence is false: `(-1,0,1)` has
distinct coordinates but trace zero, so it is not normal. -/
theorem literal_statement_false :
    ¬ ∀ x : ZMod 3 → ℚ, IsNormal splitAlg x ↔ Function.Injective x ∨ ExactlyTwoEqual x := by
  intro H
  let x : ZMod 3 → ℚ := fun j => coordLabel j - 1
  have hinj : Function.Injective x := fun i j hij => coordLabel_injective (sub_left_injective hij)
  have hn := (H x).mpr (Or.inl hinj)
  apply ((isNormal_split_iff x).mp hn).1
  change ((((0 : ZMod 3).val : ℕ) : ℚ) - 1) + ((((1 : ZMod 3).val : ℕ) : ℚ) - 1) +
    ((((2 : ZMod 3).val : ℕ) : ℚ) - 1) = 0
  rw [show (0 : ZMod 3).val = 0 from rfl, show (1 : ZMod 3).val = 1 from rfl,
    show (2 : ZMod 3).val = 2 from rfl]
  norm_num

/-- For trace-one `x`: normal iff not all coordinates equal, i.e. distinct or exactly two equal. -/
theorem isNormal_split_iff_of_traceOne (x : ZMod 3 → ℚ) (ht : HasTraceOne splitAlg x) :
    IsNormal splitAlg x ↔ Function.Injective x ∨ ExactlyTwoEqual x := by
  have htr := (hasTraceOne_split_iff x).mp ht
  rw [isNormal_split_iff]
  constructor
  · rintro ⟨-, hne⟩
    by_cases hinj : Function.Injective x
    · exact Or.inl hinj
    · refine Or.inr ⟨?_, hne⟩
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, hij, hne'⟩ := hinj
      exact ⟨i, j, hne', hij⟩
  · intro h
    refine ⟨by rw [htr]; norm_num, ?_⟩
    rcases h with hinj | ⟨-, hne⟩
    · intro hall
      exact absurd (hinj (hall 0 1)) (by decide)
    · exact hne

theorem isNormal_twist (x : ZMod 3 → ℚ) (hn : IsNormal splitAlg x) : IsNormal splitAlg.twist x := by
  have : (fun g : C3 => splitAlg.twist.act g x) = (fun g : C3 => splitAlg.act g x) ∘ Equiv.inv C3 :=
    rfl
  rw [IsNormal, this]
  exact (linearIndependent_equiv (Equiv.inv C3)).mpr hn

theorem hasTraceOne_twist (x : ZMod 3 → ℚ) (ht : HasTraceOne splitAlg x) :
    HasTraceOne splitAlg.twist x := by
  rw [HasTraceOne] at ht ⊢
  rw [← ht]
  exact Equiv.sum_comp (Equiv.inv C3) (fun g => splitAlg.act g x)

/-- `(K_spl,x) ∼ (K_spl',x)` iff `x` is invariant under a reflection `h ↦ c - h`. -/
theorem equivalent_twist_iff (x : ZMod 3 → ℚ) (hn : IsNormal splitAlg x)
    (ht : HasTraceOne splitAlg x) (hn' : IsNormal splitAlg.twist x)
    (ht' : HasTraceOne splitAlg.twist x) :
    Equivalent ⟨splitAlg, x, hn, ht⟩ ⟨splitAlg.twist, x, hn', ht'⟩ ↔
      ∃ c : ZMod 3, ∀ h, x (c - h) = x h := by
  constructor
  · rintro ⟨e, he, hx⟩
    let e' : (ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ) := e.trans reflect
    have he' : ∀ (g : C3) (y : ZMod 3 → ℚ), e' (splitAct g y) = splitAct g (e' y) := by
      intro g y
      funext h
      have := congrFun (he g y) (-h)
      change e (splitAct g y) (-h) = e y (-(h + Multiplicative.toAdd g))
      refine this.trans ?_
      change e y (-h + Multiplicative.toAdd g⁻¹) = _
      rw [toAdd_inv, neg_add]
    obtain ⟨c, hc⟩ := split_equivariant_translation e' he'
    refine ⟨c, fun h => ?_⟩
    have := hc x (h - c)
    change e x (-(h - c)) = x (h - c + c) at this
    have hx' : e x = x := hx
    rw [hx', neg_sub, sub_add_cancel] at this
    exact this
  · rintro ⟨c, hc⟩
    refine ⟨(shift c).trans reflect, fun g y => ?_, ?_⟩
    · funext h
      change y (-h + c + Multiplicative.toAdd g) = y (-(h + Multiplicative.toAdd g⁻¹) + c)
      congr 1
      rw [toAdd_inv]
      abel
    · funext h
      change x (-h + c) = x h
      rw [← hc h]
      congr 1
      abel

/-- A reflection `h ↦ c - h` of `ZMod 3` fixes one point and swaps the other two. -/
theorem reflection_swaps (c : ZMod 3) : c - (2 * c + 1) = 2 * c + 2 ∧ 2 * c + 2 ≠ 2 * c + 1 := by
  revert c; decide

theorem reflection_cases (i j h : ZMod 3) (hij : i ≠ j) :
    i + j - h = h ∨ (h = i ∧ i + j - h = j) ∨ (h = j ∧ i + j - h = i) := by
  revert i j h; decide

/-- Invariance under some reflection means two coordinates agree. -/
theorem exists_reflection_iff (x : ZMod 3 → ℚ) :
    (∃ c : ZMod 3, ∀ h, x (c - h) = x h) ↔ ∃ i j : ZMod 3, i ≠ j ∧ x i = x j := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨h1, h2⟩ := reflection_swaps c
    refine ⟨2 * c + 2, 2 * c + 1, h2, ?_⟩
    rw [← h1, hc]
  · rintro ⟨i, j, hij, hx⟩
    refine ⟨i + j, fun h => ?_⟩
    rcases reflection_cases i j h hij with h' | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
    · rw [h']
    · rw [h', hx]
    · rw [h', hx]

theorem «example:splitAlgebraNormalElement» :
    CubicTargets.OrbitParametrization.SplitNormalElements.Claim := by
  have hequiv : ∀ (x : ZMod 3 → ℚ) (hn : IsNormal splitAlg x) (ht : HasTraceOne splitAlg x)
      (hn' : IsNormal splitAlg.twist x) (ht' : HasTraceOne splitAlg.twist x),
      Equivalent ⟨splitAlg, x, hn, ht⟩ ⟨splitAlg.twist, x, hn', ht'⟩ ↔ ExactlyTwoEqual x := by
    intro x hn ht hn' ht'
    rw [equivalent_twist_iff, exists_reflection_iff, ExactlyTwoEqual]
    exact ⟨fun h => ⟨h, ((isNormal_split_iff x).mp hn).2⟩, fun h => h.1⟩
  refine ⟨isNormal_split_iff_of_traceOne, isNormal_twist, hasTraceOne_twist,
    fun x hn ht hn' ht' => ⟨hequiv x hn ht hn' ht', fun hinj => ⟨fun hpt => ?_, ?_⟩⟩⟩
  · obtain ⟨⟨i, j, hij, hx⟩, -⟩ := (hequiv x hn ht hn' ht').mp (equivalent_of_point_eq _ _ hpt)
    exact hij (hinj hx)
  · obtain ⟨e, -, he⟩ := «example:splitAlgebra».2 (Equiv.swap 0 1) ⟨0, 1, by decide, rfl⟩
    exact ⟨e, he⟩

end Cubic.OrbitParametrization.C3Algebra
