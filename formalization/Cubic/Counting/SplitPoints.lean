import Cubic.OrbitParametrization.SplitAutomorphisms
import Cubic.Counting.NormalitySpecializations
import Cubic.PoissonSummation.IntegralPointComparison
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Split points are integer triples modulo cyclic permutation (`lemma:reducibles`)

"For the split algebra, the `C₃`-equivariant automorphisms form the centralizer
of `C₃` in `S₃`, which is `C₃` itself. Thus split points are integer triples
`(α,β,γ)` with `α+β+γ=1`, modulo cyclic permutation. This action is free: a triple
fixed by a nonidentity cyclic permutation would have all coordinates equal to
`1/3`, which is not integral."

An integer triple of trace one is normal in `ℚ³` by
`lemma:normalityCriterion`, since `1-3a` is nonzero for integral `a`; its point has characteristic polynomial
`(t-α)(t-β)(t-γ)`, and two triples give the same point exactly when they differ by a
cyclic shift (`split_equivalent_iff`).
-/

noncomputable section

namespace Cubic.Counting.SplitPoints

open Cubic.OrbitParametrization Cubic.OrbitParametrization.C3Algebra

/-- Integer triples of trace one, indexed by `C₃`. -/
def Triple := {v : ZMod 3 → ℤ // v 0 + v 1 + v 2 = 1}

/-- The triple as an element of the split algebra. -/
def toSplit (v : Triple) : ZMod 3 → ℚ := fun h => (v.val h : ℚ)

theorem act_toSplit (v : Triple) (i : ZMod 3) :
    splitAlg.act (Multiplicative.ofAdd i) (toSplit v) = fun h => (v.val (h + i) : ℚ) := rfl

/-- The general normality criterion with integral coefficients and trace one. -/
theorem triple_normal (v : Triple) : C3Algebra.IsNormal splitAlg (toSplit v) := by
  apply NormalitySpecializations.integral_trace_one splitAlg (toSplit v)
    (secondCoeff (v.val 0) (v.val 1) (v.val 2)) (-(v.val 0 * v.val 1 * v.val 2))
  change (LinearMap.mul ℚ (ZMod 3 → ℚ) (toSplit v)).charpoly = _
  rw [NormalitySpecializations.split_charpoly]
  have ht : toSplit v 0 + toSplit v 1 + toSplit v 2 = 1 := by
    dsimp [toSplit]
    exact_mod_cast v.property
  rw [ht]
  simp only [map_one, one_mul, toSplit, secondCoeff, Int.cast_neg,
    Int.cast_mul, Int.cast_add, map_neg, sub_eq_add_neg]

theorem triple_trace (v : Triple) : HasTraceOne splitAlg (toSplit v) := by
  rw [HasTraceOne]
  funext h
  rw [Finset.sum_apply]
  change ∑ g : C3, (v.val (h + Multiplicative.toAdd g) : ℚ) = 1
  rw [← Equiv.sum_comp Multiplicative.ofAdd]
  simp only [toAdd_ofAdd]
  rw [show (∑ j : ZMod 3, (v.val (h + j) : ℚ)) = ∑ j, (v.val j : ℚ) from
    Equiv.sum_comp (Equiv.addLeft h) (fun j => (v.val j : ℚ))]
  rw [show (∑ j : ZMod 3, (v.val j : ℚ)) = (v.val 0 : ℚ) + v.val 1 + v.val 2 from
    Fin.sum_univ_three (fun j : ZMod 3 => (v.val j : ℚ))]
  exact_mod_cast v.property

/-- The pair `(ℚ³, (α,β,γ))`. -/
def triplePair (v : Triple) : Pair := ⟨splitAlg, toSplit v, triple_normal v, triple_trace v⟩

/-- The rational point of a triple. -/
def triplePoint (v : Triple) := point (triplePair v)

/-- Two triples give the same point exactly when they differ by a cyclic shift. -/
theorem triplePoint_eq_iff (v w : Triple) :
    triplePoint v = triplePoint w ↔ ∃ c : ZMod 3, ∀ h, w.val h = v.val (h + c) := by
  rw [triplePoint, triplePoint]
  constructor
  · intro hvw
    obtain ⟨c, hc⟩ := (split_equivalent_iff _ _ _ _ _ _).mp (equivalent_of_point_eq _ _ hvw)
    exact ⟨c, fun h => by
      have := hc h
      simp only [toSplit] at this
      exact_mod_cast this⟩
  · rintro ⟨c, hc⟩
    apply point_eq_of_equivalent
    exact (split_equivalent_iff _ _ _ _ _ _).mpr ⟨c, fun h => by
      change (w.val h : ℚ) = v.val (h + c)
      exact_mod_cast hc h⟩

/-- The action of `C₃` on triples is free. -/
theorem shift_free (v : Triple) (c : ZMod 3) (hc : ∀ h, v.val (h + c) = v.val h) : c = 0 := by
  by_contra hne
  have h1 := hc 0
  have h2 := hc c
  simp only [zero_add] at h1
  have hv := v.property
  rcases (show ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = 2 by decide) c hne with rfl | rfl
  · rw [show (1 : ZMod 3) + 1 = 2 by decide] at h2
    omega
  · rw [show (2 : ZMod 3) + 2 = 1 by decide] at h2
    omega

open Cubic.QuadraticCorrespondence Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open Cubic.QuadraticCorrespondence.DescendedCoefficients Cubic.QuadraticCorrespondence.RationalQuotientFunctor
open CyclicGroupAlgebra

/-- Evaluating the point of a triple at the coordinate `0`. -/
theorem triplePoint_apply (v : Triple) (b : quotientFixedRing) :
    triplePoint v b =
      evalZero (quotientPoint (triplePair v).algebra.carrier (unitOf (triplePair v)) b) := by
  have h := algebraMap_point (triplePair v) b
  rw [pointOver] at h
  rw [← h]
  rfl

theorem unit_triple_zero (v : Triple) (i : ZMod 3) :
    evalZero (((unitOf (triplePair v)).val : GroupAlgebra (triplePair v).algebra.carrier) i) =
      (v.val (-i) : ℚ) := by
  rw [unitOf_val, unitElement_apply]
  change toSplit v (0 + Multiplicative.toAdd (Multiplicative.ofAdd (-i))) = _
  simp [toSplit]

theorem triplePoint_linear (v : Triple) :
    triplePoint v linearCoefficient =
      ((secondCoeff (v.val 0) (v.val 1) (v.val 2) : ℤ) : ℚ) := by
  rw [triplePoint_apply, quotientPoint_linearCoefficient]
  simp only [secondCoeff, map_add, map_mul]
  rw [unit_triple_zero, unit_triple_zero, unit_triple_zero, neg_zero,
    show (-1 : ZMod 3) = 2 by decide, show (-2 : ZMod 3) = 1 by decide]
  push_cast
  ring

theorem triplePoint_constant (v : Triple) :
    triplePoint v constantCoefficient =
      ((constantCoeff (v.val 0) (v.val 1) (v.val 2) : ℤ) : ℚ) := by
  rw [triplePoint_apply, quotientPoint_constantCoefficient]
  simp only [constantCoeff, map_neg, map_mul]
  rw [unit_triple_zero, unit_triple_zero, unit_triple_zero, neg_zero,
    show (-1 : ZMod 3) = 2 by decide, show (-2 : ZMod 3) = 1 by decide]
  push_cast
  ring

/-- The point of an integer triple is `D₀`-integral. -/
theorem triplePoint_integral (v : Triple) :
    Cubic.ToricHeights.AffineInvariantRing.IntegralPoint (triplePoint v) :=
  (Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion _).mpr
    ⟨⟨_, triplePoint_linear v⟩, ⟨_, triplePoint_constant v⟩⟩

open Polynomial in
/-- A rational root of the characteristic polynomial of an integral point is an integer. -/
theorem root_integer (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (hP : Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P) (r : ℚ)
    (hr : aeval r (characteristicPolynomial P) = 0) : ∃ z : ℤ, (z : ℚ) = r := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion P).mp hP
  let p : ℤ[X] := X ^ 3 - X ^ 2 + C a * X + C b
  have hmonic : p.Monic := by simp only [p]; monicity!
  have hmap : p.map (algebraMap ℤ ℚ) = characteristicPolynomial P := by
    simp [p, characteristicPolynomial, CorrespondencePolynomials.cubic, ha, hb]
  have hr' : aeval r p = 0 := by
    rw [← hmap, aeval_map_algebraMap] at hr
    exact hr
  obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic hmonic hr'
  exact ⟨z, hz⟩

open Polynomial in
/-- Every integral point whose characteristic polynomial splits over `ℚ` is the point of
an integer triple. -/
theorem exists_triple (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (hP : Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P)
    (hs : (characteristicPolynomial P).Splits) : ∃ v : Triple, triplePoint v = P := by
  obtain ⟨q, rfl⟩ := point_surjective P
  have hprod := characteristicPolynomial_point q
  have hroot : ∀ y : q.algebra.carrier, y = q.element ∨ y = q.algebra.act σ q.element ∨
      y = q.algebra.act (σ ^ 2) q.element → aeval y (characteristicPolynomial (point q)) = 0 := by
    intro y hy
    rw [← eval_map_algebraMap, hprod]
    rcases hy with rfl | rfl | rfl <;> simp [eval_mul, eval_sub]
  rcases q.algebra.model with ⟨hK, -, -⟩ | ⟨e, he⟩
  · exfalso
    letI := hK.toField
    have hx := hroot q.element (Or.inl rfl)
    have hmem : q.element ∈ ((characteristicPolynomial (point q)).map
        (algebraMap ℚ q.algebra.carrier)).roots := by
      rw [mem_roots (Polynomial.map_ne_zero (by
        intro h0
        have := congrArg (fun f : ℚ[X] => f.coeff 3) h0
        simp [characteristicPolynomial, CorrespondencePolynomials.cubic] at this)), IsRoot.def,
        eval_map_algebraMap]
      exact hx
    rw [hs.roots_map] at hmem
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp hmem
    have hfix : q.algebra.act σ q.element = q.algebra.act 1 q.element := by
      rw [← hr, AlgEquiv.commutes, AlgEquiv.commutes]
    exact absurd (q.normal.injective hfix) (by decide)
  · -- the coordinates of `e x` are integer roots summing to one
    set y : ZMod 3 → ℚ := e q.element
    have hyroot : ∀ h : ZMod 3, aeval (y h) (characteristicPolynomial (point q)) = 0 := by
      intro h
      have := congrArg ((Pi.evalAlgHom ℚ (fun _ => ℚ) h).comp e.toAlgHom)
        (hroot q.element (Or.inl rfl))
      rwa [map_zero, ← Polynomial.aeval_algHom_apply] at this
    choose z hz using fun h => root_integer (point q) hP (y h) (hyroot h)
    have htr : y 0 + y 1 + y 2 = 1 := by
      have := congrArg (fun w : q.algebra.carrier => e w 0) q.traceOne
      simp only [map_sum, Finset.sum_apply, map_one, Pi.one_apply] at this
      rw [sum_C3] at this
      simp only [he, zero_add, toAdd_one, toAdd_ofAdd] at this
      exact this
    refine ⟨⟨z, by exact_mod_cast (show ((z 0 + z 1 + z 2 : ℤ) : ℚ) = 1 by push_cast; rw [hz, hz, hz]; exact htr)⟩, ?_⟩
    apply point_eq_of_equivalent
    refine ⟨e.symm, fun g w => ?_, ?_⟩
    · apply e.injective
      erw [AlgEquiv.apply_symm_apply]
      funext h
      erw [he, AlgEquiv.apply_symm_apply]
      rfl
    · apply e.injective
      erw [AlgEquiv.apply_symm_apply]
      funext h
      exact hz h

end Cubic.Counting.SplitPoints
