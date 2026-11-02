import Cubic.OrbitParametrization.FibreAlgebra
import Cubic.OrbitParametrization.ModuliMap
import Cubic.QuadraticCorrespondence.GeometricQuotientFibres
import Cubic.QuadraticCorrespondence.QuotientGaloisAction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# `γ₁(P)` is a `C₃`-algebra with a trace-one normal element

This is the torsor property used in [O'Desky–Rosen, Prop. 2.4, second proof]:
the fibre algebra `A ⊗_{A^G,P} ℚ` (`FibreAlgebra`) is a `C₃`-algebra and the image
`X̄` of the first coordinate is a trace-one normal element. We verify it
concretely. A cover point `g` over `P` in an algebraic closure
(`GeometricQuotientFibres`) and its two shifts give three maps from the fibre
algebra; a rational relation among the coordinates becomes a circulant relation
killed by the unit `g`, so the coordinates form a basis. If the coordinates of `g`
are rational, evaluation along the orbit identifies the fibre algebra with `ℚ³`.
Otherwise a Galois automorphism moves `g` to one of its shifts, and the map given
by `g` is injective, so the fibre algebra is a field.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open CyclicGroupAlgebra Module
open Cubic.QuadraticCorrespondence Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open Cubic.QuadraticCorrespondence.RationalCoverFunctor Cubic.QuadraticCorrespondence.RationalQuotientFunctor

variable (P : quotientFixedRing →ₐ[ℚ] ℚ)

theorem fibreAct_coord (i : ZMod 3) : fibreAct P (fibreCoord P i) = fibreCoord P (-1 + i) := by
  rw [fibreCoord, fibreAct_mk, coverAct_coord]
  rfl

theorem fibreActHom_coord (k i : ZMod 3) :
    fibreActHom P (Multiplicative.ofAdd k) (fibreCoord P i) = fibreCoord P (i - k) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
  change (fibreEquiv P ^ k.val) (fibreCoord P i) = _
  rcases hk with rfl | rfl | rfl
  · simp
  · rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
    change fibreAct P (fibreCoord P i) = _
    rw [fibreAct_coord, show (-1 : ZMod 3) + i = i - 1 by ring]
  · rw [show (2 : ZMod 3).val = 2 from rfl, pow_two, AlgEquiv.mul_apply]
    change fibreAct P (fibreAct P (fibreCoord P i)) = _
    rw [fibreAct_coord, fibreAct_coord, show (-1 : ZMod 3) + (-1 + i) = i - 2 by ring]

/-- The algebraic closure used for geometric points. -/
abbrev Kb := AlgebraicClosure E

/-- A cover point over `P` in the algebraic closure. -/
def geomLift : traceOneUnits Kb :=
  (GeometricQuotientFibres.quotientPoint_surjective (K := Kb)
    (QuotientGaloisAction.pointOver P)).choose

theorem geomLift_over : quotientPoint Kb (geomLift P) = (Algebra.ofId ℚ Kb).comp P :=
  (GeometricQuotientFibres.quotientPoint_surjective (K := Kb)
    (QuotientGaloisAction.pointOver P)).choose_spec

/-- The map from the fibre algebra given by the `j`-th shift of the geometric lift. -/
def geomHom (j : ZMod 3) : Fibre P →ₐ[ℚ] Kb :=
  fibreHom P _ (shift_over P (geomLift P) (geomLift_over P) (Multiplicative.ofAdd j))

theorem geomHom_coord (j i : ZMod 3) :
    geomHom P j (fibreCoord P i) = ((geomLift P).val : GroupAlgebra Kb) (i - j) := by
  rw [geomHom, fibreHom_coord, shift_apply]

theorem fibreCoord_expand (s : Fibre P) : ∃ q₀ q₁ q₂ : ℚ,
    s = q₀ • fibreCoord P 0 + q₁ • fibreCoord P 1 + q₂ • fibreCoord P 2 := by
  have hs : s ∈ Submodule.span ℚ (Set.range (fibreCoord P)) := by
    rw [fibreCoord_span]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hs
  obtain ⟨c, hc⟩ := hs
  refine ⟨c 0, c 1, c 2, ?_⟩
  rw [← hc]
  exact Fin.sum_univ_three (fun i : ZMod 3 => c i • fibreCoord P i)

/-- The three geometric maps are jointly injective. -/
theorem geomHom_joint (s : Fibre P) (h : ∀ j, geomHom P j s = 0) : s = 0 := by
  obtain ⟨q₀, q₁, q₂, hs⟩ := fibreCoord_expand P s
  obtain ⟨h₀, h₁, h₂⟩ := coord_relation_zero P (geomLift P) (geomLift_over P) q₀ q₁ q₂ s hs h
  rw [hs, h₀, h₁, h₂]
  simp

theorem fibreCoord_linearIndependent : LinearIndependent ℚ (fibreCoord P) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hs : (0 : Fibre P) = c 0 • fibreCoord P 0 + c 1 • fibreCoord P 1 + c 2 • fibreCoord P 2 := by
    rw [← hc]; exact Fin.sum_univ_three (fun i : ZMod 3 => c i • fibreCoord P i)
  obtain ⟨h₀, h₁, h₂⟩ := coord_relation_zero P (geomLift P) (geomLift_over P) (c 0) (c 1) (c 2) 0
    hs (fun j => map_zero _)
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
  rcases hi with rfl | rfl | rfl
  · exact h₀
  · exact h₁
  · exact h₂

/-- The coordinates form a basis of the fibre algebra. -/
def fibreBasis : Basis (ZMod 3) ℚ (Fibre P) :=
  Basis.mk (fibreCoord_linearIndependent P) (by rw [fibreCoord_span])

theorem fibre_finrank : finrank ℚ (Fibre P) = 3 := by
  rw [finrank_eq_card_basis (fibreBasis P), ZMod.card]

instance : Nontrivial (Fibre P) :=
  Module.nontrivial_of_finrank_pos (R := ℚ) (by rw [fibre_finrank]; norm_num)

theorem fibreCoord_injective : Function.Injective (fibreCoord P) :=
  (fibreCoord_linearIndependent P).injective

/-- Shifting the geometric lift is precomposition with the action. -/
theorem geomHom_act (h : ZMod 3) (s : Fibre P) :
    geomHom P 0 (fibreActHom P (Multiplicative.ofAdd h) s) = geomHom P h s := by
  have := fibreHom_ext P ((geomHom P 0).comp (fibreActHom P (Multiplicative.ofAdd h)).toAlgHom)
    (geomHom P h) (fun i => by
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, fibreActHom_coord,
        geomHom_coord, sub_zero])
  exact congrArg (fun φ : Fibre P →ₐ[ℚ] Kb => φ s) this

/-- A Galois automorphism carries the geometric map to one of its shifts. -/
theorem galois_geomHom (τ : Kb ≃ₐ[ℚ] Kb) : ∃ j : ZMod 3, ∀ s, τ (geomHom P 0 s) = geomHom P j s := by
  set g0 := cyclicUnits Kb (Multiplicative.ofAdd (0 : ZMod 3)) * geomLift P
  have hg0 : quotientPoint Kb g0 = (Algebra.ofId ℚ Kb).comp P :=
    shift_over P (geomLift P) (geomLift_over P) _
  have hτ : quotientPoint Kb (mapUnits τ.toAlgHom.toRingHom g0) = quotientPoint Kb g0 := by
    rw [quotientPoint_mapUnits, hg0]
    ext c
    exact τ.commutes (P c)
  obtain ⟨i, hi⟩ := (GeometricQuotientFibres.quotientPoint_eq_iff _ _).mp hτ
  refine ⟨Multiplicative.toAdd i, fun s => ?_⟩
  have := fibreHom_ext P (τ.toAlgHom.comp (geomHom P 0)) (geomHom P (Multiplicative.toAdd i))
    (fun k => by
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
      rw [geomHom_coord, geomHom_coord, sub_zero]
      have hk := congrArg (fun u : traceOneUnits Kb => (u.val : GroupAlgebra Kb) k) hi
      simp only [mapUnits_coefficient] at hk
      rw [← ofAdd_toAdd i, shift_apply, shift_apply, shift_apply, sub_zero, sub_zero] at hk
      exact hk)
  exact congrArg (fun φ : Fibre P →ₐ[ℚ] Kb => φ s) this

instance : FiniteDimensional ℚ (Fibre P) :=
  Module.finite_of_finrank_pos (by rw [fibre_finrank]; norm_num)

theorem fibreActHom_injective : Function.Injective (fibreActHom P) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := congrArg (fun e : Fibre P ≃ₐ[ℚ] Fibre P => e (fibreCoord P 0)) hg
  simp only [AlgEquiv.one_apply] at h
  rw [← ofAdd_toAdd g, fibreActHom_coord] at h
  have hk := fibreCoord_injective P h
  rw [zero_sub, neg_eq_zero] at hk
  rw [← ofAdd_toAdd g, hk]
  rfl

/-- Rational geometric coordinates: the fibre algebra is split. -/
theorem fibre_split (hrat : ∀ i, ((geomLift P).val : GroupAlgebra Kb) i ∈
      Set.range (algebraMap ℚ Kb)) :
    ∃ e : Fibre P ≃ₐ[ℚ] (ZMod 3 → ℚ), ∀ (g : C3) (y : Fibre P) (h : ZMod 3),
      e (fibreActHom P g y) h = e y (h + Multiplicative.toAdd g) := by
  have hval : ∀ s, geomHom P 0 s ∈ (⊥ : Subalgebra ℚ Kb) := by
    intro s
    obtain ⟨q₀, q₁, q₂, rfl⟩ := fibreCoord_expand P s
    simp only [map_add, map_smul, geomHom_coord, sub_zero]
    have hb : ∀ i, ((geomLift P).val : GroupAlgebra Kb) i ∈ (⊥ : Subalgebra ℚ Kb) := fun i => by
      obtain ⟨q, hq⟩ := hrat i
      rw [← hq]
      exact Subalgebra.algebraMap_mem _ q
    exact Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.smul_mem _ (hb 0) _)
      (Subalgebra.smul_mem _ (hb 1) _)) (Subalgebra.smul_mem _ (hb 2) _)
  let h0' : Fibre P →ₐ[ℚ] ℚ :=
    (Algebra.botEquiv ℚ Kb).toAlgHom.comp ((geomHom P 0).codRestrict ⊥ hval)
  have hh0' : ∀ s, algebraMap ℚ Kb (h0' s) = geomHom P 0 s := by
    intro s
    have h := (Algebra.botEquiv ℚ Kb).symm_apply_apply ((geomHom P 0).codRestrict ⊥ hval s)
    rw [Algebra.botEquiv_symm_apply] at h
    exact congrArg Subtype.val h
  let e : Fibre P →ₐ[ℚ] (ZMod 3 → ℚ) :=
    Pi.algHom ℚ _ (fun h => h0'.comp (fibreActHom P (Multiplicative.ofAdd h)).toAlgHom)
  have hinj : Function.Injective e := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    apply geomHom_joint P y
    intro j
    have := congrFun hy j
    change h0' (fibreActHom P (Multiplicative.ofAdd j) y) = 0 at this
    rw [← geomHom_act, ← hh0', this, map_zero]
  have hsurj : Function.Surjective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := e.toLinearMap)
      (by rw [fibre_finrank, Module.finrank_fintype_fun_eq_card, ZMod.card])).mp hinj
  refine ⟨AlgEquiv.ofBijective e ⟨hinj, hsurj⟩, fun g y h => ?_⟩
  change h0' (fibreActHom P (Multiplicative.ofAdd h) (fibreActHom P g y)) =
    h0' (fibreActHom P (Multiplicative.ofAdd (h + Multiplicative.toAdd g)) y)
  rw [← AlgEquiv.mul_apply, ← map_mul]
  rfl

/-- Otherwise the fibre algebra is a field. -/
theorem fibre_field (i : ZMod 3)
    (hi : ((geomLift P).val : GroupAlgebra Kb) i ∉ Set.range (algebraMap ℚ Kb)) :
    IsField (Fibre P) := by
  set y := ((geomLift P).val : GroupAlgebra Kb) i
  have hy : IsAlgebraic ℚ y := Algebra.IsAlgebraic.isAlgebraic y
  have hsep : (minpoly ℚ y).Separable := Algebra.IsSeparable.isSeparable ℚ y
  have hsplit : ((minpoly ℚ y).map (algebraMap ℚ Kb)).Splits := IsAlgClosed.splits _
  have hdeg : 2 ≤ (minpoly ℚ y).natDegree := (minpoly.two_le_natDegree_iff hy.isIntegral).mpr hi
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := Kb) hsep hsplit
  obtain ⟨x, hx, hxy⟩ : ∃ x ∈ (minpoly ℚ y).rootSet Kb, x ≠ y := by
    by_contra hno
    push_neg at hno
    have : ((minpoly ℚ y).rootSet Kb).toFinset.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Set.mem_toFinset] at ha hb
      rw [hno a ha, hno b hb]
    rw [Set.toFinset_card, hcard] at this
    omega
  have hev : Polynomial.aeval x (minpoly ℚ y) = 0 := (Polynomial.mem_rootSet.mp hx).2
  obtain ⟨τ, hτ⟩ := minpoly.exists_algEquiv_of_root' hy hev
  obtain ⟨j, hj⟩ := galois_geomHom P τ
  have hj0 : j ≠ 0 := by
    rintro rfl
    have := hj (fibreCoord P i)
    rw [geomHom_coord, sub_zero] at this
    exact hxy (hτ.symm.trans this)
  have hj2 : ∀ s, τ (τ (geomHom P 0 s)) = geomHom P (j + j) s := by
    intro s
    have hmul : fibreActHom P (Multiplicative.ofAdd j) (fibreActHom P (Multiplicative.ofAdd j) s) =
        fibreActHom P (Multiplicative.ofAdd (j + j)) s := by
      rw [← AlgEquiv.mul_apply, ← map_mul]
      rfl
    calc τ (τ (geomHom P 0 s)) = τ (geomHom P j s) := by rw [hj]
      _ = τ (geomHom P 0 (fibreActHom P (Multiplicative.ofAdd j) s)) := by rw [geomHom_act]
      _ = geomHom P j (fibreActHom P (Multiplicative.ofAdd j) s) := by rw [hj]
      _ = geomHom P 0 (fibreActHom P (Multiplicative.ofAdd j)
            (fibreActHom P (Multiplicative.ofAdd j) s)) := by rw [geomHom_act]
      _ = geomHom P (j + j) s := by rw [hmul, geomHom_act]
  have hinj : Function.Injective (geomHom P 0) := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    apply geomHom_joint P s
    intro k
    have hk : ∀ j : ZMod 3, j ≠ 0 → ∀ k : ZMod 3, k = 0 ∨ k = j ∨ k = j + j := by decide
    rcases hk j hj0 k with rfl | rfl | rfl
    · exact hs
    · rw [← hj, hs, map_zero]
    · rw [← hj2, hs, map_zero, map_zero]
  haveI : IsDomain (Fibre P) := Function.Injective.isDomain (geomHom P 0).toRingHom hinj
  haveI : Algebra.IsIntegral ℚ (Fibre P) := Algebra.IsIntegral.of_finite ℚ (Fibre P)
  exact (Algebra.IsIntegral.isField_iff_isField (algebraMap ℚ (Fibre P)).injective).mp
    (Field.toIsField ℚ)

/-- The fibre algebra is a `C₃`-algebra: the torsor property of the cover. -/
theorem fibre_model : (IsField (Fibre P) ∧ finrank ℚ (Fibre P) = 3 ∧
      Function.Injective (fibreActHom P)) ∨
    ∃ e : Fibre P ≃ₐ[ℚ] (ZMod 3 → ℚ), ∀ (g : C3) (y : Fibre P) (h : ZMod 3),
      e (fibreActHom P g y) h = e y (h + Multiplicative.toAdd g) := by
  by_cases hrat : ∀ i, ((geomLift P).val : GroupAlgebra Kb) i ∈ Set.range (algebraMap ℚ Kb)
  · exact Or.inr (fibre_split P hrat)
  · push_neg at hrat
    obtain ⟨i, hi⟩ := hrat
    exact Or.inl ⟨fibre_field P i hi, fibre_finrank P, fibreActHom_injective P⟩

/-- The `C₃`-algebra `γ₁(P)`. -/
def fibreAlg : C3Alg where
  carrier := Fibre P
  act := fibreActHom P
  model := fibre_model P

theorem fibreAct_xbar (g : C3) :
    (fibreAlg P).act g (fibreCoord P 0) = fibreCoord P (-Multiplicative.toAdd g) := by
  change fibreActHom P g _ = _
  rw [← ofAdd_toAdd g, fibreActHom_coord, zero_sub, toAdd_ofAdd]

theorem fibre_normal : IsNormal (fibreAlg P) (fibreCoord P 0) := by
  rw [IsNormal]
  have heq : (fun g : C3 => (fibreAlg P).act g (fibreCoord P 0)) =
      fibreCoord P ∘ (fun g : C3 => -Multiplicative.toAdd g) := by
    funext g
    exact fibreAct_xbar P g
  rw [heq]
  exact (fibreCoord_linearIndependent P).comp _ (fun a b h => by simpa using h)

theorem coord_sum : coord 0 + coord 1 + coord 2 = 1 := by
  have h := trace_one CoverAlg universalUnit
  rw [universalUnit_apply, universalUnit_apply, universalUnit_apply] at h
  exact h

theorem fibre_traceOne : HasTraceOne (fibreAlg P) (fibreCoord P 0) := by
  rw [HasTraceOne, sum_C3]
  simp only [fibreAct_xbar, toAdd_one, neg_zero]
  rw [show -(Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))) = 2 by decide,
    show -(Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 3))) = 1 by decide]
  change fibreMk P (coord 0) + fibreMk P (coord 2) + fibreMk P (coord 1) = 1
  rw [← map_add, ← map_add, show coord 0 + coord 2 + coord 1 = coord 0 + coord 1 + coord 2 by ring,
    coord_sum, map_one]

/-- The pair `γ₁(P) = (A ⊗_{A^G,P} ℚ, X̄₁)`. -/
def fibrePair : Pair := ⟨fibreAlg P, fibreCoord P 0, fibre_normal P, fibre_traceOne P⟩

/-- `γ₂(γ₁(P)) = P`. -/
theorem point_fibrePair : point (fibrePair P) = P := by
  have hunit : unitOf (fibrePair P) = mapUnits (fibreMk P).toRingHom universalUnit := by
    apply Subtype.ext
    apply Units.ext
    ext i
    rw [unitOf_val, unitElement_apply]
    refine Eq.trans ?_ (mapUnits_coefficient (fibreMk P).toRingHom universalUnit i).symm
    rw [universalUnit_apply]
    change (fibreAlg P).act _ (fibreCoord P 0) = fibreCoord P i
    rw [fibreAct_xbar, toAdd_ofAdd, neg_neg]
  apply AlgHom.ext
  intro b
  apply (algebraMap ℚ (Fibre P)).injective
  change algebraMap ℚ (fibrePair P).algebra.carrier (point (fibrePair P) b) = _
  rw [algebraMap_point, pointOver, hunit]
  have h := congrArg (fun φ : quotientFixedRing →ₐ[ℚ] Fibre P => φ b)
    (quotientPoint_mapUnits CoverAlg (fibreMk P) universalUnit)
  simp only at h
  change quotientPoint (Fibre P) _ b = _
  rw [h, AlgHom.comp_apply]
  have hU : quotientPoint CoverAlg universalUnit b = quotientInclusion b := by
    change rationalCoverPointEquiv CoverAlg universalUnit (quotientInclusion b) = _
    rw [universalUnit, Equiv.apply_symm_apply]
    rfl
  rw [hU, fibreMk_inclusion]

end Cubic.OrbitParametrization.C3Algebra
