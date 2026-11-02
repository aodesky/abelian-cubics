import Cubic.Counting.CyclicCubicField
import Cubic.Counting.CubicImpliesNormal
import Cubic.Counting.NormalityCriterion
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Cubic.OrbitParametrization.ModularInterpretation

/-!
# Cyclic cubics give two rational points (`lemma:reducibles`)

The proof of `lemma:reducibles`: "Each irreducible `f` contributes two points, one
for each isomorphism `C₃ ≅ Gal(ℚ(x)/ℚ)`: for either action its three roots give
equivalent pairs, whereas the two actions give inequivalent pairs." Here: for a
real root `θ` of the cyclic cubic `f`, `K = ℚ(θ)` has three automorphisms. Each of
the two identifications of `C₃` with them makes `(K,θ)` a pair (`θ` is normal by the
general criterion `lemma:normalityCriterion`); both have characteristic polynomial `f`, and they are
inequivalent.
-/

noncomputable section

namespace Cubic.Counting.CyclicFibre

open Polynomial Module
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open Cubic.QuadraticCorrespondence.CyclotomicTorusGalois Cubic.QuadraticCorrespondence.DescendedCoefficients
open Cubic.OrbitParametrization.C3Algebra CyclicCubicField

variable (a b : ℚ) (hc : HasCyclicCubicGaloisGroup (cubic a b))

/-- The root field `ℚ(θ) ⊂ ℝ`. -/
abbrev K := rootField a b hc

instance : FiniteDimensional ℚ (K a b hc) :=
  Module.finite_of_finrank_pos (by rw [rootField_finrank]; norm_num)

theorem isSplittingField : (cubic a b).IsSplittingField ℚ (K a b hc) := by
  have hsplit := CyclicPolynomialRealRoots.splits_real hc
  change (cubic a b).IsSplittingField ℚ (rootField a b hc)
  rw [rootField_eq]
  exact IntermediateField.adjoin_rootSet_isSplittingField hsplit

instance : Normal ℚ (K a b hc) :=
  haveI := isSplittingField a b hc
  Normal.of_isSplittingField (cubic a b)

instance : IsGalois ℚ (K a b hc) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

theorem card_aut : Nat.card ((K a b hc) ≃ₐ[ℚ] (K a b hc)) = 3 := by
  rw [IsGalois.card_aut_eq_finrank, rootField_finrank]

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- An identification of the automorphism group with `C₃`. -/
def autEquiv : ((K a b hc) ≃ₐ[ℚ] (K a b hc)) ≃* C3 :=
  mulEquivOfPrimeCardEq (card_aut a b hc) (by rw [Nat.card_eq_fintype_card]; rfl)

/-- The two actions: `C₃ ≅ Aut(K)` and its composite with inversion. -/
def act (s : Bool) : C3 →* ((K a b hc) ≃ₐ[ℚ] (K a b hc)) :=
  if s then (autEquiv a b hc).symm.toMonoidHom
  else (autEquiv a b hc).symm.toMonoidHom.comp (invMonoidHom (α := C3))

theorem act_injective (s : Bool) : Function.Injective (act a b hc s) := by
  cases s
  · intro g h hgh
    simp only [act, Bool.false_eq_true, if_false, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, invMonoidHom_apply] at hgh
    exact inv_injective ((autEquiv a b hc).symm.injective hgh)
  · exact (autEquiv a b hc).symm.injective

/-- The generator `θ` of `K`. -/
def θ : K a b hc := IntermediateField.AdjoinSimple.gen ℚ (realRoot a b hc)

theorem aut_eq_one_of_fixes (τ : (K a b hc) ≃ₐ[ℚ] (K a b hc)) (hτ : τ (θ a b hc) = θ a b hc) :
    τ = 1 := by
  have h : τ.toAlgHom = (1 : (K a b hc) ≃ₐ[ℚ] (K a b hc)).toAlgHom := by
    apply IntermediateField.algHom_ext_of_eq_adjoin (S := rootField a b hc)
      (s := {realRoot a b hc}) (hS := rfl)
    intro x hx
    obtain rfl : x = realRoot a b hc := hx
    exact hτ
  exact AlgEquiv.ext fun z => congrArg (fun φ : (K a b hc) →ₐ[ℚ] (K a b hc) => φ z) h

/-- `K` with the `C₃`-action `act s`. -/
def alg (s : Bool) : C3Alg where
  carrier := K a b hc
  commRing := (inferInstance : CommRing (K a b hc))
  algebra := (inferInstance : Algebra ℚ (K a b hc))
  act := act a b hc s
  model := Or.inl ⟨Field.toIsField _, rootField_finrank a b hc, act_injective a b hc s⟩

theorem act_bijective (s : Bool) : Function.Bijective (act a b hc s) :=
  (Nat.bijective_iff_injective_and_card _).mpr ⟨act_injective a b hc s, by
    rw [card_aut, Nat.card_eq_fintype_card]; rfl⟩

theorem cubic_nextCoeff : (cubic a b).nextCoeff = -1 := by
  rw [nextCoeff, cubic_natDegree, if_neg (by norm_num)]
  simp [cubic, coeff_X_pow]

theorem trace_θ (s : Bool) : traceSum (alg a b hc s) (θ a b hc) = 1 := by
  change ∑ g : C3, act a b hc s g (θ a b hc) = 1
  rw [(act_bijective a b hc s).sum_comp (fun τ => τ (θ a b hc)),
    ← trace_eq_sum_automorphisms]
  change algebraMap ℚ (K a b hc) (Algebra.trace ℚ (IntermediateField.adjoin ℚ {realRoot a b hc})
    (IntermediateField.AdjoinSimple.gen ℚ (realRoot a b hc))) = 1
  rw [trace_adjoinSimpleGen (isIntegral_realRoot a b hc),
    minpoly_realRoot, cubic_nextCoeff, neg_neg, map_one]

theorem act_σ_ne (s : Bool) : act a b hc s σ (θ a b hc) ≠ θ a b hc := by
  intro h
  have := act_injective a b hc s ((aut_eq_one_of_fixes a b hc _ h).trans (map_one _).symm)
  exact absurd this (by decide)

/-- The actual multiplication characteristic polynomial of the field generator. -/
theorem θ_charpoly : (LinearMap.mul ℚ (K a b hc) (θ a b hc)).charpoly = cubic a b := by
  let pb := IntermediateField.adjoin.powerBasis (isIntegral_realRoot a b hc)
  have hgen : θ a b hc = pb.gen := (IntermediateField.adjoin.powerBasis_gen _).symm
  rw [hgen, ← (LinearMap.mul ℚ (K a b hc) pb.gen).charpoly_toMatrix pb.basis]
  change (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = _
  rw [charpoly_leftMulMatrix pb]
  change minpoly ℚ (IntermediateField.AdjoinSimple.gen ℚ (realRoot a b hc)) = _
  rw [IntermediateField.minpoly_gen, minpoly_realRoot]

/-- Apply the general normality criterion. For the rational-coefficient extension
of the paper's integer count, distinct real conjugates show `1-3a ≠ 0`. -/
theorem θ_normal (s : Bool) : IsNormal (alg a b hc s) (θ a b hc) := by
  have hc' : (LinearMap.mul ℚ (alg a b hc s).carrier (θ a b hc)).charpoly =
      X ^ 3 - C (1 : ℚ) * X ^ 2 + C a * X - C (-b) := by
    simpa [cubic] using θ_charpoly a b hc
  apply (NormalityCriterion.«lemma:normalityCriterion» (alg a b hc s)
    (θ a b hc) 1 a (-b) hc').mpr
  by_cases haInt : ∃ m : ℤ, (m : ℚ) = a
  · obtain ⟨m, rfl⟩ := haInt
    norm_num only [one_pow, one_mul]
    have h : (1 : ℤ) - 3 * m ≠ 0 := by omega
    exact_mod_cast h
  have he2 := congrArg (rootField a b hc).val
    (NormalityCriterion.coefficients (alg a b hc s) (θ a b hc) 1 a (-b) hc').2
  let u : ℝ := (θ a b hc : K a b hc)
  let v : ℝ := (act a b hc s σ (θ a b hc) : K a b hc)
  let w : ℝ := (act a b hc s (σ ^ 2) (θ a b hc) : K a b hc)
  have he2R : u * v + v * w + w * u = (a : ℝ) := by
    simpa only [Cubic.OrbitParametrization.secondCoeff, map_add, map_mul,
      AlgHom.commutes] using he2
  have hsum : u + v + w = 1 := by
    have h := congrArg (rootField a b hc).val (trace_θ a b hc s)
    simpa only [traceSum_eq, map_add, map_one] using h
  have hne : u ≠ v := fun h => act_σ_ne a b hc s (Subtype.ext h.symm)
  have hdet := conjugates_det_neg_of_trace_one u v w hsum hne
  rw [conjugates_det_of_trace_one u v w hsum] at hdet
  change 3 * (u * v + v * w + w * u) - 1 < 0 at hdet
  rw [he2R] at hdet
  have hnonzero : (1 : ℝ) * (1 ^ 2 - 3 * (a : ℝ)) ≠ 0 := by nlinarith
  exact_mod_cast hnonzero

/-- The pair `(K, θ)` with the action `act s`. -/
def pair (s : Bool) : Pair := ⟨alg a b hc s, θ a b hc, θ_normal a b hc s, trace_θ a b hc s⟩

theorem θ_root : Polynomial.aeval (θ a b hc) (cubic a b) = 0 := by
  apply (algebraMap (K a b hc) ℝ).injective
  rw [← Polynomial.aeval_algebraMap_apply, map_zero]
  exact realRoot_root a b hc

theorem conj_root (τ : (K a b hc) ≃ₐ[ℚ] (K a b hc)) :
    Polynomial.aeval (τ (θ a b hc)) (cubic a b) = 0 := by
  rw [show τ (θ a b hc) = τ.toAlgHom (θ a b hc) from rfl, Polynomial.aeval_algHom_apply, θ_root,
    map_zero]

theorem conj_injective (s : Bool) :
    Function.Injective (fun g : C3 => act a b hc s g (θ a b hc)) := by
  intro g h hgh
  simp only at hgh
  have : act a b hc s (h⁻¹ * g) (θ a b hc) = θ a b hc := by
    rw [map_mul, AlgEquiv.mul_apply, hgh, ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, AlgEquiv.one_apply]
  have h1 := act_injective a b hc s ((aut_eq_one_of_fixes a b hc _ this).trans (map_one _).symm)
  rw [inv_mul_eq_one] at h1
  exact h1.symm

/-- Both pairs have characteristic polynomial `f`. -/
theorem charPoly_pair (s : Bool) : characteristicPolynomial (point (pair a b hc s)) = cubic a b := by
  set P := point (pair a b hc s)
  have hprod := characteristicPolynomial_point (pair a b hc s)
  set D := characteristicPolynomial P - cubic a b
  have hD : D = C (P linearCoefficient - a) * X + C (P constantCoefficient - b) := by
    simp only [D, characteristicPolynomial, cubic, C_sub]
    ring
  have hdeg : D.natDegree < Fintype.card C3 := by
    rw [hD]
    calc _ ≤ 1 := natDegree_linear_le
      _ < _ := by decide
  have hzero : D.map (algebraMap ℚ (K a b hc)) = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (conj_injective a b hc s)
    · intro g
      rw [Polynomial.map_sub, eval_sub]
      have h1 : eval (act a b hc s g (θ a b hc))
          ((characteristicPolynomial P).map (algebraMap ℚ (K a b hc))) = 0 := by
        change eval _ ((characteristicPolynomial (point (pair a b hc s))).map
          (algebraMap ℚ (pair a b hc s).algebra.carrier)) = 0
        rw [hprod]
        have hg : g = 1 ∨ g = σ ∨ g = σ ^ 2 := by revert g; decide
        rcases hg with rfl | rfl | rfl <;>
          simp [eval_mul, eval_sub, pair, alg]
      have h2 : eval (act a b hc s g (θ a b hc)) ((cubic a b).map (algebraMap ℚ (K a b hc))) = 0 := by
        rw [eval_map_algebraMap]
        exact conj_root a b hc _
      rw [h1, h2, sub_zero]
    · rwa [natDegree_map]
  have := Polynomial.map_injective (algebraMap ℚ (K a b hc)) (algebraMap ℚ _).injective
    (hzero.trans (Polynomial.map_zero _).symm)
  exact sub_eq_zero.mp this

/-- The automorphisms of `C₃` are the identity and inversion. -/
theorem aut_C3 (φ : C3 →* C3) (hφ : Function.Injective φ) :
    (∀ g, φ g = g) ∨ (∀ g, φ g = g⁻¹) := by
  have hg : ∀ g : C3, g = σ ^ (Multiplicative.toAdd g).val := by decide
  have hσ : φ σ ≠ 1 := fun h => absurd (hφ (h.trans (map_one φ).symm)) (by decide)
  have key : ∀ x : C3, x ≠ 1 → (∀ g : C3, x ^ (Multiplicative.toAdd g).val = g) ∨
      (∀ g : C3, x ^ (Multiplicative.toAdd g).val = g⁻¹) := by decide
  rcases key (φ σ) hσ with h | h
  · left; intro g; rw [hg g, map_pow, h, ← hg]
  · right; intro g; rw [hg g, map_pow, h, ← hg]

/-- The two pairs give distinct points. -/
theorem point_pair_ne : point (pair a b hc true) ≠ point (pair a b hc false) := by
  intro h
  obtain ⟨e, he, hex⟩ := equivalent_of_point_eq _ _ h
  let e' : (K a b hc) ≃ₐ[ℚ] (K a b hc) := e
  have he1 : e' = 1 := aut_eq_one_of_fixes a b hc e' hex
  have hid : ∀ y, e' y = y := fun y => by rw [he1, AlgEquiv.one_apply]
  have hact : act a b hc true σ = act a b hc false σ := by
    ext y
    have := he σ y
    change e' (act a b hc true σ y) = act a b hc false σ (e' y) at this
    rw [hid, hid] at this
    exact congrArg Subtype.val this
  simp only [act, if_true, Bool.false_eq_true, if_false, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, invMonoidHom_apply] at hact
  exact absurd ((autEquiv a b hc).symm.injective hact) (by decide)

/-- Every point with characteristic polynomial `f` is one of the two. -/
theorem point_mem (q : Pair) (hq : characteristicPolynomial (point q) = cubic a b) :
    point q = point (pair a b hc true) ∨ point q = point (pair a b hc false) := by
  -- `x` is a root of `f`
  have hroot : Polynomial.aeval q.element (cubic a b) = 0 := by
    have h := characteristicPolynomial_point q
    rw [hq] at h
    have := congrArg (Polynomial.eval q.element) h
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at this
    rwa [eval_map_algebraMap] at this
  -- the field `K` maps isomorphically onto `Kq`, `θ ↦ x`
  have hθ := isIntegral_realRoot a b hc
  have hev : (minpoly ℚ (realRoot a b hc)).eval₂ (Algebra.ofId ℚ q.algebra.carrier) q.element = 0 := by
    rw [minpoly_realRoot, ← hroot, aeval_def]
    rfl
  let φ : (K a b hc) →ₐ[ℚ] q.algebra.carrier :=
    (AdjoinRoot.liftAlgHom (minpoly ℚ (realRoot a b hc)) (Algebra.ofId ℚ q.algebra.carrier)
      q.element hev).comp
      (IntermediateField.adjoinRootEquivAdjoin ℚ hθ).symm.toAlgHom
  have hφθ : φ (θ a b hc) = q.element := by
    change AdjoinRoot.liftAlgHom _ _ q.element hev ((IntermediateField.adjoinRootEquivAdjoin ℚ hθ).symm
      (IntermediateField.AdjoinSimple.gen ℚ (realRoot a b hc))) = q.element
    rw [IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.liftAlgHom_root]
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (by rw [rootField_finrank, finrank_eq_three])).mp hφinj
  let e0 : q.algebra.carrier ≃ₐ[ℚ] (K a b hc) := (AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm
  have he0x : e0 q.element = θ a b hc := by
    rw [← hφθ]
    exact (AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm_apply_apply _
  -- the transported action
  let act'' : C3 →* ((K a b hc) ≃ₐ[ℚ] (K a b hc)) :=
    { toFun := fun g => (e0.symm.trans (q.algebra.act g)).trans e0
      map_one' := by
        ext y
        simp only [AlgEquiv.trans_apply, map_one, AlgEquiv.one_apply, AlgEquiv.apply_symm_apply]
      map_mul' := fun g h => by
        ext y
        simp only [AlgEquiv.trans_apply, map_mul, AlgEquiv.mul_apply, AlgEquiv.symm_apply_apply] }
  have hqinj : Function.Injective q.algebra.act := by
    intro g h hgh
    exact q.normal.injective (by simp only [hgh])
  have hinj'' : Function.Injective act'' := by
    intro g h hgh
    apply hqinj
    ext y
    have := congrArg (fun τ : (K a b hc) ≃ₐ[ℚ] (K a b hc) => e0.symm (τ (e0 y))) hgh
    simpa only [act'', MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.trans_apply,
      AlgEquiv.symm_apply_apply] using this
  have hequiv : ∀ s : Bool, (∀ g, act'' g = act a b hc s g) →
      point q = point (pair a b hc s) := by
    intro s hs
    apply point_eq_of_equivalent
    refine ⟨e0, fun g y => ?_, he0x⟩
    change e0 (q.algebra.act g y) = act a b hc s g (e0 y)
    rw [← hs g]
    simp only [act'', MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.trans_apply,
      AlgEquiv.symm_apply_apply]
  rcases aut_C3 ((autEquiv a b hc).toMonoidHom.comp act'')
      ((autEquiv a b hc).injective.comp hinj'') with h | h
  · left
    apply hequiv true
    intro g
    have := congrArg (autEquiv a b hc).symm (h g)
    simpa [act] using this
  · right
    apply hequiv false
    intro g
    have := congrArg (autEquiv a b hc).symm (h g)
    simpa [act] using this

include hc in
/-- `lemma:reducibles`: a cyclic cubic is the characteristic polynomial of exactly two
rational points. -/
theorem fibre_card :
    Nat.card {P : quotientFixedRing →ₐ[ℚ] ℚ // characteristicPolynomial P = cubic a b} = 2 := by
  have hset : {P : quotientFixedRing →ₐ[ℚ] ℚ | characteristicPolynomial P = cubic a b} =
      {point (pair a b hc true), point (pair a b hc false)} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hP
      obtain ⟨q, rfl⟩ := point_surjective P
      exact point_mem a b hc q hP
    · rintro (rfl | rfl)
      · exact charPoly_pair a b hc true
      · exact charPoly_pair a b hc false
  change Set.ncard {P : quotientFixedRing →ₐ[ℚ] ℚ | characteristicPolynomial P = cubic a b} = 2
  rw [hset]
  exact Set.ncard_pair (point_pair_ne a b hc)

end Cubic.Counting.CyclicFibre
