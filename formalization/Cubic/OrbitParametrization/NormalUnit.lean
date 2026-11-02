import Cubic.OrbitParametrization.C3AlgebraBasic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Cubic.OrbitParametrization.CyclicGroupAlgebraMaps

/-!
# Normal elements and units of the group algebra ([O'Desky–Rosen, Lemma 2.2])

For an element `x` of a `C₃`-algebra `K`, the paper's element
`u = x[1] + σ²x[σ] + σx[σ²]` of `K[C₃]` is a unit exactly when `x` is normal,
and its augmentation is the trace of `x`. A `ℚ`-relation among the conjugates of
`x` gives a nonzero element of `ℚ[C₃]` annihilated by `u`. Conversely, if `x` is
normal, the element `y` with `t(x·σᵏy) = δₖ₀` (where `t` is the sum of the
conjugates) exists by nondegeneracy of `t(ab)`, and `Σₖ σᵏ(y)[σᵏ]` is the
inverse of `u`.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open CyclicGroupAlgebra Module

theorem sum_C3 {M : Type*} [AddCommMonoid M] (f : C3 → M) :
    ∑ g : C3, f g = f 1 + f (Multiplicative.ofAdd 1) + f (Multiplicative.ofAdd 2) := by
  rw [← Equiv.sum_comp Multiplicative.ofAdd]
  exact Fin.sum_univ_three _

theorem coordinates_mul (R : Type*) [CommRing R] (a₀ a₁ a₂ b₀ b₁ b₂ : R) :
    coordinates R a₀ a₁ a₂ * coordinates R b₀ b₁ b₂ =
      coordinates R (a₀ * b₀ + a₁ * b₂ + a₂ * b₁) (a₀ * b₁ + a₁ * b₀ + a₂ * b₂)
        (a₀ * b₂ + a₁ * b₁ + a₂ * b₀) := by
  ext i
  fin_cases i <;>
  simp +decide [coordinates, add_mul, mul_add, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_apply] <;> ring

theorem coordinates_eq_zero {R : Type*} [CommRing R] {a₀ a₁ a₂ : R}
    (h : coordinates R a₀ a₁ a₂ = 0) : a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 := by
  have h0 := congrArg (fun f : GroupAlgebra R => f 0) h
  have h1 := congrArg (fun f : GroupAlgebra R => f 1) h
  have h2 := congrArg (fun f : GroupAlgebra R => f 2) h
  simp +decide [coordinates] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem coordinates_one (R : Type*) [CommRing R] : coordinates R 1 0 0 = 1 := by
  simp [coordinates, AddMonoidAlgebra.one_def]

variable (K : C3Alg)

/-- The generator `σ`. -/
abbrev σ : C3 := Multiplicative.ofAdd 1

/-- The paper's unit `u = x[1] + σ²x[σ] + σx[σ²]`, i.e. the coefficient of `[g]` is `g⁻¹x`. -/
def unitElement (x : K.carrier) : GroupAlgebra K.carrier :=
  coordinates K.carrier x (K.act (σ ^ 2) x) (K.act σ x)

theorem act_σ_pow_three (z : K.carrier) : K.act (σ ^ 3) z = z := by
  rw [show σ ^ 3 = (1 : C3) by decide, map_one]
  rfl

theorem act_σ_σ (z : K.carrier) : K.act σ (K.act σ z) = K.act (σ ^ 2) z := by
  rw [← AlgEquiv.mul_apply, ← map_mul, pow_two]

theorem act_σ_σ2 (z : K.carrier) : K.act σ (K.act (σ ^ 2) z) = z := by
  rw [← AlgEquiv.mul_apply, ← map_mul, ← pow_succ', act_σ_pow_three]

theorem act_σ2_σ (z : K.carrier) : K.act (σ ^ 2) (K.act σ z) = z := by
  rw [← AlgEquiv.mul_apply, ← map_mul, ← pow_succ, act_σ_pow_three]

theorem act_σ2_σ2 (z : K.carrier) : K.act (σ ^ 2) (K.act (σ ^ 2) z) = K.act σ z := by
  rw [← AlgEquiv.mul_apply, ← map_mul, ← pow_add,
    show σ ^ (2 + 2) = σ by decide]

theorem traceSum_eq (z : K.carrier) : traceSum K z = z + K.act σ z + K.act (σ ^ 2) z := by
  rw [traceSum, sum_C3, map_one, show (Multiplicative.ofAdd (2 : ZMod 3)) = σ ^ 2 by decide]
  rfl

theorem augmentation_unitElement (x : K.carrier) :
    augmentation K.carrier (unitElement K x) = traceSum K x := by
  rw [unitElement, ← coordinates_coefficients K.carrier (coordinates K.carrier _ _ _),
    augmentation_coefficients, traceSum_eq]
  simp +decide [coordinates]
  ring

/-- A unit `u` forces `x` to be normal. -/
theorem normal_of_isUnit (x : K.carrier) (h : IsUnit (unitElement K x)) : IsNormal K x := by
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
  have hw : unitElement K x * coordinates K.carrier (algebraMap ℚ K.carrier (c 1)) (algebraMap ℚ K.carrier (c σ))
      (algebraMap ℚ K.carrier (c (σ ^ 2))) = 0 := by
    rw [unitElement, coordinates_mul]
    have e0 : x * algebraMap ℚ K.carrier (c 1) + K.act (σ ^ 2) x * algebraMap ℚ K.carrier (c (σ ^ 2)) + K.act σ x * algebraMap ℚ K.carrier (c σ) = 0 := by
      linear_combination hR
    have e1 : x * algebraMap ℚ K.carrier (c σ) + K.act (σ ^ 2) x * algebraMap ℚ K.carrier (c 1) + K.act σ x * algebraMap ℚ K.carrier (c (σ ^ 2)) = 0 := by
      linear_combination hR2
    have e2 : x * algebraMap ℚ K.carrier (c (σ ^ 2)) + K.act (σ ^ 2) x * algebraMap ℚ K.carrier (c σ) + K.act σ x * algebraMap ℚ K.carrier (c 1) = 0 := by
      linear_combination hR1
    rw [e0, e1, e2]
    simp [coordinates]
  obtain ⟨h0, h1, h2⟩ := coordinates_eq_zero ((h.mul_right_eq_zero).mp hw)
  have hinj := (algebraMap ℚ K.carrier).injective
  intro g
  have hg : g = 1 ∨ g = σ ∨ g = σ ^ 2 := by
    revert g
    decide
  rcases hg with rfl | rfl | rfl
  · exact hinj (h0.trans (map_zero _).symm)
  · exact hinj (h1.trans (map_zero _).symm)
  · exact hinj (h2.trans (map_zero _).symm)

theorem traceSum_act (h : C3) (z : K.carrier) : traceSum K (K.act h z) = traceSum K z := by
  simp only [traceSum, ← AlgEquiv.mul_apply, ← map_mul]
  exact Fintype.sum_bijective (· * h) (Group.mulRight_bijective h) _ _ (fun _ => rfl)

theorem traceSum_add (y z : K.carrier) : traceSum K (y + z) = traceSum K y + traceSum K z := by
  simp [traceSum, Finset.sum_add_distrib]

theorem traceSum_smul (q : ℚ) (z : K.carrier) : traceSum K (q • z) = q • traceSum K z := by
  simp [traceSum, Finset.smul_sum]

/-- The trace as a `ℚ`-valued linear functional. -/
def ratTrace : K.carrier →ₗ[ℚ] ℚ where
  toFun z := (traceSum_rational K z).choose
  map_add' y z := by
    apply (algebraMap ℚ K.carrier).injective
    rw [map_add, (traceSum_rational K _).choose_spec, (traceSum_rational K _).choose_spec,
      (traceSum_rational K _).choose_spec, traceSum_add]
  map_smul' q z := by
    apply (algebraMap ℚ K.carrier).injective
    rw [RingHom.id_apply, smul_eq_mul, map_mul, (traceSum_rational K _).choose_spec,
      (traceSum_rational K _).choose_spec, traceSum_smul, Algebra.smul_def]

theorem algebraMap_ratTrace (z : K.carrier) : algebraMap ℚ K.carrier (ratTrace K z) = traceSum K z :=
  (traceSum_rational K z).choose_spec

/-- The trace-dual element to a normal element. -/
theorem exists_dual (x : K.carrier) (hx : IsNormal K x) :
    ∃ y : K.carrier, traceSum K (x * y) = 1 ∧ traceSum K (x * K.act σ y) = 0 ∧
      traceSum K (x * K.act (σ ^ 2) y) = 0 := by
  let Ψ : K.carrier →ₗ[ℚ] (C3 → ℚ) :=
    LinearMap.pi fun g => (ratTrace K).comp ((LinearMap.mulLeft ℚ x).comp (K.act g).toLinearMap)
  have hspan : Submodule.span ℚ (Set.range fun g : C3 => K.act g x) = ⊤ :=
    hx.span_eq_top_of_card_eq_finrank (by rw [finrank_eq_three]; rfl)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have hzero : ∀ g : C3, traceSum K (x * K.act g y) = 0 := fun g => by
      have := congrFun (LinearMap.mem_ker.mp hy) g
      rw [← algebraMap_ratTrace]
      simpa [Ψ] using congrArg (algebraMap ℚ K.carrier) this
    have hall : ∀ b ∈ Submodule.span ℚ (Set.range fun g : C3 => K.act g x),
        traceSum K (b * y) = 0 := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨g, rfl⟩ := hb
        have := hzero g⁻¹
        rw [← traceSum_act K g, map_mul, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel,
          map_one] at this
        exact this
      | zero => simp [traceSum]
      | add a b _ _ ha hb => rw [add_mul, traceSum_add, ha, hb, add_zero]
      | smul q b _ hb => rw [smul_mul_assoc, traceSum_smul, hb, smul_zero]
    by_contra hy0
    obtain ⟨b, hb⟩ := pairing_nondegenerate K y hy0
    apply hb
    rw [mul_comm]
    exact hall b (hspan ▸ Submodule.mem_top)
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_eq_three, Module.finrank_fintype_fun_eq_card]; rfl)).mp hinj
  obtain ⟨y, hy⟩ := hsurj (Pi.single 1 1)
  have hval : ∀ g : C3, traceSum K (x * K.act g y) =
      algebraMap ℚ K.carrier ((Pi.single (1 : C3) (1 : ℚ) : C3 → ℚ) g) :=
    fun g => by
      rw [← hy, ← algebraMap_ratTrace]
      rfl
  refine ⟨y, ?_, ?_, ?_⟩
  · have := hval 1
    rw [map_one] at this
    simpa using this
  · have := hval σ
    rwa [Pi.single_eq_of_ne (by decide : (σ : C3) ≠ 1), map_zero] at this
  · have := hval (σ ^ 2)
    rwa [Pi.single_eq_of_ne (by decide : (σ ^ 2 : C3) ≠ 1), map_zero] at this

/-- A normal element gives a unit (the converse of `normal_of_isUnit`). -/
theorem isUnit_of_normal (x : K.carrier) (hx : IsNormal K x) : IsUnit (unitElement K x) := by
  obtain ⟨y, h0, h1, h2⟩ := exists_dual K x hx
  refine IsUnit.of_mul_eq_one (coordinates K.carrier y (K.act σ y) (K.act (σ ^ 2) y)) ?_
  rw [unitElement, coordinates_mul, ← coordinates_one]
  rw [traceSum_eq] at h0 h1 h2
  simp only [map_mul, act_σ_σ, act_σ_σ2, act_σ2_σ, act_σ2_σ2] at h0 h1 h2
  congr 1
  · linear_combination h0
  · linear_combination h1
  · linear_combination h2

theorem isUnit_iff_normal (x : K.carrier) : IsUnit (unitElement K x) ↔ IsNormal K x :=
  ⟨normal_of_isUnit K x, isUnit_of_normal K x⟩

/-- The coefficient of `[i]` in `u` is `σ^{-i} x`. -/
theorem unitElement_apply (x : K.carrier) (i : ZMod 3) :
    unitElement K x i = K.act (Multiplicative.ofAdd (-i)) x := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
  rcases hi with rfl | rfl | rfl
  · rw [show Multiplicative.ofAdd (-(0 : ZMod 3)) = (1 : C3) by decide, map_one]
    simp +decide [unitElement, coordinates]
  · rw [show Multiplicative.ofAdd (-(1 : ZMod 3)) = σ ^ 2 by decide]
    simp +decide [unitElement, coordinates]
  · rw [show Multiplicative.ofAdd (-(2 : ZMod 3)) = σ by decide]
    simp +decide [unitElement, coordinates]

/-- The augmentation-one unit of a pair. -/
def unitOf (p : Pair) : traceOneUnits p.algebra.carrier :=
  ⟨(isUnit_of_normal p.algebra p.element p.normal).unit, by
    apply Units.ext
    change augmentation _ (unitElement p.algebra p.element) = 1
    rw [augmentation_unitElement]
    exact p.traceOne⟩

theorem unitOf_val (p : Pair) :
    ((unitOf p).val : GroupAlgebra p.algebra.carrier) = unitElement p.algebra p.element := rfl

/-- The action of `C₃` on the coefficients is left multiplication by `[g]`. -/
theorem mapUnits_act (p : Pair) (h : C3) :
    mapUnits (p.algebra.act h).toRingEquiv.toRingHom (unitOf p) =
      cyclicUnits p.algebra.carrier h * unitOf p := by
  apply Subtype.ext
  apply Units.ext
  ext i
  rw [mapUnits_coefficient, unitOf_val, unitElement_apply]
  change _ = ((AddMonoidAlgebra.single (Multiplicative.toAdd h) 1 *
    unitElement p.algebra p.element : GroupAlgebra p.algebra.carrier)) i
  rw [AddMonoidAlgebra.single_mul_apply, one_mul, unitElement_apply]
  change p.algebra.act h (p.algebra.act _ p.element) = _
  rw [← AlgEquiv.mul_apply, ← map_mul]
  congr 2
  rw [← ofAdd_toAdd h, ← ofAdd_add]
  congr 1
  simp only [toAdd_ofAdd]
  abel

end Cubic.OrbitParametrization.C3Algebra
