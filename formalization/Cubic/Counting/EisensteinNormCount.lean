import Cubic.Counting.EisensteinIdealCount
import Cubic.QuadraticCorrespondence.CyclotomicNormTrace
import Mathlib.NumberTheory.NumberField.Norm

/-!
# Elements of `ℤ[ζ]` of a given norm

Supporting arithmetic for `lemma:traceZeroCoefficients`. Every element of `𝓞_E = ℤ[ζ]` is
`a + bζ` for unique integers `a, b`, of norm `a² - ab + b²`. Since `𝓞_E` is a principal
ideal domain with six units, each ideal of norm `K ≥ 1` has exactly six generators, so
`#{(a, b) : a² - ab + b² = K} = 6 · #{ideals of norm K}`.
-/

noncomputable section

namespace Cubic.Counting.EisensteinNormCount

open NumberField Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.QuadraticCorrespondence.CyclotomicCoefficients
open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinIdealCount

/-- `(a, b) ↦ a + bζ`. -/
def coord (p : ℤ × ℤ) : Integers := (p.1 : Integers) + (p.2 : Integers) * zetaInteger

theorem coe_coord (p : ℤ × ℤ) :
    ((coord p : Integers) : E) = algebraMap ℚ E p.1 + algebraMap ℚ E p.2 * zeta := by
  simp [coord, zetaInteger]

theorem zetaInteger_sq : zetaInteger ^ 2 = -zetaInteger - 1 := by
  apply RingOfIntegers.ext
  have hz : ((zetaInteger : Integers) : E) = zeta := rfl
  push_cast [hz]
  linear_combination zeta_relation

theorem norm_coord (p : ℤ × ℤ) :
    Algebra.norm ℤ (coord p) = p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 := by
  have h := Algebra.coe_norm_int (K := E) (coord p)
  rw [coe_coord, norm_linear, normForm] at h
  have h' : ((Algebra.norm ℤ (coord p) : ℤ) : ℚ) = ((p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 : ℤ) : ℚ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h'

theorem coord_surjective : Function.Surjective coord := by
  intro x
  have hx : x ∈ Algebra.adjoin ℤ {zetaInteger} := by
    rw [← integralPowerBasis_gen, integralPowerBasis.adjoin_gen_eq_top]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]; exact ⟨(0, 1), by simp [coord]⟩
  | algebraMap r => exact ⟨(r, 0), by simp [coord]⟩
  | add y z _ _ hy hz =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hy
    obtain ⟨⟨c, d⟩, rfl⟩ := hz
    exact ⟨(a + c, b + d), by simp [coord]; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hy
    obtain ⟨⟨c, d⟩, rfl⟩ := hz
    refine ⟨(a * c - b * d, a * d + b * c - b * d), ?_⟩
    simp only [coord, Int.cast_sub, Int.cast_add, Int.cast_mul]
    linear_combination (-(b : Integers) * d) * zetaInteger_sq

theorem coord_injective : Function.Injective coord := by
  intro p q hpq
  have h0 : coord (p - q) = 0 := by
    have : coord (p - q) = coord p - coord q := by simp [coord]; ring
    rw [this, hpq, sub_self]
  have h := norm_coord (p - q)
  rw [h0, Algebra.norm_zero] at h
  generalize hd : p - q = d at h
  obtain ⟨x, y⟩ := d
  have hx : x = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
  have hy : y = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
  subst hx hy
  exact sub_eq_zero.mp hd

/-- The integer points of norm `K`. -/
def normSet (K : ℤ) : Set (ℤ × ℤ) := {p | p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = K}

theorem normForm_nonneg (a b : ℤ) : 0 ≤ a ^ 2 - a * b + b ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

/-- `normSet K` is the set of elements generating an ideal of norm `K`. -/
def normSetEquiv (K : ℕ) :
    normSet K ≃ {α : Integers // Ideal.absNorm (Ideal.span {α}) = K} where
  toFun p := ⟨coord p.1, by
    rw [Ideal.absNorm_span_singleton, norm_coord, p.2, Int.natAbs_natCast]⟩
  invFun α := ⟨(Function.surjInv coord_surjective α.1), by
    have h := α.2
    rw [Ideal.absNorm_span_singleton, ← Function.surjInv_eq coord_surjective α.1,
      norm_coord] at h
    show _ = (K : ℤ)
    rw [← Int.natAbs_of_nonneg (normForm_nonneg _ _), h]⟩
  left_inv p := Subtype.ext (coord_injective (Function.surjInv_eq coord_surjective _))
  right_inv α := Subtype.ext (Function.surjInv_eq coord_surjective _)

instance : IsPrincipalIdealRing Integers := integers_principal

/-- The chosen generator of an ideal. -/
def gen (I : Ideal Integers) : Integers := Submodule.IsPrincipal.generator I

theorem span_gen (I : Ideal Integers) : Ideal.span {gen I} = I :=
  Ideal.span_singleton_generator I

theorem gen_associated (α : Integers) : Associated (gen (Ideal.span {α})) α :=
  Ideal.span_singleton_eq_span_singleton.mp (span_gen _)

/-- The unit relating `α` to the chosen generator of `(α)`. -/
def unitOf (α : Integers) : Integersˣ := (gen_associated α).choose

theorem gen_mul_unitOf (α : Integers) : gen (Ideal.span {α}) * unitOf α = α :=
  (gen_associated α).choose_spec

theorem span_gen_mul (I : Ideal Integers) (u : Integersˣ) : Ideal.span {gen I * u} = I := by
  rw [Ideal.span_singleton_mul_right_unit u.isUnit, span_gen]

/-- An element generating an ideal of norm `K ≠ 0` is a unit times the chosen generator. -/
def generatorEquiv (K : ℕ) (hK : K ≠ 0) :
    {α : Integers // Ideal.absNorm (Ideal.span {α}) = K} ≃
      {I : Ideal Integers // Ideal.absNorm I = K} × Integersˣ where
  toFun α := (⟨Ideal.span {α.1}, α.2⟩, unitOf α.1)
  invFun x := ⟨gen x.1.1 * x.2, by rw [span_gen_mul]; exact x.1.2⟩
  left_inv α := Subtype.ext (gen_mul_unitOf α.1)
  right_inv x := by
    obtain ⟨⟨I, hI⟩, u⟩ := x
    have hI0 : gen I ≠ 0 := by
      intro h0
      have h := span_gen I
      rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at h
      rw [← h, Ideal.absNorm_bot] at hI
      exact hK hI.symm
    refine Prod.ext (Subtype.ext (span_gen_mul I u)) ?_
    have h := gen_mul_unitOf (gen I * u)
    rw [span_gen_mul] at h
    exact Units.ext (mul_left_cancel₀ hI0 h)

theorem card_normSet (K : ℕ) (hK : K ≠ 0) :
    Nat.card (normSet K) = 6 * idealCount K := by
  rw [Nat.card_congr ((normSetEquiv K).trans (generatorEquiv K hK)), Nat.card_prod, card_units,
    idealCount, mul_comm]

theorem normSet_finite (K : ℤ) : (normSet K).Finite := by
  refine ((Set.finite_Icc (-2 * K) (2 * K)).prod (Set.finite_Icc (-2 * K) (2 * K))).subset ?_
  rintro ⟨a, b⟩ (h : a ^ 2 - a * b + b ^ 2 = K)
  have h1 := Int.le_self_sq a
  have h2 := Int.le_self_sq (-a)
  have h3 := Int.le_self_sq b
  have h4 := Int.le_self_sq (-b)
  simp only [Set.mem_prod, Set.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg (2 * a - b), sq_nonneg (2 * b - a)]

end Cubic.Counting.EisensteinNormCount
