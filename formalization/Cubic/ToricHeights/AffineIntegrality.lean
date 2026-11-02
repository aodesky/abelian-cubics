import Cubic.ToricHeights.AffineC3Invariants
import CubicTargets.ToricHeights.AffineIntegrality
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# `lemma:affineIntegrality`

Paper route. The generation identity is `eqn:affineC3invariants`. The invariant `δ`
satisfies the monic quadratic
`δ² - (e₂ - 3e₃)δ + (e₂³ + e₃ - 6e₂e₃ + 9e₃²) = 0`
(the dehomogenization, `e₁ = 1`, of `δ + δ' = e₁e₂ - 3e₃`,
`δδ' = e₂³ + e₁³e₃ - 6e₁e₂e₃ + 9e₃²` with `δ' = XY² + YZ² + ZX²`; the paper states only that
such a quadratic exists). If `e₂(P), e₃(P) ∈ ℤ`, then `δ(P)` is a rational number integral
over `ℤ`, hence an integer because `ℤ` is integrally closed. By the generation identity every
invariant is a polynomial over `ℤ` in `e₂, e₃, δ`, so it is `ℤ`-valued at `P`: this is
`D₀`-integrality. The converse holds because `e₂, e₃` are invariants.
-/

noncomputable section

namespace Cubic.ToricHeights.AffineIntegrality

open MvPolynomial AffineInvariantRing AffineChartInvariants

/-- The monic quadratic satisfied by `δ` over `ℤ[e₂, e₃]`. -/
theorem delta_quadratic :
    delta ^ 2 - (e2 - 3 * e3) * delta + (e2 ^ 3 + e3 - 6 * e2 * e3 + 9 * e3 ^ 2) = 0 := by
  simp only [delta, e2, e3, linearPolynomial, thirdCoordinate]
  ring

/-- A rational root of a monic integer quadratic is an integer. -/
theorem int_of_monic_quadratic (q : ℚ) (u v : ℤ) (h : q ^ 2 + u * q + v = 0) :
    ∃ z : ℤ, q = z := by
  have hint : IsIntegral ℤ q := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C u * Polynomial.X + Polynomial.C v, ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow]
      simpa using h
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨z, by simpa using hz.symm⟩

theorem «lemma:affineIntegrality» : CubicTargets.ToricHeights.AffineIntegrality.Claim := by
  have hgen := AffineC3Invariants.«eqn:affineC3invariants»
  refine ⟨hgen, fun P => ⟨fun hP => ⟨hP _, hP _⟩, ?_⟩⟩
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  -- `δ(P)` is an integer
  have hδ : ∃ z : ℤ, P ⟨delta, delta_mem⟩ = z := by
    have hq : (⟨delta, delta_mem⟩ : invariants) ^ 2 -
        (⟨e2, e2_mem⟩ - 3 * ⟨e3, e3_mem⟩) * ⟨delta, delta_mem⟩ +
        ((⟨e2, e2_mem⟩ : invariants) ^ 3 + ⟨e3, e3_mem⟩ - 6 * ⟨e2, e2_mem⟩ * ⟨e3, e3_mem⟩ +
          9 * (⟨e3, e3_mem⟩ : invariants) ^ 2) = 0 :=
      Subtype.ext delta_quadratic
    have h := congrArg P hq
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, ha, hb] at h
    exact int_of_monic_quadratic _ (-(a - 3 * b)) (a ^ 3 + b - 6 * a * b + 9 * b ^ 2)
      (by push_cast; linear_combination h)
  -- every invariant is a polynomial in `e₂, e₃, δ`
  intro f
  have hf : f.val ∈ Algebra.adjoin ℤ ({e2, e3, delta} : Set ChartRing) := hgen ▸ f.property
  obtain ⟨g, hg⟩ := f
  simp only at hf
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩
    · exact hδ
  | algebraMap r =>
    refine ⟨r, ?_⟩
    have : (⟨algebraMap ℤ ChartRing r, hg⟩ : invariants) = (r : invariants) := by
      apply Subtype.ext; simp
    rw [this, map_intCast]
  | add x y hx hy ihx ihy =>
    obtain ⟨zx, hzx⟩ := ihx (hgen.ge hx)
    obtain ⟨zy, hzy⟩ := ihy (hgen.ge hy)
    refine ⟨zx + zy, ?_⟩
    have : (⟨x + y, hg⟩ : invariants) = ⟨x, hgen.ge hx⟩ + ⟨y, hgen.ge hy⟩ := rfl
    rw [this, map_add, hzx, hzy]; push_cast; rfl
  | mul x y hx hy ihx ihy =>
    obtain ⟨zx, hzx⟩ := ihx (hgen.ge hx)
    obtain ⟨zy, hzy⟩ := ihy (hgen.ge hy)
    refine ⟨zx * zy, ?_⟩
    have : (⟨x * y, hg⟩ : invariants) = ⟨x, hgen.ge hx⟩ * ⟨y, hgen.ge hy⟩ := rfl
    rw [this, map_mul, hzx, hzy]; push_cast; rfl

/-- Comparison with the torus points: a point `P ∈ T(ℚ)` (a `ℚ`-algebra map on the
quotient torus ring) gives the rational point `P ∘ restriction` of `S ∖ D₀`, and the
all-invariants integrality `AffineInvariantRing.IntegralPoint P` is exactly
`D₀`-integrality of that point. -/
theorem integralPoint_iff_isD0Integral
    (P : Cubic.QuadraticCorrespondence.CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ) :
    IntegralPoint P ↔ IsD0Integral ((P : _ →+* ℚ).comp invariantRestriction.toRingHom) :=
  Iff.rfl

end Cubic.ToricHeights.AffineIntegrality
