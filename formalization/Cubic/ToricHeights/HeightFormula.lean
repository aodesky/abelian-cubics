import CubicTargets.ToricHeights.HeightFormula
import Cubic.ToricHeights.FormulaForNormCharacter

/-!
# Proof of `lemma:heightformula` (with `eqn:weightVectors`)

## Correspondence with the paper's proof

The paper's proof has three steps.

1. **Weight decomposition.** By [Fulton, p. 66, §3.4],
   `H⁰(S_E, 𝒪(3D₀)) ≅ ⊕_{u ∈ P ∩ M_E} E χ^u`, where `P = {u ≥ 3φ₀ on 𝔱_E}`. In the
   coordinates `u = u₁v₁^∨ + u₂v₂^∨`, `P` is the triangle `u₁, u₂ ≥ 0`, `u₁ + u₂ ≤ 3`. Its
   lattice points in `M_E = ℤa' ⊕ ℤb'` are `0, a'+b', 2a'+b', 2b'+a'`, so `h⁰ = 4`.
2. **Twisting `𝟏`.** The weight vectors are the twists `χ^u 𝟏` of `𝟏` by these characters.
3. **Formulas.** `eqn:formulaForNormCharacter(2)` express `χ^u` through `e₁, e₂, e₃, √disc`,
   which gives the displayed sections.

In the model `H⁰ = E[X,Y,Z]₃^{C₃} · e₁⁻³` (see the docstring of the target statement),
the steps become the following.

* **Step 1: weight decomposition of invariant cubics.** Use the eigen-coordinates
  `χ₀ = X+Y+Z = e₁`, `χ₁ = X+ζY+ζ²Z` and `χ₂ = X+ζ²Y+ζZ`. The substitution `toEigen` sends
  `X, Y, Z` to `χ₀, χ₁, χ₂`. It is an automorphism of `E[X,Y,Z]` with inverse `fromEigen`
  (`toEigen_fromEigen`, `fromEigen_toEigen`), and it uses `1/3 ∈ E`.
  - **Diagonal action.** The generator of `C₃` becomes diagonal: `χ₀ ↦ χ₀`, `χ₁ ↦ ζ²χ₁`,
    `χ₂ ↦ ζχ₂` (`cyclicShift_toEigen`). So `χ₀^aχ₁^bχ₂^c` is an eigenvector with eigenvalue
    `ζ^{2b+c}` (`coeff_diagShift`).
  - **Weights.** As a section, `χ₀^aχ₁^bχ₂^c e₁⁻³ = (χ₁/χ₀)^b (χ₂/χ₀)^c 𝟏`. Since
    `χ^{v_i^∨} = χ_i/χ₀`, this is the weight vector of weight `u = b v₁^∨ + c v₂^∨`.
  - **Invariance means `u ∈ M_E`.** The monomial is invariant iff `3 ∣ 2b+c`. This is the
    condition `(b,c) ∈ pullback(ℤ²) = M_E` (`CharacterLattice.mem_range_pullback`).
  - **Degree three means `u ∈ P`.** The condition `a = 3-b-c ≥ 0` is `u ∈ P`. Here `P` is
    defined as the paper's `{u ≥ 3φ₀}`, with `φ₀(n) = min(0, n₁, n₂)` in `v`-coordinates
    (`InPolytope`, `inPolytope_iff`).
  - **Lattice points.** The lattice points of `P ∩ M_E` are exactly `0, a'+b', 2a'+b', 2b'+a'`
    (`latticePoint_iff`). Hence the invariant eigen-monomials are exactly `χ₀³`, `χ₀χ₁χ₂`,
    `χ₁³`, `χ₂³` (`exists_weightExponent`).
  - **Decomposition.** Every invariant cubic is the sum of its weight components
    (`invariant_decomposition`), so the four eigen-monomials span `E[X,Y,Z]₃^{C₃}`
    (`span_eigenMonomial`). This is the model's form of `H⁰ = ⊕_{u ∈ P∩M_E} E χ^u`.
* **Step 2.** `weightSection j = sectionOf (eigenMonomial j)` is `χ^u 𝟏`. Its value at every
  point `g` is `χ^u(g)` times the value of `𝟏` (`weightSection_isWeightVector`, via
  `value_eigenMonomial`, `weightCharacter_val` and `FormulaForNormCharacter.groupCharacter_val`).
* **Step 3.** The displayed numerators equal the eigen-monomials as polynomials
  (`numerator_eq_eigenMonomial`):
  - `e₁³ - 3e₁e₂ = χ₀χ₁χ₂`, the identity behind `eqn:formulaForNormCharacter`
    (`TraceOneCharacters.eigenvalue_product`);
  - `e₁³ - 9/2 e₁e₂ + 27/2 e₃ ± √-27/2 √disc = χ₁³, χ₂³`, the identity behind
    `eqn:formulaForNormCharacter2` (`TraceOneCharacters.eigenvalue_cubes_sum`,
    `WeightVectors.eigenvalue_cubes_difference`). The `+` sign gives `χ₁³ = χ^{2a'+b'}`
    and the `-` sign gives `χ₂³ = χ^{2b'+a'}`.

  Hence `weightVector j = weightSection j` (`weightVector_eq_weightSection`), which gives the
  weight-vector property and the spanning.

**Departure from the paper (forced by the model).** Fulton's theorem is not available, because
mathlib has no toric-variety theory. It is replaced by the explicit weight decomposition of
`C₃`-invariant cubics in eigen-coordinates. That decomposition is proved here, and it
passes through the paper's `P` and its lattice points. The formulas of
`eqn:formulaForNormCharacter(2)` are used as polynomial identities in `E[X,Y,Z]`, proved from
the same generic identities as those equations. The equation labels themselves are statements
about values at points of `T_E`, so they are not quoted.
-/

noncomputable section

namespace Cubic.ToricHeights.HeightFormula

open MvPolynomial
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters
open CubicTargets.ToricHeights.HeightFormula

/-! ### Monomials -/

/-- The exponent `X^a Y^b Z^c`. -/
def mono (a b c : ℕ) : ZMod 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

private theorem z10 : (1 : ZMod 3) ≠ 0 := by decide
private theorem z20 : (2 : ZMod 3) ≠ 0 := by decide
private theorem z21 : (2 : ZMod 3) ≠ 1 := by decide

@[simp] theorem mono_zero (a b c : ℕ) : mono a b c 0 = a := by
  simp [mono, z20]

@[simp] theorem mono_one (a b c : ℕ) : mono a b c 1 = b := by
  simp [mono, z21]

@[simp] theorem mono_two (a b c : ℕ) : mono a b c 2 = c := by
  simp [mono, z20, z21]

theorem mono_self (d : ZMod 3 →₀ ℕ) : mono (d 0) (d 1) (d 2) = d := by
  ext i
  fin_cases i <;> simp

@[simp] theorem mono_eq_iff (a b c a' b' c' : ℕ) :
    mono a b c = mono a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h,
      by simpa using congrArg (· 2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem mono_degree (a b c : ℕ) : (mono a b c).degree = a + b + c := by
  simp [mono, map_add, Finsupp.degree_single]

/-- The monomial `X^a Y^b Z^c`. -/
def m (a b c : ℕ) : Poly := monomial (mono a b c) 1

theorem m_eq (a b c : ℕ) : m a b c = X 0 ^ a * X 1 ^ b * X 2 ^ c := by
  simp [m, mono, X_pow_eq_monomial, monomial_mul]

theorem m_homogeneous (a b c : ℕ) : (m a b c).IsHomogeneous (a + b + c) :=
  isHomogeneous_monomial _ (mono_degree a b c)

/-! ### The polyhedron `P` and its lattice points -/

/-- The support function `φ₀` of `D₀` in the coordinates `n = n₁v₁ + n₂v₂` of `𝔱_E`.
It is `0` on `σ₁₂`, `v₂^∨` on `σ₁₀` and `v₁^∨` on `σ₂₀`, i.e. `min(0, n₁, n₂)`. -/
def supportFunction₀ (n : ℝ × ℝ) : ℝ := min 0 (min n.1 n.2)

/-- `u = u₁v₁^∨ + u₂v₂^∨` lies in the polyhedron `P = {u ≥ 3φ₀ on 𝔱_E}`. -/
def InPolytope (u : ℤ × ℤ) : Prop :=
  ∀ n : ℝ × ℝ, 3 * supportFunction₀ n ≤ u.1 * n.1 + u.2 * n.2

/-- `P` is the triangle `u₁, u₂ ≥ 0`, `u₁ + u₂ ≤ 3`. -/
theorem inPolytope_iff (u : ℤ × ℤ) : InPolytope u ↔ 0 ≤ u.1 ∧ 0 ≤ u.2 ∧ u.1 + u.2 ≤ 3 := by
  constructor
  · intro h
    have h1 := h (1, 0)
    have h2 := h (0, 1)
    have h3 := h (-1, -1)
    norm_num [supportFunction₀] at h1 h2 h3
    refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, ?_⟩
    have : ((u.1 + u.2 : ℤ) : ℝ) ≤ 3 := by push_cast; linarith
    exact_mod_cast this
  · rintro ⟨h1, h2, h3⟩ n
    have h1' : (0 : ℝ) ≤ u.1 := by exact_mod_cast h1
    have h2' : (0 : ℝ) ≤ u.2 := by exact_mod_cast h2
    have h3' : (u.1 : ℝ) + u.2 ≤ 3 := by exact_mod_cast h3
    have hm0 : supportFunction₀ n ≤ 0 := min_le_left _ _
    have hm1 : supportFunction₀ n ≤ n.1 := (min_le_right _ _).trans (min_le_left _ _)
    have hm2 : supportFunction₀ n ≤ n.2 := (min_le_right _ _).trans (min_le_right _ _)
    nlinarith [mul_nonneg h1' (sub_nonneg.2 hm1), mul_nonneg h2' (sub_nonneg.2 hm2),
      mul_nonneg (sub_nonneg.2 h3') (neg_nonneg.2 hm0)]

/-- The characters `0, a'+b', 2a'+b', 2b'+a'` in the coordinates `(m₁, m₂)` of `m₁a' + m₂b'`. -/
def latticePoint : Fin 4 → ℤ × ℤ := ![(0, 0), (1, 1), (2, 1), (1, 2)]

/-- The lattice points of `P ∩ M_E` are exactly `0, a'+b', 2a'+b', 2b'+a'`. -/
theorem latticePoint_iff (m : ℤ × ℤ) :
    InPolytope (CharacterLattice.pullback m) ↔ ∃ j, latticePoint j = m := by
  rw [inPolytope_iff]
  obtain ⟨m₁, m₂⟩ := m
  simp only [CharacterLattice.pullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hb1 : 0 ≤ m₁ ∧ m₁ ≤ 3 := by omega
    have hb2 : 0 ≤ m₂ ∧ m₂ ≤ 3 := by omega
    obtain ⟨hl1, hu1⟩ := hb1
    obtain ⟨hl2, hu2⟩ := hb2
    interval_cases m₁ <;> interval_cases m₂ <;> first
      | omega
      | exact ⟨0, rfl⟩
      | exact ⟨1, rfl⟩
      | exact ⟨2, rfl⟩
      | exact ⟨3, rfl⟩
  · rintro ⟨j, hj⟩
    fin_cases j <;> simp [latticePoint, Prod.ext_iff] at hj <;> omega

/-- The exponents `(a,b,c)` of the invariant eigen-monomials `χ₀^aχ₁^bχ₂^c`: `(b,c)` are the
`v^∨`-coordinates of the weight `latticePoint j`, and `a = 3-b-c`. -/
def weightExponent : Fin 4 → ZMod 3 →₀ ℕ := ![mono 3 0 0, mono 1 1 1, mono 0 3 0, mono 0 0 3]

theorem pullback_latticePoint (j : Fin 4) :
    CharacterLattice.pullback (latticePoint j) =
      ((weightExponent j 1 : ℤ), (weightExponent j 2 : ℤ)) := by
  fin_cases j <;> simp [latticePoint, weightExponent, CharacterLattice.pullback]

theorem weightExponent_sum (j : Fin 4) :
    weightExponent j 0 + weightExponent j 1 + weightExponent j 2 = 3 := by
  fin_cases j <;> simp [weightExponent]

theorem weightExponent_injective : Function.Injective weightExponent := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [weightExponent]

/-- The invariant cubic eigen-monomials are those whose weight is a lattice point of `P ∩ M_E`:
if `a+b+c = 3` and `3 ∣ 2b+c`, then `(a,b,c)` is one of the four `weightExponent j`. -/
theorem exists_weightExponent {a b c : ℕ} (hdeg : a + b + c = 3) (hdvd : 3 ∣ 2 * b + c) :
    ∃ j, weightExponent j = mono a b c := by
  -- the weight `u = b v₁^∨ + c v₂^∨` lies in `M_E`
  obtain ⟨m, hm⟩ := (CharacterLattice.mem_range_pullback ((b : ℤ), (c : ℤ))).2 (by
    dsimp
    omega)
  -- and in `P`
  have hP : InPolytope (CharacterLattice.pullback m) := by
    rw [hm, inPolytope_iff]
    dsimp
    omega
  obtain ⟨j, rfl⟩ := (latticePoint_iff m).1 hP
  refine ⟨j, ?_⟩
  have h := pullback_latticePoint j
  rw [hm, Prod.mk.injEq] at h
  obtain ⟨hb, hc⟩ := h
  have hs := weightExponent_sum j
  rw [← mono_self (weightExponent j), mono_eq_iff]
  omega

/-! ### Eigen-coordinates -/

/-- `ζ` as a constant of `E[X,Y,Z]`. -/
local notation "ζ" => (C zeta : Poly)

theorem zeta_rel : ζ ^ 2 + ζ + 1 = 0 := by
  simpa using congrArg (C : E → Poly) zeta_relation

/-- `χ₁ = X + ζY + ζ²Z`. -/
def χ₁ : Poly := X 0 + ζ * X 1 + ζ ^ 2 * X 2

/-- `χ₂ = X + ζ²Y + ζZ`. -/
def χ₂ : Poly := X 0 + ζ ^ 2 * X 1 + ζ * X 2

/-- The eigen-coordinates `χ₀ = e₁`, `χ₁`, `χ₂`. -/
def eigenCoord : ZMod 3 → Poly := ![e₁, χ₁, χ₂]

/-- The linear change of variables `X, Y, Z ↦ χ₀, χ₁, χ₂`. -/
def toEigen : Poly →ₐ[E] Poly := aeval eigenCoord

/-- The inverse coordinates `(X+Y+Z)/3`, `(X+ζ²Y+ζZ)/3`, `(X+ζY+ζ²Z)/3`. -/
def fromEigenCoord : ZMod 3 → Poly :=
  ![C (1 / 3) * (X 0 + X 1 + X 2), C (1 / 3) * (X 0 + ζ ^ 2 * X 1 + ζ * X 2),
    C (1 / 3) * (X 0 + ζ * X 1 + ζ ^ 2 * X 2)]

/-- The inverse change of variables. -/
def fromEigen : Poly →ₐ[E] Poly := aeval fromEigenCoord

private theorem third : (C (1 / 3 : E) : Poly) * 3 = 1 := by
  rw [← map_ofNat C 3, ← map_mul]
  norm_num

private theorem e21 : (2 : ZMod 3) + 1 = 0 := by decide

theorem toEigen_fromEigen : toEigen.comp fromEigen = AlgHom.id E Poly := by
  have hz := zeta_rel
  have h3 := third
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;>
    simp only [AlgHom.comp_apply, AlgHom.id_apply, fromEigen, fromEigenCoord, toEigen, eigenCoord,
      aeval_X, map_mul, map_add, map_pow, aeval_C, algebraMap_eq, e₁, χ₁, χ₂, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · linear_combination C (1 / 3 : E) * (X 1 + X 2) * hz + X 0 * h3
  · linear_combination
      C (1 / 3 : E) * (X 0 + 2 * (ζ - 1) * X 1 + (ζ ^ 2 - ζ + 1) * X 2) * hz + X 1 * h3
  · linear_combination
      C (1 / 3 : E) * (X 0 + (ζ ^ 2 - ζ + 1) * X 1 + 2 * (ζ - 1) * X 2) * hz + X 2 * h3

theorem fromEigen_toEigen : fromEigen.comp toEigen = AlgHom.id E Poly := by
  have hz := zeta_rel
  have h3 := third
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;>
    simp only [AlgHom.comp_apply, AlgHom.id_apply, fromEigen, fromEigenCoord, toEigen, eigenCoord,
      aeval_X, map_mul, map_add, map_pow, aeval_C, algebraMap_eq, e₁, χ₁, χ₂, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · linear_combination C (1 / 3 : E) * (X 1 + X 2) * hz + X 0 * h3
  · linear_combination
      C (1 / 3 : E) * (X 0 + 2 * (ζ - 1) * X 1 + (ζ ^ 2 - ζ + 1) * X 2) * hz + X 1 * h3
  · linear_combination
      C (1 / 3 : E) * (X 0 + (ζ ^ 2 - ζ + 1) * X 1 + 2 * (ζ - 1) * X 2) * hz + X 2 * h3

theorem toEigen_fromEigen_apply (F : Poly) : toEigen (fromEigen F) = F :=
  congrArg (fun φ : Poly →ₐ[E] Poly => φ F) toEigen_fromEigen

theorem fromEigen_toEigen_apply (F : Poly) : fromEigen (toEigen F) = F :=
  congrArg (fun φ : Poly →ₐ[E] Poly => φ F) fromEigen_toEigen

/-- The generator of `C₃` in eigen-coordinates: `χ₀ ↦ χ₀`, `χ₁ ↦ ζ²χ₁`, `χ₂ ↦ ζχ₂`. -/
def diagShift : Poly →ₐ[E] Poly := aeval (![X 0, ζ ^ 2 * X 1, ζ * X 2] : ZMod 3 → Poly)

theorem cyclicShift_toEigen : cyclicShift.comp toEigen = toEigen.comp diagShift := by
  have hz := zeta_rel
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;>
    simp only [AlgHom.comp_apply, cyclicShift, diagShift, toEigen, eigenCoord, aeval_X,
      map_mul, map_add, map_pow, aeval_C, rename_X, rename_C, algebraMap_eq, e₁, χ₁, χ₂,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, zero_add, one_add_one_eq_two,
      e21]
  · ring
  · linear_combination (-(ζ - 1) * (X 1 + ζ * X 2)) * hz
  · linear_combination (-(ζ - 1) * X 1) * hz

/-- A linear form with constant coefficients is homogeneous of degree `1`. -/
theorem linear_homogeneous (a b c : E) :
    (C a * X 0 + C b * X 1 + C c * X 2 : Poly).IsHomogeneous 1 :=
  (((isHomogeneous_X E 0).C_mul a).add ((isHomogeneous_X E 1).C_mul b)).add
    ((isHomogeneous_X E 2).C_mul c)

theorem linear_homogeneous_of_eq {p : Poly} (a b c : E)
    (h : p = C a * X 0 + C b * X 1 + C c * X 2) : p.IsHomogeneous 1 :=
  h ▸ linear_homogeneous a b c

theorem eigenCoord_homogeneous (i : ZMod 3) : (eigenCoord i).IsHomogeneous 1 := by
  fin_cases i
  · exact linear_homogeneous_of_eq 1 1 1
      (by simp only [eigenCoord, e₁, map_one, Fin.zero_eta, Matrix.cons_val]; ring)
  · exact linear_homogeneous_of_eq 1 zeta (zeta ^ 2)
      (by simp only [eigenCoord, χ₁, map_one, map_pow, Fin.mk_one, Matrix.cons_val]; ring)
  · exact linear_homogeneous_of_eq 1 (zeta ^ 2) zeta
      (by simp only [eigenCoord, χ₂, map_one, map_pow, Fin.reduceFinMk, Matrix.cons_val]; ring)

theorem fromEigenCoord_homogeneous (i : ZMod 3) : (fromEigenCoord i).IsHomogeneous 1 := by
  fin_cases i
  · exact linear_homogeneous_of_eq (1 / 3) (1 / 3) (1 / 3)
      (by simp only [fromEigenCoord, Fin.zero_eta, Matrix.cons_val]; ring)
  · exact linear_homogeneous_of_eq (1 / 3) (1 / 3 * zeta ^ 2) (1 / 3 * zeta)
      (by simp only [fromEigenCoord, map_mul, map_pow, Fin.mk_one, Matrix.cons_val]; ring)
  · exact linear_homogeneous_of_eq (1 / 3) (1 / 3 * zeta) (1 / 3 * zeta ^ 2)
      (by simp only [fromEigenCoord, map_mul, map_pow, Fin.reduceFinMk, Matrix.cons_val]; ring)

theorem fromEigen_homogeneous {F : Poly} {n : ℕ} (hF : F.IsHomogeneous n) :
    (fromEigen F).IsHomogeneous n := by
  have h := hF.aeval fromEigenCoord fromEigenCoord_homogeneous
  rwa [one_mul] at h

/-- `χ₀^aχ₁^bχ₂^c` is an eigenvector of the generator of `C₃` with eigenvalue `ζ^{2b+c}`. -/
theorem coeff_diagShift (G : Poly) (a b c : ℕ) :
    coeff (mono a b c) (diagShift G) = zeta ^ (2 * b + c) * coeff (mono a b c) G := by
  induction G using MvPolynomial.induction_on' with
  | monomial d k =>
    rw [← mono_self d]
    have hd : monomial (mono (d 0) (d 1) (d 2)) k = C k * m (d 0) (d 1) (d 2) := by
      rw [m, C_mul_monomial, mul_one]
    have himage : diagShift (C k * m (d 0) (d 1) (d 2)) =
        C (k * zeta ^ (2 * d 1 + d 2)) * m (d 0) (d 1) (d 2) := by
      rw [m_eq]
      simp only [diagShift, map_mul, map_pow, aeval_X, aeval_C, algebraMap_eq,
        Matrix.cons_val, pow_add, pow_mul]
      ring
    rw [hd, himage, m, C_mul_monomial, C_mul_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [mono_eq_iff] at h
      obtain ⟨-, h1, h2⟩ := h
      rw [h1, h2]
      ring
    · ring
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/-! ### Weight decomposition of invariant cubics -/

/-- A cubic in eigen-coordinates that is fixed by the generator of `C₃` is the sum of its
components of weight in `P ∩ M_E`. -/
theorem eigen_decomposition {G : Poly} (hG : G.IsHomogeneous 3) (hinv : diagShift G = G) :
    G = ∑ j, coeff (weightExponent j) G • monomial (weightExponent j) (1 : E) := by
  ext d
  rw [coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hd : coeff d G = 0
  · rw [hd]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    split_ifs with h
    · rw [h, hd]
    · rfl
  · -- the exponent of a nonzero coefficient has degree `3` and weight in `M_E`
    have hdeg : d 0 + d 1 + d 2 = 3 := by
      by_contra h
      exact hd (hG.coeff_eq_zero (by rw [← mono_self d, mono_degree]; exact h))
    have hdvd : 3 ∣ 2 * d 1 + d 2 := by
      have h := coeff_diagShift G (d 0) (d 1) (d 2)
      rw [mono_self, hinv] at h
      have h1 : zeta ^ (2 * d 1 + d 2) = 1 := by
        have := mul_right_cancel₀ hd (h.symm.trans (one_mul _).symm)
        exact this
      exact (zeta_primitive.pow_eq_one_iff_dvd _).1 h1
    obtain ⟨j, hj⟩ := exists_weightExponent hdeg hdvd
    rw [mono_self] at hj
    subst hj
    rw [Finset.sum_eq_single j
      (fun k _ hk => if_neg fun h => hk (weightExponent_injective h))
      (fun h => absurd (Finset.mem_univ j) h), if_pos rfl]

/-- The eigen-monomial `χ₀^aχ₁^bχ₂^c` with `(a,b,c) = weightExponent j`, of weight
`b v₁^∨ + c v₂^∨ = latticePoint j`. -/
def eigenMonomial (j : Fin 4) : Poly := toEigen (monomial (weightExponent j) 1)

theorem toEigen_m (a b c : ℕ) : toEigen (m a b c) = e₁ ^ a * χ₁ ^ b * χ₂ ^ c := by
  rw [m_eq]
  simp [toEigen, eigenCoord]

theorem eigenMonomial_eq (j : Fin 4) :
    eigenMonomial j =
      e₁ ^ weightExponent j 0 * χ₁ ^ weightExponent j 1 * χ₂ ^ weightExponent j 2 := by
  conv_lhs => rw [eigenMonomial, ← mono_self (weightExponent j)]
  exact toEigen_m _ _ _

/-- A `C₃`-invariant cubic is the sum of its weight components. -/
theorem invariant_decomposition {F : Poly} (hF : F ∈ invariantCubics) :
    F = ∑ j, coeff (weightExponent j) (fromEigen F) • eigenMonomial j := by
  obtain ⟨hhom, hinv⟩ := hF
  change F.IsHomogeneous 3 at hhom
  change cyclicShift F = F at hinv
  have hG : diagShift (fromEigen F) = fromEigen F := by
    have h := congrArg (fun φ : Poly →ₐ[E] Poly => φ (fromEigen F)) cyclicShift_toEigen
    simp only [AlgHom.comp_apply, toEigen_fromEigen_apply, hinv] at h
    have h' := congrArg fromEigen h
    rw [fromEigen_toEigen_apply] at h'
    exact h'.symm
  conv_lhs => rw [← toEigen_fromEigen_apply F,
    eigen_decomposition (fromEigen_homogeneous hhom) hG]
  simp only [map_sum, map_smul, eigenMonomial]

theorem zeta_pow_weight (j : Fin 4) :
    zeta ^ (2 * weightExponent j 1 + weightExponent j 2) = 1 := by
  have h3 : zeta ^ 3 = 1 := zeta_primitive.pow_eq_one
  fin_cases j <;> simp [weightExponent]
  · exact h3
  · rw [show 6 = 3 * 2 by rfl, pow_mul, h3, one_pow]
  · exact h3

theorem eigenMonomial_mem (j : Fin 4) : eigenMonomial j ∈ invariantCubics := by
  refine ⟨?_, ?_⟩
  · change (eigenMonomial j).IsHomogeneous 3
    have h := (isHomogeneous_monomial (R := E) (1 : E)
      (show (weightExponent j).degree = 3 by
        rw [← mono_self (weightExponent j), mono_degree, weightExponent_sum])).aeval
      eigenCoord eigenCoord_homogeneous
    rwa [one_mul] at h
  · change cyclicShift (eigenMonomial j) = eigenMonomial j
    have hfix :
        diagShift (monomial (weightExponent j) (1 : E)) = monomial (weightExponent j) 1 := by
      ext d
      rw [← mono_self d, coeff_diagShift, coeff_monomial]
      split_ifs with h
      · have hw := zeta_pow_weight j
        rw [h, mono_one, mono_two] at hw
        rw [hw, one_mul]
      · rw [mul_zero]
    have h := congrArg (fun φ : Poly →ₐ[E] Poly => φ (monomial (weightExponent j) (1 : E)))
      cyclicShift_toEigen
    simp only [AlgHom.comp_apply, hfix] at h
    exact h

/-- The four eigen-monomials span `E[X,Y,Z]₃^{C₃}`: the model's `H⁰ = ⊕_{u ∈ P∩M_E} Eχ^u`. -/
theorem span_eigenMonomial : Submodule.span E (Set.range eigenMonomial) = invariantCubics := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact eigenMonomial_mem j
  · intro F hF
    rw [invariant_decomposition hF]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-! ### The displayed numerators are the eigen-monomials -/

local notation "s27" => Cubic.ToricHeights.WeightVectors.sqrtNegTwentySeven

/-- The numerators `e₁³`, `e₁³-3e₁e₂`, `e₁³ - 9/2 e₁e₂ + 27/2 e₃ ± √-27/2 √disc`. -/
def numerator : Fin 4 → Poly :=
  ![e₁ ^ 3, e₁ ^ 3 - (3 : E) • (e₁ * e₂),
    e₁ ^ 3 - (9 / 2 : E) • (e₁ * e₂) + (27 / 2 : E) • e₃ + (s27 / 2) • sqrtDisc,
    e₁ ^ 3 - (9 / 2 : E) • (e₁ * e₂) + (27 / 2 : E) • e₃ - (s27 / 2) • sqrtDisc]

/-- `e₁³ = χ₀³`, `e₁³-3e₁e₂ = χ₀χ₁χ₂` (`eqn:formulaForNormCharacter`) and
`e₁³ - 9/2 e₁e₂ + 27/2 e₃ ± √-27/2 √disc = χ₁³, χ₂³` (`eqn:formulaForNormCharacter2`). -/
theorem numerator_eq_eigenMonomial (j : Fin 4) : numerator j = eigenMonomial j := by
  have hz := zeta_rel
  have h2 : (C (1 / 2 : E) : Poly) * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul]
    norm_num
  have c92 : (C (9 / 2 : E) : Poly) = 9 * C (1 / 2) := by
    rw [← map_ofNat C 9, ← map_mul]
    norm_num
  have c272 : (C (27 / 2 : E) : Poly) = 27 * C (1 / 2) := by
    rw [← map_ofNat C 27, ← map_mul]
    norm_num
  have cs : (C (s27 / 2) : Poly) = 3 * (2 * ζ + 1) * C (1 / 2) := by
    have : (s27 / 2 : E) = 3 * (2 * zeta + 1) * (1 / 2) := by
      simp only [Cubic.ToricHeights.WeightVectors.sqrtNegTwentySeven, sqrtNegThree]
      ring
    rw [this]
    simp only [map_mul, map_add, map_ofNat, map_one]
  have hp := eigenvalue_product ζ hz (X 0) (X 1) (X 2)
  have hs := eigenvalue_cubes_sum ζ hz (X 0) (X 1) (X 2)
  have hd := Cubic.ToricHeights.WeightVectors.eigenvalue_cubes_difference ζ hz (X 0) (X 1) (X 2)
  unfold Cubic.OrbitParametrization.secondCoeff at hp hs
  rw [eigenMonomial_eq]
  fin_cases j <;>
    simp only [numerator, weightExponent, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, mono_zero, mono_one, mono_two, smul_eq_C_mul, map_ofNat, c92, c272, cs,
      pow_zero, pow_one, mul_one, e₁, e₂, e₃, sqrtDisc, χ₁, χ₂]
  · linear_combination (-(X 0 + X 1 + X 2)) * hp
  · linear_combination (-C (1 / 2 : E)) * hs - C (1 / 2 : E) * hd -
      ((X 0 + X 1 + X 2) ^ 3 - (X 0 + ζ * X 1 + ζ ^ 2 * X 2) ^ 3) * h2
  · linear_combination (-C (1 / 2 : E)) * hs + C (1 / 2 : E) * hd -
      ((X 0 + X 1 + X 2) ^ 3 - (X 0 + ζ ^ 2 * X 1 + ζ * X 2) ^ 3) * h2

theorem numerator_mem (j : Fin 4) : numerator j ∈ invariantCubics := by
  rw [numerator_eq_eigenMonomial]
  exact eigenMonomial_mem j

/-- The numerators span `E[X,Y,Z]₃^{C₃}`. -/
theorem span_numerator : Submodule.span E (Set.range numerator) = invariantCubics := by
  rw [show numerator = eigenMonomial from funext numerator_eq_eigenMonomial, span_eigenMonomial]

/-! ### The sections `F e₁⁻³` -/

theorem e₁_ne_zero : e₁ ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ => (1 : E))) h
  simp [e₁] at this
  norm_num at this

theorem toRatFun_injective : Function.Injective toRatFun :=
  IsFractionRing.injective Poly RatFun

theorem toRatFun_e₁_ne_zero : toRatFun e₁ ≠ 0 :=
  (map_ne_zero_iff _ toRatFun_injective).mpr e₁_ne_zero

theorem sectionOf_apply (F : Poly) : sectionOf F = toRatFun F * (toRatFun e₁)⁻¹ ^ 3 := rfl

theorem sectionOf_injective : Function.Injective sectionOf := by
  intro F G h
  rw [sectionOf_apply, sectionOf_apply] at h
  exact toRatFun_injective
    (mul_right_cancel₀ (pow_ne_zero 3 (inv_ne_zero toRatFun_e₁_ne_zero)) h)

theorem sectionOf_numerator (j : Fin 4) : sectionOf (numerator j) = weightVector j := by
  have h := toRatFun_e₁_ne_zero
  rw [sectionOf_apply]
  fin_cases j <;>
    simp only [numerator, weightVector, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, map_pow, map_sub, map_add, map_mul, Algebra.smul_def,
      AlgHom.commutes, map_ofNat, map_div₀, mul_one] <;>
    field_simp

/-- The twist `χ^u 𝟏 = χ₀^aχ₁^bχ₂^c e₁⁻³` of `𝟏` by the character `u = latticePoint j`. -/
def weightSection (j : Fin 4) : RatFun := sectionOf (eigenMonomial j)

/-- The displayed weight vectors are the twists `χ^u 𝟏`. -/
theorem weightVector_eq_weightSection (j : Fin 4) : weightVector j = weightSection j := by
  rw [weightSection, ← numerator_eq_eigenMonomial, sectionOf_numerator]

theorem span_weightVector :
    Submodule.span E (Set.range weightVector) = globalSections := by
  have h : Set.range weightVector = sectionOf '' Set.range numerator := by
    rw [← Set.range_comp]
    congr 1
    funext j
    exact (sectionOf_numerator j).symm
  rw [h, Submodule.span_image, span_numerator]
  rfl

/-! ### Values of the twists `χ^u 𝟏` -/

theorem coordinateSum_ne_zero (g : (GroupAlgebra E)ˣ) :
    (g : GroupAlgebra E) 0 + (g : GroupAlgebra E) 1 + (g : GroupAlgebra E) 2 ≠ 0 := by
  rw [← augmentation_coefficients]
  exact Cubic.ToricHeights.FormulaForNormCharacter.augmentation_ne_zero g

private theorem ratio_identity {K : Type*} [Field K] {s v w : K} (hs : s ≠ 0) {a b c : ℕ}
    (h : a + b + c = 3) : s ^ a * v ^ b * w ^ c / s ^ 3 = (v / s) ^ b * (w / s) ^ c := by
  rw [div_pow, div_pow, ← h, pow_add, pow_add]
  field_simp

/-- The value of `χ₀^aχ₁^bχ₂^c e₁⁻³` at `g` is `(χ₁(g)/χ₀(g))^b (χ₂(g)/χ₀(g))^c`. -/
theorem value_eigenMonomial (j : Fin 4) (g : (GroupAlgebra E)ˣ) :
    value (eigenMonomial j) g =
      (((g : GroupAlgebra E) 0 + zeta * (g : GroupAlgebra E) 1 +
          zeta ^ 2 * (g : GroupAlgebra E) 2) /
        ((g : GroupAlgebra E) 0 + (g : GroupAlgebra E) 1 + (g : GroupAlgebra E) 2)) ^
          weightExponent j 1 *
      (((g : GroupAlgebra E) 0 + zeta ^ 2 * (g : GroupAlgebra E) 1 +
          zeta * (g : GroupAlgebra E) 2) /
        ((g : GroupAlgebra E) 0 + (g : GroupAlgebra E) 1 + (g : GroupAlgebra E) 2)) ^
          weightExponent j 2 := by
  rw [value, eigenMonomial_eq]
  simp only [map_mul, map_pow, map_add, eval_X, eval_C, e₁, χ₁, χ₂]
  exact ratio_identity (coordinateSum_ne_zero g) (weightExponent_sum j)

/-- The character values `χ^m(g) = (χ₁(g)/χ₀(g))^{m₁'} (χ₂(g)/χ₀(g))^{m₂'}` with
`(m₁',m₂') = pullback m` the `v^∨`-coordinates. -/
theorem character_value (m : ℤ × ℤ) (g : (GroupAlgebra E)ˣ) :
    ((CubicTargets.ToricHeights.FormulaForNormCharacter.groupCharacter zeta zeta_relation m g :
        Eˣ) : E) =
      (((g : GroupAlgebra E) 0 + zeta * (g : GroupAlgebra E) 1 +
          zeta ^ 2 * (g : GroupAlgebra E) 2) /
        ((g : GroupAlgebra E) 0 + (g : GroupAlgebra E) 1 + (g : GroupAlgebra E) 2)) ^
          (CharacterLattice.pullback m).1 *
      (((g : GroupAlgebra E) 0 + zeta ^ 2 * (g : GroupAlgebra E) 1 +
          zeta * (g : GroupAlgebra E) 2) /
        ((g : GroupAlgebra E) 0 + (g : GroupAlgebra E) 1 + (g : GroupAlgebra E) 2)) ^
          (CharacterLattice.pullback m).2 := by
  rw [Cubic.ToricHeights.FormulaForNormCharacter.groupCharacter_val,
    Cubic.ToricHeights.FormulaForNormCharacter.first_normalize,
    Cubic.ToricHeights.FormulaForNormCharacter.second_normalize, augmentation_coefficients,
    inv_mul_eq_div, inv_mul_eq_div]

/-- `weightCharacter j = χ^u` for `u = latticePoint j`, in `v^∨`-coordinates. -/
theorem weightCharacter_val (j : Fin 4) (g : (GroupAlgebra E)ˣ) :
    ((weightCharacter j g : Eˣ) : E) =
      (((g : GroupAlgebra E) 0 + zeta * (g : GroupAlgebra E) 1 +
          zeta ^ 2 * (g : GroupAlgebra E) 2) /
        ((g : GroupAlgebra E) 0 + (g : GroupAlgebra E) 1 + (g : GroupAlgebra E) 2)) ^
          weightExponent j 1 *
      (((g : GroupAlgebra E) 0 + zeta ^ 2 * (g : GroupAlgebra E) 1 +
          zeta * (g : GroupAlgebra E) 2) /
        ((g : GroupAlgebra E) 0 + (g : GroupAlgebra E) 1 + (g : GroupAlgebra E) 2)) ^
          weightExponent j 2 := by
  fin_cases j
  · simp [weightCharacter, weightExponent]
  all_goals
    simp only [weightCharacter, Matrix.cons_val, Fin.mk_one, Fin.reduceFinMk]
    rw [character_value]
  · rw [show ((1 : ℤ), (1 : ℤ)) = latticePoint 1 from rfl, pullback_latticePoint]
    simp only [zpow_natCast]
  · rw [show ((2 : ℤ), (1 : ℤ)) = latticePoint 2 from rfl, pullback_latticePoint]
    simp only [zpow_natCast]
  · rw [show ((1 : ℤ), (2 : ℤ)) = latticePoint 3 from rfl, pullback_latticePoint]
    simp only [zpow_natCast]

/-- `χ^u 𝟏` is a weight vector with character `χ^u`. -/
theorem weightSection_isWeightVector (j : Fin 4) :
    IsWeightVector (weightSection j) (weightCharacter j) := by
  intro F F₁ hF hF₁ g
  obtain rfl : F = eigenMonomial j := sectionOf_injective hF
  obtain rfl : F₁ = eigenMonomial 0 :=
    sectionOf_injective (hF₁.trans (weightVector_eq_weightSection 0 : (1 : RatFun) = _))
  rw [value_eigenMonomial, value_eigenMonomial, weightCharacter_val]
  simp [weightExponent]

theorem weightVector_character (j : Fin 4) :
    IsWeightVector (weightVector j) (weightCharacter j) := by
  rw [weightVector_eq_weightSection]
  exact weightSection_isWeightVector j

theorem «lemma:heightformula» : CubicTargets.ToricHeights.HeightFormula.Claim := by
  refine ⟨fun j => ?_, span_weightVector, weightVector_character⟩
  rw [← span_weightVector]
  exact Submodule.subset_span ⟨j, rfl⟩

end Cubic.ToricHeights.HeightFormula
