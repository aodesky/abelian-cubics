import Cubic.ToricHeights.WeightVectors
import CubicTargets.ToricHeights.FormulaForNormCharacter
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Concrete statement of `lemma:heightformula` (with `eqn:weightVectors`)

Let `𝟏 ∈ H⁰(S_E, 𝒪(3D₀))` be the section associated to the effective Cartier divisor `3D₀`.
The space `H⁰(S_E, 𝒪(3D₀))` is spanned over `E` by the four weight vectors
```text
𝟏,   (1 - 3e₂e₁⁻²)𝟏,
(e₁³ - 9/2 e₁e₂ + 27/2 e₃ + √-27/2 √disc) e₁⁻³ 𝟏,
(e₁³ - 9/2 e₁e₂ + 27/2 e₃ - √-27/2 √disc) e₁⁻³ 𝟏,        √disc := (X-Z)(Y-X)(Z-Y),
```
with associated characters of `T_E` respectively `1, χ^{a'+b'}, χ^{2a'+b'}, χ^{2b'+a'}`,
where `a' = 2v₁^∨ - v₂^∨`, `b' = 2v₂^∨ - v₁^∨`.

## Model

* **Global sections.** The model for `H⁰(S_E, 𝒪(3D₀))` used here is
  `E[X,Y,Z]₃^{C₃} · e₁⁻³`: `C₃`-invariant cubic forms divided by `e₁³`. This is the
  identification `H⁰(S_E,𝒪(3D₀)) = H⁰(ℙ_E,𝒪(3D₀'))^{C₃}`, with `D₀'` the divisor of the
  section `e₁` of `𝒪(1)`: `𝒪(3D₀)` pulls back to `𝒪(3D₀')` under the quotient morphism
  `ℙ_E → ℙ_E/C₃`. The paper uses this identification without displaying it. Concretely `globalSections` is the `E`-subspace of the field of rational functions
  `RatFun = Frac E[X,Y,Z]` consisting of the `F/e₁³` with `F ∈ invariantCubics`, a homogeneous
  cubic of `E[X,Y,Z]` invariant under the cyclic permutation `X ↦ Y ↦ Z ↦ X` generating `C₃`.
  The variables are indexed by `ZMod 3` (`X = X 0`, `Y = X 1`, `Z = X 2`), and `C₃` acts by
  `rename (· + 1)`.
* **The section `𝟏`.** The image of `1` under `𝒪 ↪ 𝒪(3D₀)` is the rational function
  `1 = e₁³/e₁³`.
* **Weight vectors.** `T_E` acts through the torus: a point of `T_E` is represented by a unit
  `g = X·1 + Y·σ + Z·σ²` of the group algebra `E[C₃]` (as in
  `CubicTargets.ToricHeights.FormulaForNormCharacter`; characters of `𝒢₁` are pulled back to
  the full unit group along `g ↦ χ₀(g)⁻¹g`). The value of the section `F/e₁³` at `g` is
  `F(g₀,g₁,g₂)/e₁(g)³` (`value`; `e₁(g) = χ₀(g) ≠ 0` for a unit, and the value is invariant
  under scaling `g`, so it is a function on the augmentation-one quotient). A section `s` is a
  weight vector with character `χ` (`IsWeightVector`) if its value equals `χ` times the value of
  `𝟏`, at every point `g`.
* **Characters.** `χ^m` for `m = m₁a' + m₂b' ∈ M_E` is
  `FormulaForNormCharacter.groupCharacter ζ hζ (m₁, m₂)` (so `a'+b' = (1,1)`,
  `2a'+b' = (2,1)`, `2b'+a' = (1,2)`), with `ζ = CyclotomicField.zeta ∈ E`.
* **`√-27`.** The TeX does not fix the square root; we use the project's
  `√-27 = 3(2ζ+1)` (`WeightVectors.sqrtNegTwentySeven`), the same choice as in
  `eqn:formulaForNormCharacter2`.

The paper's proof uses Fulton's weight decomposition
`H⁰ = ⊕_{u ∈ P ∩ M_E} E χ^u`. In this model the proof carries out that weight
decomposition explicitly, in eigen-coordinates: the invariant eigen-monomials correspond to
the lattice points of `P` (see the proof file).
-/

noncomputable section

namespace CubicTargets.ToricHeights.HeightFormula

open MvPolynomial
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.OrbitParametrization.CyclicGroupAlgebra
open CubicTargets.ToricHeights.FormulaForNormCharacter

/-- `E[X,Y,Z]`, with `X, Y, Z = X 0, X 1, X 2`. -/
abbrev Poly := MvPolynomial (ZMod 3) E

/-- The field of rational functions `E(X,Y,Z)`. -/
abbrev RatFun := FractionRing Poly

/-- The generator `X ↦ Y ↦ Z ↦ X` of the `C₃`-action. -/
def cyclicShift : Poly →ₐ[E] Poly := rename (fun i : ZMod 3 => i + 1)

/-- `E[X,Y,Z]₃^{C₃}`: homogeneous cubics invariant under the cyclic permutation. -/
def invariantCubics : Submodule E Poly :=
  homogeneousSubmodule (ZMod 3) E 3 ⊓ LinearMap.eqLocus cyclicShift.toLinearMap LinearMap.id

/-- `e₁ = X+Y+Z`. -/
def e₁ : Poly := X 0 + X 1 + X 2

/-- `e₂ = XY+YZ+ZX`. -/
def e₂ : Poly := X 0 * X 1 + X 1 * X 2 + X 2 * X 0

/-- `e₃ = XYZ`. -/
def e₃ : Poly := X 0 * X 1 * X 2

/-- `√disc = (X-Z)(Y-X)(Z-Y)`. -/
def sqrtDisc : Poly := (X 0 - X 2) * (X 1 - X 0) * (X 2 - X 1)

/-- Polynomials as rational functions. -/
def toRatFun : Poly →ₐ[E] RatFun := IsScalarTower.toAlgHom E Poly RatFun

/-- `F ↦ F · e₁⁻³`. -/
def sectionOf : Poly →ₗ[E] RatFun :=
  LinearMap.mulRight E ((toRatFun e₁)⁻¹ ^ 3) ∘ₗ toRatFun.toLinearMap

/-- `H⁰(S_E, 𝒪(3D₀)) = E[X,Y,Z]₃^{C₃} · e₁⁻³`. -/
def globalSections : Submodule E RatFun := invariantCubics.map sectionOf

/-- The four weight vectors of `eqn:weightVectors` (`𝟏 = 1`). -/
def weightVector : Fin 4 → RatFun :=
  let x₁ := toRatFun e₁
  let x₂ := toRatFun e₂
  let x₃ := toRatFun e₃
  let d := toRatFun sqrtDisc
  let s := algebraMap E RatFun Cubic.ToricHeights.WeightVectors.sqrtNegTwentySeven
  ![1,
    (1 - 3 * x₂ * x₁⁻¹ ^ 2) * 1,
    (x₁ ^ 3 - 9 / 2 * x₁ * x₂ + 27 / 2 * x₃ + s / 2 * d) * x₁⁻¹ ^ 3 * 1,
    (x₁ ^ 3 - 9 / 2 * x₁ * x₂ + 27 / 2 * x₃ - s / 2 * d) * x₁⁻¹ ^ 3 * 1]

/-- The value of the section `F · e₁⁻³` at the point `g = X·1 + Y·σ + Z·σ²`. -/
def value (F : Poly) (g : (GroupAlgebra E)ˣ) : E :=
  eval (fun i => (g : GroupAlgebra E) i) F / eval (fun i => (g : GroupAlgebra E) i) e₁ ^ 3

/-- `s` is a weight vector with character `χ`: its value is `χ` times the value of `𝟏`. -/
def IsWeightVector (s : RatFun) (χ : (GroupAlgebra E)ˣ →* Eˣ) : Prop :=
  ∀ F F₁ : Poly, sectionOf F = s → sectionOf F₁ = 1 →
    ∀ g : (GroupAlgebra E)ˣ, value F g = (χ g : E) * value F₁ g

/-- The characters `1, χ^{a'+b'}, χ^{2a'+b'}, χ^{2b'+a'}`. -/
def weightCharacter : Fin 4 → ((GroupAlgebra E)ˣ →* Eˣ) :=
  ![1, groupCharacter zeta zeta_relation (1, 1), groupCharacter zeta zeta_relation (2, 1),
    groupCharacter zeta zeta_relation (1, 2)]

def Claim : Prop :=
  (∀ j, weightVector j ∈ globalSections) ∧
    Submodule.span E (Set.range weightVector) = globalSections ∧
    ∀ j, IsWeightVector (weightVector j) (weightCharacter j)

end CubicTargets.ToricHeights.HeightFormula
