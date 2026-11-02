import Cubic.ToricHeights.QuotientFiniteHeight

/-!
# Spectral characters from the original finite logarithms

Apply `exp(2πi⟨m,ell⟩)` to the residue-weighted logarithm contributions,
with `m(v₀)=t` and `m(v₁)=m(v₂)=-t/2`. The proved comparison with the local
models establishes multiplicativity and continuity of these explicit formulas.
The local character is inverted only by the Fourier integrand, not here.
The adelic character is assembled in `Cubic.PoissonSummation.FiniteAdelicData`
and `Cubic.PoissonSummation.AdelicData`, and its triviality on rational points is
proved in `Cubic.PoissonSummation.AdelicRationalCharacter`.
-/

noncomputable section

namespace Cubic.ToricHeights.QuotientFiniteCharacter

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois
open QuotientFiniteHeight LocalLogarithmNormalization
open scoped RegularFunctionTopology RationalQuotientGroup

variable (p : ℕ) [Fact p.Prime]

section Split

variable [Fact (p % 3 = 1)]

theorem split_formula (t : ℝ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    Circle.exp (2 * Real.pi * spectralPairing t (splitLogarithm p P)) =
      SplitLocalModel.character p t (QuotientLocalModels.splitEquiv p P) := by
  rw [splitLogarithm_eq, ← split_character_averaged, QuotientLocalModels.splitEquiv_apply]

/-- The character defined by the sum of the two splitting-field contributions. -/
def splitCharacter (t : ℝ) : PontryaginDual (quotientFixedRing →ₐ[ℚ] ℚ_[p]) where
  toFun P := Circle.exp (2 * Real.pi * spectralPairing t (splitLogarithm p P))
  map_one' := by rw [split_formula, map_one, map_one]
  map_mul' P Q := by simp only [split_formula, map_mul]
  continuous_toFun := by
    have h : (fun P => Circle.exp (2 * Real.pi * spectralPairing t (splitLogarithm p P))) =
        (SplitLocalModel.character p t) ∘ (QuotientLocalModels.splitEquiv p) :=
      funext (split_formula p t)
    rw [h]
    exact (SplitLocalModel.character p t).continuous.comp (QuotientLocalModels.splitEquiv p).continuous

theorem splitCharacter_eq (t : ℝ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    splitCharacter p t P = SplitLocalModel.character p t (QuotientLocalModels.splitEquiv p P) :=
  split_formula p t P

@[simp]
theorem splitCharacter_zero : splitCharacter p 0 = 1 := by
  apply DFunLike.ext
  intro P
  change Circle.exp (2 * Real.pi * spectralPairing 0 (splitLogarithm p P)) = 1
  simp [spectralPairing]

end Split

section Inert

variable [Fact (p % 3 = 2)]

theorem inert_formula (t : ℝ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    Circle.exp (2 * Real.pi * spectralPairing t (inertLogarithm p P)) =
      InertLocalModel.character p t (QuotientLocalModels.inertEquiv p P) := by
  rw [inertLogarithm_eq, phase_eq p t _ _ (InertLocalModel.rayCoordinates_sum p _)]
  rfl

/-- The inert character uses the residue degree in the logarithmic weight. -/
def inertCharacter (t : ℝ) : PontryaginDual (quotientFixedRing →ₐ[ℚ] ℚ_[p]) where
  toFun P := Circle.exp (2 * Real.pi * spectralPairing t (inertLogarithm p P))
  map_one' := by rw [inert_formula, map_one, map_one]
  map_mul' P Q := by simp only [inert_formula, map_mul]
  continuous_toFun := by
    have h : (fun P => Circle.exp (2 * Real.pi * spectralPairing t (inertLogarithm p P))) =
        (InertLocalModel.character p t) ∘ (QuotientLocalModels.inertEquiv p) :=
      funext (inert_formula p t)
    rw [h]
    exact (InertLocalModel.character p t).continuous.comp (QuotientLocalModels.inertEquiv p).continuous

theorem inertCharacter_eq (t : ℝ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) :
    inertCharacter p t P = InertLocalModel.character p t (QuotientLocalModels.inertEquiv p P) :=
  inert_formula p t P

@[simp]
theorem inertCharacter_zero : inertCharacter p 0 = 1 := by
  apply DFunLike.ext
  intro P
  change Circle.exp (2 * Real.pi * spectralPairing 0 (inertLogarithm p P)) = 1
  simp [spectralPairing]

end Inert

theorem ramified_formula (t : ℝ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    Circle.exp (2 * Real.pi * spectralPairing t (ramifiedLogarithm P)) =
      RamifiedLocalModel.character t (QuotientLocalModels.ramifiedEquiv P) := by
  rw [ramifiedLogarithm_eq, ← ramified_character, QuotientLocalModels.ramifiedEquiv_apply]

/-- The ramified character retains exactly one division by the global degree. -/
def ramifiedCharacter (t : ℝ) : PontryaginDual (quotientFixedRing →ₐ[ℚ] ℚ_[3]) where
  toFun P := Circle.exp (2 * Real.pi * spectralPairing t (ramifiedLogarithm P))
  map_one' := by rw [ramified_formula, map_one, map_one]
  map_mul' P Q := by simp only [ramified_formula, map_mul]
  continuous_toFun := by
    have h : (fun P => Circle.exp (2 * Real.pi * spectralPairing t (ramifiedLogarithm P))) =
        (RamifiedLocalModel.character t) ∘ QuotientLocalModels.ramifiedEquiv :=
      funext (ramified_formula t)
    rw [h]
    exact (RamifiedLocalModel.character t).continuous.comp QuotientLocalModels.ramifiedEquiv.continuous

theorem ramifiedCharacter_eq (t : ℝ) (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) :
    ramifiedCharacter t P = RamifiedLocalModel.character t (QuotientLocalModels.ramifiedEquiv P) :=
  ramified_formula t P

@[simp]
theorem ramifiedCharacter_zero : ramifiedCharacter 0 = 1 := by
  apply DFunLike.ext
  intro P
  change Circle.exp (2 * Real.pi * spectralPairing 0 (ramifiedLogarithm P)) = 1
  simp [spectralPairing]

end Cubic.ToricHeights.QuotientFiniteCharacter
