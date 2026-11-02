import Cubic.QuadraticCorrespondence.CyclotomicLocalRoots
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Splitting the third cyclotomic algebra

We use the quotient `K[X]/(X²+X+1)`, via mathlib's `AdjoinRoot`.
At a split rational prime the Hensel-lifted roots give an algebra isomorphism
to `ℚ_[p] × ℚ_[p]`. Its formulas record which coordinate is which.
`CyclotomicBaseChange.lean` identifies this quotient with the global field's
local tensor product.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicLocalAlgebra

open Polynomial

/-- A presentation of the third cyclotomic algebra over the base field. -/
abbrev Model (K : Type*) [CommRing K] := AdjoinRoot (cyclotomic 3 K)

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- Evaluation on the quotient at a root of the cyclotomic polynomial. -/
def evaluation (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) : Model K →ₐ[K] K :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId K K) ζ (by simpa [cyclotomic_three] using hζ)

omit [CharZero K] in
theorem other_root (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (-1 - ζ) ^ 2 + (-1 - ζ) + 1 = 0 := by
  linear_combination hζ

theorem roots_distinct (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ≠ -1 - ζ := by
  intro h
  have hd : 2 * ζ + 1 = 0 := by linear_combination h
  have h3 : (3 : K) = 0 := by linear_combination 4 * hζ - (2 * ζ + 1) * hd
  norm_num at h3

def evaluationPair (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) : Model K →ₐ[K] K × K :=
  (evaluation ζ hζ).prod (evaluation (-1 - ζ) (other_root ζ hζ))

omit [CharZero K] in
@[simp]
theorem evaluationPair_root (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    evaluationPair ζ hζ (AdjoinRoot.root (cyclotomic 3 K)) = (ζ, -1 - ζ) := by
  simp [evaluationPair, evaluation]

/-- Two-point interpolation proves that both coordinates can be specified independently. -/
theorem evaluationPair_surjective (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    Function.Surjective (evaluationPair ζ hζ) := by
  rintro ⟨x, y⟩
  let b := (x - y) / (ζ - (-1 - ζ))
  let a := x - b * ζ
  refine ⟨algebraMap K (Model K) a +
    algebraMap K (Model K) b * AdjoinRoot.root (cyclotomic 3 K), ?_⟩
  have hn : ζ - (-1 - ζ) ≠ 0 := sub_ne_zero.mpr (roots_distinct ζ hζ)
  simp only [map_add, map_mul, AlgHom.commutes, evaluationPair_root]
  apply Prod.ext <;> dsimp [a, b]
  · ring
  · field_simp
    ring

instance finiteDimensional : FiniteDimensional K (Model K) :=
  (cyclotomic.monic 3 K).finite_adjoinRoot

omit [CharZero K] in
theorem finrank_model : Module.finrank K (Model K) = 2 := by
  rw [(AdjoinRoot.powerBasis' (cyclotomic.monic 3 K)).finrank,
    AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic]
  rfl

/-- The cyclotomic quotient is the product algebra when a root exists. -/
def splittingEquiv (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) : Model K ≃ₐ[K] K × K :=
  AlgEquiv.ofBijective (evaluationPair ζ hζ) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [finrank_model]) (f := (evaluationPair ζ hζ).toLinearMap)).mpr
        (evaluationPair_surjective ζ hζ),
    evaluationPair_surjective ζ hζ⟩

@[simp]
theorem splittingEquiv_root (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    splittingEquiv ζ hζ (AdjoinRoot.root (cyclotomic 3 K)) = (ζ, -1 - ζ) :=
  evaluationPair_root ζ hζ

end Field

/-- At a prime `p ≡ 1 (mod 3)` the cyclotomic quotient over `ℚ_[p]` is `ℚ_[p] × ℚ_[p]`. -/
def padicSplittingEquiv (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    Model ℚ_[p] ≃ₐ[ℚ_[p]] ℚ_[p] × ℚ_[p] :=
  splittingEquiv (Classical.choose (CyclotomicLocalRoots.field_root p hp))
    (Classical.choose_spec (CyclotomicLocalRoots.field_root p hp))

end Cubic.QuadraticCorrespondence.CyclotomicLocalAlgebra
