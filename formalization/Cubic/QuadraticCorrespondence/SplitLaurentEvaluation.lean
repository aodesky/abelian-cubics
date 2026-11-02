import Cubic.QuadraticCorrespondence.SplitLaurentInvariants
import Cubic.QuadraticCorrespondence.CharacterCoefficients

/-!
# Evaluation of the split Laurent coordinate ring

Evaluate Laurent polynomials on pairs of units over a commutative algebra.
The exponent pullback defining the invariant ring evaluates to `(A²/B, B²/A)`,
and the diagonal ring action evaluates to multiplication by `(ζ, ζ²)`.
These identities connect the coordinate-ring construction to the quotient
characters on the original augmentation-one group-algebra cover.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.SplitLaurentEvaluation

open SplitLaurentInvariants

variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R] [Algebra K R]

/-- Evaluation of a lattice character on a pair of units. -/
def pointCharacter (x : Rˣ × Rˣ) : Multiplicative (ℤ × ℤ) →* Rˣ where
  toFun n := x.1 ^ n.toAdd.1 * x.2 ^ n.toAdd.2
  map_one' := by simp
  map_mul' n m := by
    change x.1 ^ (n.toAdd.1 + m.toAdd.1) * x.2 ^ (n.toAdd.2 + m.toAdd.2) = _
    simp only [zpow_add]
    ac_rfl

/-- The coordinate-ring point associated to a pair of invertible coordinates. -/
def evaluate (x : Rˣ × Rˣ) : LaurentRing (K := K) →ₐ[K] R :=
  AddMonoidAlgebra.lift K R _ ((Units.coeHom R).comp (pointCharacter x))

theorem evaluate_single (x : Rˣ × Rˣ) (n : ℤ × ℤ) (c : K) :
    evaluate x (AddMonoidAlgebra.single n c) =
      algebraMap K R c * (x.1 ^ n.1 * x.2 ^ n.2 : Rˣ) := by
  simp [evaluate, pointCharacter, Algebra.smul_def]

private theorem square_zpow (x : Rˣ) (n : ℤ) :
    (x ^ 2) ^ n = x ^ (2 * n) := by
  rw [← zpow_natCast, ← zpow_mul]
  rfl

theorem pointCharacter_quotient (x : Rˣ × Rˣ) (n : ℤ × ℤ) :
    pointCharacter (x.1 ^ 2 / x.2, x.2 ^ 2 / x.1) (Multiplicative.ofAdd n) =
      pointCharacter x (Multiplicative.ofAdd (CharacterLattice.pullback n)) := by
  change (x.1 ^ 2 / x.2) ^ n.1 * (x.2 ^ 2 / x.1) ^ n.2 =
    x.1 ^ (2 * n.1 - n.2) * x.2 ^ (-n.1 + 2 * n.2)
  simp only [div_eq_mul_inv, mul_zpow, square_zpow, inv_zpow, zpow_sub, zpow_add,
    zpow_neg, mul_assoc, mul_comm, mul_left_comm]

/-- The coordinate-ring pullback has the same point formula as the paper's
quotient characters. -/
theorem evaluate_pullback (x : Rˣ × Rˣ) (f : LaurentRing (K := K)) :
    evaluate x (pullbackHom f) = evaluate (x.1 ^ 2 / x.2, x.2 ^ 2 / x.1) f := by
  have h : (evaluate x).comp pullbackHom =
      evaluate (K := K) (x.1 ^ 2 / x.2, x.2 ^ 2 / x.1) := by
    apply AddMonoidAlgebra.algHom_ext
    intro n
    change evaluate x (Finsupp.mapDomain CharacterLattice.pullback
      (AddMonoidAlgebra.single n (1 : K))) = _
    rw [Finsupp.mapDomain_single]
    simp only [evaluate_single, map_one, one_mul]
    exact congrArg Units.val (pointCharacter_quotient x n).symm
  exact DFunLike.congr_fun h f

theorem pointCharacter_scaled (ζ : Rˣ) (x : Rˣ × Rˣ) (n : ℤ × ℤ) :
    pointCharacter (ζ * x.1, ζ ^ 2 * x.2) (Multiplicative.ofAdd n) =
      ζ ^ (n.1 + 2 * n.2) * pointCharacter x (Multiplicative.ofAdd n) := by
  change (ζ * x.1) ^ n.1 * (ζ ^ 2 * x.2) ^ n.2 =
    ζ ^ (n.1 + 2 * n.2) * (x.1 ^ n.1 * x.2 ^ n.2)
  simp only [mul_zpow, square_zpow, zpow_add, mul_assoc, mul_comm, mul_left_comm]

/-- Scaling the point is dual to the diagonal action on its coordinate ring. -/
theorem evaluate_twist (ζ : Kˣ) (x : Rˣ × Rˣ) (f : LaurentRing (K := K)) :
    evaluate x (twist ζ f) = evaluate
      (Units.map (algebraMap K R).toMonoidHom ζ * x.1,
        Units.map (algebraMap K R).toMonoidHom ζ ^ 2 * x.2) f := by
  let ζR := Units.map (algebraMap K R).toMonoidHom ζ
  have h : (evaluate x).comp (twist ζ) =
      evaluate (K := K) (ζR * x.1, ζR ^ 2 * x.2) := by
    apply AddMonoidAlgebra.algHom_ext
    intro n
    change evaluate x (twist ζ (AddMonoidAlgebra.single n 1)) = _
    rw [twist_single]
    simp only [evaluate_single, one_mul, map_one]
    have hscaled := congrArg Units.val (pointCharacter_scaled ζR x n).symm
    simpa only [ζR, ← map_zpow, Units.coe_map, Units.val_mul] using hscaled
  exact DFunLike.congr_fun h f

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters
open CharacterCoefficients

/-- The ring pullback agrees with the quotient characters constructed from
the convolution algebra, before descent to the ground field. -/
theorem evaluate_pullback_on_cover (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (g : traceOneUnits K) (f : LaurentRing (K := K)) :
    evaluate (firstCharacter ζ hζ g, secondCharacter ζ hζ g) (pullbackHom f) =
      evaluate (quotientCharacters ζ hζ g) f := by
  simpa only [quotientCharacters, MonoidHom.prod_apply, MonoidHom.mul_apply,
    MonoidHom.pow_apply, MonoidHom.inv_apply, div_eq_mul_inv] using
      (evaluate_pullback (firstCharacter ζ hζ g, secondCharacter ζ hζ g) f)

end Cubic.QuadraticCorrespondence.SplitLaurentEvaluation
