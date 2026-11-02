import Cubic.QuadraticCorrespondence.SplitLaurentEvaluation

/-!
# Points of the split Laurent ring and its invariant subalgebra

For every commutative `K`-algebra `R`, algebra homomorphisms `K[ℤ²] → R`
are exactly pairs of units of `R`. The invariant-ring isomorphism gives the
same description for points of the cyclic quotient in split coordinates.
This concerns algebra homomorphisms, not orbits of `R`-valued cover points:
the latter need not surject onto quotient points.

The natural comparison with the original group-algebra unit functor is proved
in `SplitCoverFunctor`; Galois descent is in `CyclotomicTorusDescent` and
`RationalCoverFunctor`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.SplitLaurentPoints

open SplitLaurentInvariants SplitLaurentEvaluation

variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R] [Algebra K R]

/-- A Laurent monomial is a unit, with inverse the opposite exponent. -/
def monomialUnit : Multiplicative (ℤ × ℤ) →* (LaurentRing (K := K))ˣ :=
  (AddMonoidAlgebra.of K (ℤ × ℤ)).toHomUnits

/-- Recover the two invertible coordinates from a coordinate-ring point. -/
def coordinates (F : LaurentRing (K := K) →ₐ[K] R) : Rˣ × Rˣ :=
  (Units.map F.toMonoidHom (monomialUnit (Multiplicative.ofAdd (1, 0))),
    Units.map F.toMonoidHom (monomialUnit (Multiplicative.ofAdd (0, 1))))

private theorem lattice_decomposition (n : ℤ × ℤ) :
    Multiplicative.ofAdd n = Multiplicative.ofAdd (1, 0) ^ n.1 *
      Multiplicative.ofAdd (0, 1) ^ n.2 := by
  apply Multiplicative.toAdd.injective
  simp

theorem pointCharacter_coordinates (F : LaurentRing (K := K) →ₐ[K] R) (n : ℤ × ℤ) :
    pointCharacter (coordinates F) (Multiplicative.ofAdd n) =
      Units.map F.toMonoidHom (monomialUnit (Multiplicative.ofAdd n)) := by
  conv_rhs => rw [lattice_decomposition n]
  simp [pointCharacter, coordinates]

theorem evaluate_coordinates (F : LaurentRing (K := K) →ₐ[K] R) :
    evaluate (coordinates F) = F := by
  apply AddMonoidAlgebra.algHom_ext
  intro n
  rw [evaluate_single, map_one, one_mul]
  exact congrArg Units.val (pointCharacter_coordinates F n)

theorem coordinates_evaluate (x : Rˣ × Rˣ) : coordinates (evaluate (K := K) x) = x := by
  apply Prod.ext
  · apply Units.ext
    change evaluate x (AddMonoidAlgebra.single (1, 0) (1 : K)) = (x.1 : R)
    simp [evaluate_single]
  · apply Units.ext
    change evaluate x (AddMonoidAlgebra.single (0, 1) (1 : K)) = (x.2 : R)
    simp [evaluate_single]

/-- The Laurent ring represents the split two-dimensional multiplicative group. -/
def pointEquiv : (LaurentRing (K := K) →ₐ[K] R) ≃ Rˣ × Rˣ where
  toFun := coordinates
  invFun := evaluate
  left_inv := evaluate_coordinates
  right_inv := coordinates_evaluate

/-- Points of the invariant ring, using its Laurent presentation.
Such a point need not lift to a cover point over `R`. -/
def quotientPointEquiv (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    (invariantRing ζ →ₐ[K] R) ≃ Rˣ × Rˣ :=
  ((invariantEquiv ζ hζ).symm.arrowCongr (AlgEquiv.refl : R ≃ₐ[K] R)).trans pointEquiv

/-- Restricting a cover point to invariant functions gives precisely the
quotient-character formula, as a map of coordinate-ring points. -/
theorem quotientPointEquiv_restrict (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3)
    (x : Rˣ × Rˣ) :
    quotientPointEquiv ζ hζ ((evaluate x).comp (invariantRing ζ).val) =
      (x.1 ^ 2 / x.2, x.2 ^ 2 / x.1) := by
  change coordinates ((evaluate x).comp pullbackHom) = _
  have h : (evaluate x).comp pullbackHom =
      evaluate (K := K) (x.1 ^ 2 / x.2, x.2 ^ 2 / x.1) :=
    AlgHom.ext (evaluate_pullback x)
  rw [h, coordinates_evaluate]

/-- The unit coordinates are compatible with a change of target algebra. -/
theorem coordinates_comp {S : Type*} [CommRing S] [Algebra K S]
    (φ : R →ₐ[K] S) (F : LaurentRing (K := K) →ₐ[K] R) :
    coordinates (φ.comp F) =
      (Units.map φ.toMonoidHom (coordinates F).1,
        Units.map φ.toMonoidHom (coordinates F).2) := by
  apply Prod.ext <;> apply Units.ext <;> rfl

end Cubic.QuadraticCorrespondence.SplitLaurentPoints
