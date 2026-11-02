import Cubic.QuadraticCorrespondence.CharacterLattice
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The invariant Laurent ring of the split cyclic action

The diagonal cover has Laurent ring `K[ℤ²]`. Its cyclic generator scales the
two coordinates by `ζ` and `ζ²`, hence a monomial of exponent `(r,s)` by
`ζ^(r+2s)`. We construct this algebra automorphism, prove its cube is the
identity, and identify its fixed subalgebra with the image of the quotient's
character lattice. The invariant ring is again a two-variable Laurent ring.

This is the coordinate-ring quotient in diagonal coordinates over the splitting
field. `SplitCoverFunctor` proves compatibility with the original group-algebra
unit functor and its cyclic action. Descent to the ground field is in
`SplitLaurentGalois` and `CyclotomicTorusDescent`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.SplitLaurentInvariants

variable {K : Type*} [Field K]

abbrev LaurentRing := AddMonoidAlgebra K (ℤ × ℤ)

/-- The scalar weight of a Laurent monomial under the cyclic generator. -/
def weightCharacter (ζ : Kˣ) : Multiplicative (ℤ × ℤ) →* Kˣ where
  toFun n := ζ ^ (n.toAdd.1 + 2 * n.toAdd.2)
  map_one' := by simp
  map_mul' n m := by
    change ζ ^ ((n.toAdd.1 + m.toAdd.1) + 2 * (n.toAdd.2 + m.toAdd.2)) = _
    rw [show (n.toAdd.1 + m.toAdd.1) + 2 * (n.toAdd.2 + m.toAdd.2) =
      (n.toAdd.1 + 2 * n.toAdd.2) + (m.toAdd.1 + 2 * m.toAdd.2) by ring, zpow_add]

private def twistedMonomial (ζ : Kˣ) : Multiplicative (ℤ × ℤ) →* LaurentRing (K := K) where
  toFun n := AddMonoidAlgebra.single n.toAdd (weightCharacter ζ n : K)
  map_one' := by simp [weightCharacter, AddMonoidAlgebra.one_def]
  map_mul' n m := by
    simp only [AddMonoidAlgebra.single_mul_single, map_mul, Units.val_mul]
    rfl

/-- The diagonal scaling action as an algebra homomorphism. -/
def twist (ζ : Kˣ) : LaurentRing (K := K) →ₐ[K] LaurentRing (K := K) :=
  AddMonoidAlgebra.lift K _ _ (twistedMonomial ζ)

theorem twist_single (ζ : Kˣ) (n : ℤ × ℤ) (c : K) :
    twist ζ (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single n (c * (ζ ^ (n.1 + 2 * n.2) : Kˣ)) := by
  simp [twist, twistedMonomial, weightCharacter, smul_eq_mul]

theorem twist_apply (ζ : Kˣ) (f : LaurentRing (K := K)) (n : ℤ × ℤ) :
    twist ζ f n = f n * (ζ ^ (n.1 + 2 * n.2) : Kˣ) := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp [hf, hg, add_mul]
  · intro m c
    rw [twist_single]
    by_cases h : m = n
    · subst m
      simp
    · simp [h]

theorem twist_one : twist (1 : Kˣ) = AlgHom.id K (LaurentRing (K := K)) := by
  apply AlgHom.ext
  intro f
  ext n
  simp [twist_apply]

theorem twist_comp (ζ η : Kˣ) : (twist ζ).comp (twist η) = twist (ζ * η) := by
  apply AlgHom.ext
  intro f
  ext n
  simp [twist_apply, mul_zpow, mul_assoc, mul_comm]

/-- The generator acts by an algebra automorphism. -/
def twistEquiv (ζ : Kˣ) : LaurentRing (K := K) ≃ₐ[K] LaurentRing (K := K) :=
  AlgEquiv.ofAlgHom (twist ζ) (twist ζ⁻¹)
    (by rw [twist_comp, mul_inv_cancel, twist_one])
    (by rw [twist_comp, inv_mul_cancel, twist_one])

theorem twist_cube (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (twist ζ).comp ((twist ζ).comp (twist ζ)) = AlgHom.id K (LaurentRing (K := K)) := by
  rw [twist_comp, twist_comp,
    show ζ * (ζ * ζ) = ζ ^ 3 by simp [pow_succ, mul_assoc], hζ, twist_one]

/-- The fixed subalgebra of the generator. For a cube root, `twist_cube`
proves the order-three relation, so this is the cyclic invariant ring. -/
def invariantRing (ζ : Kˣ) : Subalgebra K (LaurentRing (K := K)) :=
  AlgHom.equalizer (twist ζ) (AlgHom.id K _)

/-- Fixing the generator is equivalent to fixing every element of the
cyclic action it generates. -/
theorem twist_pow_apply_of_mem (ζ : Kˣ) (f : invariantRing ζ) (n : ℕ) :
    twist (ζ ^ n) (f : LaurentRing (K := K)) = f := by
  have hf : twist ζ (f : LaurentRing (K := K)) = f := f.property
  induction n with
  | zero => simp [twist_one]
  | succ n ih =>
    rw [pow_succ, ← twist_comp]
    change twist (ζ ^ n) (twist ζ (f : LaurentRing (K := K))) = f
    rw [hf, ih]

/-- Invariance means exactly that coefficients outside the character sublattice vanish. -/
theorem mem_invariantRing_iff (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3)
    (f : LaurentRing (K := K)) :
    f ∈ invariantRing ζ ↔ ∀ n : ℤ × ℤ, ¬ (3 : ℤ) ∣ n.1 + 2 * n.2 → f n = 0 := by
  change twist ζ f = f ↔ _
  constructor
  · intro hf n hn
    by_contra hnonzero
    have hc := congrArg (fun g : LaurentRing (K := K) => g n) hf
    change twist ζ f n = f n at hc
    rw [twist_apply] at hc
    have hpow : ζ ^ (n.1 + 2 * n.2) = 1 := by
      apply Units.ext
      exact mul_left_cancel₀ hnonzero (hc.trans (mul_one (f n)).symm)
    exact hn ((hζ.zpow_eq_one_iff_dvd _).mp hpow)
  · intro hf
    ext n
    rw [twist_apply]
    by_cases hn : (3 : ℤ) ∣ n.1 + 2 * n.2
    · rw [(hζ.zpow_eq_one_iff_dvd _).mpr hn]
      simp
    · rw [hf n hn, zero_mul]

/-- Pullback of Laurent monomials along the quotient-character basis. -/
def pullbackHom : LaurentRing (K := K) →ₐ[K] LaurentRing (K := K) :=
  AddMonoidAlgebra.mapDomainAlgHom K K CharacterLattice.pullback

theorem pullbackHom_single (n : ℤ × ℤ) (c : K) :
    pullbackHom (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single (CharacterLattice.pullback n) c :=
  Finsupp.mapDomain_single

theorem pullbackHom_injective : Function.Injective (pullbackHom (K := K)) :=
  AddMonoidAlgebra.mapDomain_injective CharacterLattice.pullback_injective

/-- The image of the quotient Laurent ring is the entire invariant subalgebra. -/
theorem range_pullbackHom (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    (pullbackHom (K := K)).range = invariantRing ζ := by
  ext f
  change f ∈ Set.range (Finsupp.mapDomain CharacterLattice.pullback) ↔ f ∈ invariantRing ζ
  rw [mem_invariantRing_iff ζ hζ]
  simpa only [CharacterLattice.mem_range_pullback] using
    (Finsupp.mem_range_mapDomain_iff CharacterLattice.pullback CharacterLattice.pullback_injective
      (f : (ℤ × ℤ) →₀ K))

/-- The cyclic invariant coordinate ring is a Laurent polynomial algebra
with the paper's quotient characters as its two generators. -/
def invariantEquiv (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    LaurentRing (K := K) ≃ₐ[K] invariantRing ζ :=
  (AlgEquiv.ofInjective pullbackHom pullbackHom_injective).trans
    (Subalgebra.equivOfEq _ _ (range_pullbackHom ζ hζ))

end Cubic.QuadraticCorrespondence.SplitLaurentInvariants
