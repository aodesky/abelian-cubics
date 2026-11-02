import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The cyclic group algebra and its augmentation-one units

This is the paper's group algebra, with convolution multiplication, and the
group of its units with augmentation one. Evaluation at a cube root of unity
gives its multiplicative characters. The quotient torus by `C₃` is not defined
here; its rational points are not the quotient of the rational points of this
group.
-/

noncomputable section

namespace Cubic.OrbitParametrization.CyclicGroupAlgebra

variable (R : Type*) [CommRing R]

abbrev GroupAlgebra := AddMonoidAlgebra R (ZMod 3)

/-- The element `x e + y σ + z σ²` of the group algebra. -/
def coordinates (x y z : R) : GroupAlgebra R :=
  AddMonoidAlgebra.single 0 x + AddMonoidAlgebra.single 1 y + AddMonoidAlgebra.single 2 z

theorem coordinates_coefficients (f : GroupAlgebra R) :
    coordinates R (f 0) (f 1) (f 2) = f := by
  ext i
  fin_cases i <;> simp [coordinates,
    show (2 : ZMod 3) ≠ 0 by decide, show (2 : ZMod 3) ≠ 1 by decide,
    show (0 : ZMod 3) ≠ 2 by decide, show (1 : ZMod 3) ≠ 2 by decide]

/-- The character of the cyclic group specified by the image of its generator. -/
def rootCharacter (ζ : R) (hζ : ζ ^ 3 = 1) : Multiplicative (ZMod 3) →* R where
  toFun i := ζ ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change ζ ^ (i.toAdd + j.toAdd).val = ζ ^ i.toAdd.val * ζ ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

/-- Extend the cyclic character to an algebra homomorphism by mathlib's
universal property of the group algebra. -/
def evaluation (ζ : R) (hζ : ζ ^ 3 = 1) : GroupAlgebra R →ₐ[R] R :=
  AddMonoidAlgebra.lift R R (ZMod 3) (rootCharacter R ζ hζ)

theorem evaluation_coordinates (ζ : R) (hζ : ζ ^ 3 = 1) (x y z : R) :
    evaluation R ζ hζ (coordinates R x y z) = x + y * ζ + z * ζ ^ 2 := by
  norm_num [evaluation, coordinates, rootCharacter, smul_eq_mul, ZMod.val]

theorem evaluation_coefficients (ζ : R) (hζ : ζ ^ 3 = 1) (f : GroupAlgebra R) :
    evaluation R ζ hζ f = f 0 + f 1 * ζ + f 2 * ζ ^ 2 := by
  conv_lhs => rw [← coordinates_coefficients R f]
  exact evaluation_coordinates R ζ hζ _ _ _

/-- The usual augmentation of the group algebra. -/
def augmentation : GroupAlgebra R →ₐ[R] R := evaluation R 1 (by simp)

theorem augmentation_coefficients (f : GroupAlgebra R) :
    augmentation R f = f 0 + f 1 + f 2 := by
  simp [augmentation, evaluation_coefficients]

/-- The group of units of the group algebra with augmentation one. -/
def traceOneUnits : Subgroup (GroupAlgebra R)ˣ :=
  (Units.map (augmentation R).toMonoidHom).ker

theorem augmentation_traceOneUnit (g : traceOneUnits R) :
    augmentation R (g.val : GroupAlgebra R) = 1 := by
  exact congrArg Units.val g.property

theorem trace_one (g : traceOneUnits R) :
    (g.val : GroupAlgebra R) 0 + (g.val : GroupAlgebra R) 1 +
      (g.val : GroupAlgebra R) 2 = 1 := by
  rw [← augmentation_coefficients]
  exact augmentation_traceOneUnit R g

/-- The cyclic group sits inside the augmentation-one units via its
group-algebra basis elements. -/
def cyclicUnits : Multiplicative (ZMod 3) →* traceOneUnits R :=
  (AddMonoidAlgebra.of R (ZMod 3)).toHomUnits.codRestrict (traceOneUnits R) (by
    intro i
    apply Units.ext
    change evaluation R 1 _ (AddMonoidAlgebra.single i.toAdd 1) = 1
    simp [evaluation, rootCharacter])

theorem cyclicUnits_injective [Nontrivial R] : Function.Injective (cyclicUnits R) := by
  intro i j h
  apply AddMonoidAlgebra.of_injective (R := R)
  exact congrArg (fun g : traceOneUnits R => (g.val : GroupAlgebra R)) h

/-- The character restricted to the augmentation-one unit group. -/
def character (ζ : R) (hζ : ζ ^ 3 = 1) : traceOneUnits R →* Rˣ :=
  (Units.map (evaluation R ζ hζ).toMonoidHom).comp (traceOneUnits R).subtype

theorem character_val (ζ : R) (hζ : ζ ^ 3 = 1) (g : traceOneUnits R) :
    (character R ζ hζ g : R) =
      (g.val : GroupAlgebra R) 0 + (g.val : GroupAlgebra R) 1 * ζ +
        (g.val : GroupAlgebra R) 2 * ζ ^ 2 :=
  evaluation_coefficients R ζ hζ _

theorem character_cyclicUnits (ζ : R) (hζ : ζ ^ 3 = 1) (i : Multiplicative (ZMod 3)) :
    (character R ζ hζ (cyclicUnits R i) : R) = ζ ^ i.toAdd.val := by
  change evaluation R ζ hζ (AddMonoidAlgebra.single i.toAdd 1) = _
  simp [evaluation, rootCharacter]

end Cubic.OrbitParametrization.CyclicGroupAlgebra
