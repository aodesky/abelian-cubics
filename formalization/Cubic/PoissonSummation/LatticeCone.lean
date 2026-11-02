import Cubic.OrbitParametrization.CocharacterLattice
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Lattice points in the integral cone

The cone is the nonnegative quadrant in the paper's ambient `(v₁,v₂)`
coordinates, intersected with `N_E`, not with the smaller lattice `N'_E`.
The equivalence with `AmbientCone` makes that distinction explicit.
-/

noncomputable section

namespace Cubic.PoissonSummation.LatticeCone

open Cubic.OrbitParametrization.CocharacterLattice

def InCone (n : ℤ × ℤ) : Prop := 0 ≤ (coordinates n).1 ∧ 0 ≤ (coordinates n).2

theorem inCone_iff (n : ℤ × ℤ) : InCone n ↔ 0 ≤ n.2 ∧ 0 ≤ 3 * n.1 + 2 * n.2 := by
  change (0 ≤ (n.1 : ℚ) + 2 * n.2 / 3 ∧ 0 ≤ (n.2 : ℚ) / 3) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · exact_mod_cast (by linarith : 0 ≤ (n.2 : ℚ))
    · exact_mod_cast (by linarith : 0 ≤ 3 * (n.1 : ℚ) + 2 * n.2)
  · rintro ⟨h1, h2⟩
    have h1' : 0 ≤ (n.2 : ℚ) := by exact_mod_cast h1
    have h2' : 0 ≤ 3 * (n.1 : ℚ) + 2 * n.2 := by exact_mod_cast h2
    constructor <;> linarith

abbrev ConePoint := {n : ℤ × ℤ // InCone n}

/-- The actual nonnegative cone in the rational ambient plane, intersected with `N_E`. -/
abbrev AmbientCone := {n : ℚ × ℚ // n ∈ lattice ∧ 0 ≤ n.1 ∧ 0 ≤ n.2}

def toAmbient (n : ConePoint) : AmbientCone :=
  ⟨coordinates n.1, ⟨⟨n.1, rfl⟩, n.2⟩⟩

/-- The integral-coordinate model counts precisely the paper's lattice points. -/
def ambientEquiv : ConePoint ≃ AmbientCone := Equiv.ofBijective toAmbient (by
  constructor
  · intro n m h
    exact Subtype.ext (coordinates_injective (congrArg Subtype.val h))
  · rintro ⟨x, hx, hcone⟩
    obtain ⟨n, hn⟩ := hx
    exact ⟨⟨n, by simpa [InCone, hn] using hcone⟩, Subtype.ext hn⟩)

theorem degree_nonneg (n : ConePoint) : 0 ≤ n.1.1 + n.1.2 := by
  have h := (inCone_iff n.1).mp n.2
  omega

/-- The integral height degree `n₁+n₂ = a+b`. -/
def degree (n : ConePoint) : ℕ := (n.1.1 + n.1.2).toNat

@[simp]
theorem degree_coe (n : ConePoint) : (degree n : ℤ) = n.1.1 + n.1.2 :=
  Int.toNat_of_nonneg (degree_nonneg n)

theorem coordinate_sum (n : ConePoint) :
    (coordinates n.1).1 + (coordinates n.1).2 = (degree n : ℚ) := by
  have h : (degree n : ℚ) = (n.1.1 : ℚ) + n.1.2 := by exact_mod_cast degree_coe n
  rw [h]
  simp [coordinates]
  ring

theorem second_coordinate_bounds (n : ConePoint) :
    0 ≤ n.1.2 ∧ n.1.2 ≤ 3 * (degree n : ℤ) := by
  have h := (inCone_iff n.1).mp n.2
  rw [degree_coe]
  omega

/-- The degree and the integer parameter `0 ≤ b ≤ 3k` parametrize the entire cone. -/
def sliceEquiv : ConePoint ≃ (Σ k : ℕ, Fin (3 * k + 1)) where
  toFun n := ⟨degree n, ⟨n.1.2.toNat, by
    have h := second_coordinate_bounds n
    have he := Int.toNat_of_nonneg h.1
    omega⟩⟩
  invFun s := ⟨((s.1 : ℤ) - s.2, (s.2 : ℕ)), by
    rw [inCone_iff]
    have h := s.2.isLt
    constructor <;> dsimp <;> omega⟩
  left_inv n := by
    apply Subtype.ext
    have h := second_coordinate_bounds n
    have he := Int.toNat_of_nonneg h.1
    have hd := degree_coe n
    apply Prod.ext <;> dsimp <;> omega
  right_inv s := by
    rcases s with ⟨k, b, hb⟩
    simp [degree]
    apply (Fin.heq_ext_iff (by simp)).mpr
    rfl

@[simp]
theorem sliceEquiv_degree (n : ConePoint) : (sliceEquiv n).1 = degree n := rfl

@[simp]
theorem degree_sliceEquiv_symm (s : Σ k : ℕ, Fin (3 * k + 1)) :
    degree (sliceEquiv.symm s) = s.1 := by
  exact congrArg Sigma.fst (sliceEquiv.apply_symm_apply s)

/-- A degree slice contains precisely the parameters `b = 0, …, 3k`. -/
def degreeFiberEquiv (k : ℕ) : {n : ConePoint // degree n = k} ≃ Fin (3 * k + 1) :=
  (sliceEquiv.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype k)

/-- The split-cone multiplicity appearing in the paper's local Fourier series. -/
theorem card_degreeFiber (k : ℕ) : Nat.card {n : ConePoint // degree n = k} = 3 * k + 1 := by
  rw [Nat.card_congr (degreeFiberEquiv k), Nat.card_fin]

abbrev InvariantConePoint := {n : ConePoint // conjugation n.1 = n.1}

/-- Inclusion of the split cone into the full valuation lattice. Multiplicative
notation lets a valuation be a homomorphism from the local torus group. -/
def splitEmbedding : ConePoint ↪ Multiplicative (ℤ × ℤ) where
  toFun n := Multiplicative.ofAdd n.1
  inj' := fun _ _ h => Subtype.ext h

/-- Inclusion of the invariant cone into the full invariant valuation lattice. -/
def inertEmbedding : InvariantConePoint ↪ Multiplicative invariantLattice where
  toFun n := Multiplicative.ofAdd ⟨n.1.1, n.2⟩
  inj' := by
    intro n m h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Multiplicative invariantLattice => x.toAdd.1) h

/-- Invariance in integral coordinates is exactly invariance under swapping the ambient rays. -/
def invariantAmbientEquiv : InvariantConePoint ≃
    {n : AmbientCone // Prod.swap n.1 = n.1} :=
  ambientEquiv.subtypeEquiv (fun n => conjugation_fixed_iff_coordinates n.1)

/-- The inert invariant cone consists exactly of `k(v₁+v₂)` for `k : ℕ`. -/
def invariantEquiv : ℕ ≃ InvariantConePoint where
  toFun k := ⟨⟨(-(k : ℤ), 3 * (k : ℤ)), by rw [inCone_iff]; constructor <;> dsimp <;> omega⟩,
    by rw [conjugation_fixed_iff]; dsimp; ring⟩
  invFun n := (-n.1.1.1).toNat
  left_inv k := by simp
  right_inv n := by
    have hc := (inCone_iff n.1.1).mp n.1.2
    have hf := (conjugation_fixed_iff n.1.1).mp n.2
    have hn : 0 ≤ -n.1.1.1 := by omega
    have he := Int.toNat_of_nonneg hn
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> omega

@[simp]
theorem degree_invariantEquiv (k : ℕ) : degree (invariantEquiv k).1 = 2 * k := by
  change ((-(k : ℤ)) + 3 * k).toNat = 2 * k
  omega

theorem coordinates_invariantEquiv (k : ℕ) :
    coordinates (invariantEquiv k).1.1 = ((k : ℚ), (k : ℚ)) := by
  ext <;> simp [invariantEquiv, coordinates]; ring

end Cubic.PoissonSummation.LatticeCone
