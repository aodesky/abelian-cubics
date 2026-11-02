import Cubic.ToricHeights.WeightVectors
import Cubic.ToricHeights.QuotientFiniteHeight
import Cubic.ToricHeights.ArchimedeanQuotientLogarithm

/-!
# Local heights as maxima over weight vectors (`eqn:localHeight`)

The proof of `prop:canonicalHeight` uses [Fulton, p. 68] to express the
support function of `3D₀` through the weight vectors of `lemma:heightformula`.
For this fan the polyhedron `P = {u ≥ 3φ₀}` is the triangle with vertices
`0, 3v₁^∨, 3v₂^∨`, whose lattice points are the four weights
`0, a'+b', 2a'+b', a'+2b'`. The needed fact is checked directly:
`3φ₀` is the minimum of the pairings with these four weights
(`triangle_min`).

The local height factor is `q_w^{-3φ₀(ℓ_w(x))/[E:ℚ]}`, and the pairing of `ℓ_w(x)`
with a character is its order, so `q_w^{-⟨u,ℓ_w(x)⟩} = |χ^u(x)|_w` with the
paper's normalization `|·|_w = q_w^{-ord_w(·)}`. Hence each local factor is
`max(1, |χ^{a'+b'}(x)|_w, |χ^{2a'+b'}(x)|_w, |χ^{a'+2b'}(x)|_w)^{1/[E:ℚ]}`.
The values of these characters are `1-3e₂` and the two conjugate
weight-vector values `z±` (`WeightVectors`).

In Lean the height of `O(3D₀)` is `inverseHeight (-3) 0`, since the height is
the inverse height at negated divisor parameters.
-/

noncomputable section

namespace Cubic.ToricHeights.LocalWeightHeight

open scoped TensorProduct
open Cubic.QuadraticCorrespondence
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open CyclotomicTorusGalois QuotientLocalCharacters

/-- Fulton's description of `3φ₀` as a minimum over the lattice points of the triangle. -/
theorem triangle_min (x y : ℝ) :
    3 * min 0 (min x y) = min (min 0 (x + y)) (min (3 * x) (3 * y)) := by
  simp only [min_def]
  split_ifs <;> linarith

/-- The paper's normalized absolute value `|·|_w = q_w^{-ord_w(·)}`, from an order. -/
def localAbs (q o : ℝ) : ℝ := q ^ (-o)

/-- The local factor of the height of `O(3D₀)` as a maximum over the four weights. -/
theorem rpow_support_eq_max {q D : ℝ} (hq : 1 < q) (n : ℝ × ℝ) (o₁₁ o₂₁ o₁₂ : ℝ)
    (h₁₁ : n.1 + n.2 = o₁₁) (h₂₁ : 3 * n.1 = o₂₁) (h₁₂ : 3 * n.2 = o₁₂) :
    q ^ (-(3 * min 0 (min n.1 n.2)) / D) =
      (max (max 1 (localAbs q o₁₁)) (max (localAbs q o₂₁) (localAbs q o₁₂))) ^ (1 / D) := by
  have hanti : Antitone (fun t : ℝ => q ^ (-t)) := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hab)
  rw [triangle_min, h₁₁, h₂₁, h₁₂, neg_div, ← mul_one_div, ← neg_mul,
    Real.rpow_mul (by linarith)]
  congr 1
  rw [hanti.map_min, hanti.map_min, hanti.map_min]
  simp [localAbs]

private theorem supportFunction_three (n : ℝ × ℝ) :
    supportFunction (-3) 0 n = ((-(3 * min 0 (min n.1 n.2)) : ℝ) : ℂ) := by
  simp [supportFunction]

private theorem cpow_real {q : ℝ} (hq : 0 ≤ q) (x : ℝ) : (q : ℂ) ^ (x : ℂ) = ((q ^ x : ℝ) : ℂ) :=
  (Complex.ofReal_cpow hq x).symm

section Finite

variable (A : Type*) [CommRing A] [Algebra ℚ A]
variable {L : Type*} [Field L]
variable (place : E ⊗[ℚ] A →+* L) (ord : Lˣ →* Multiplicative ℤ)

/-- The paper's `|χ^m(x)|_w` at a finite place with residue cardinality `q`. -/
def characterAbs (q : ℕ) (P : quotientFixedRing →ₐ[ℚ] A) (m : ℤ × ℤ) : ℝ :=
  localAbs q ((ord (localCharacter A place P (Multiplicative.ofAdd m))).toAdd : ℝ)

/-- `eqn:localHeight` at a finite place of `E`: the local factor of the height of
`O(3D₀)` is the maximum over the four weight vectors, raised to `1/[E:ℚ]`. -/
theorem finite_localHeight (q : ℕ) (hq : 1 < q) (P : quotientFixedRing →ₐ[ℚ] A) :
    (q : ℂ) ^ (supportFunction (-3) 0
        (QuotientFiniteHeight.realCoordinates (localCocharacter A place ord P)) /
          Module.finrank ℚ E) =
      ((max (max 1 (characterAbs A place ord q P (1, 1)))
        (max (characterAbs A place ord q P (2, 1)) (characterAbs A place ord q P (1, 2)))) ^
          (1 / 2 : ℝ) : ℝ) := by
  have hpair := localCocharacter_pairing A place ord P
  have h₁₁ := hpair (1, 1)
  have h₂₁ := hpair (2, 1)
  have h₁₂ := hpair (1, 2)
  simp only [CharacterLattice.pullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h₁₁ h₂₁ h₁₂
  norm_num at h₁₁ h₂₁ h₁₂
  rw [supportFunction_three, CyclotomicField.finrank_eq_two]
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  rw [show ((q : ℕ) : ℂ) = ((q : ℝ) : ℂ) by simp, show ((2 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) by simp,
    ← Complex.ofReal_div, cpow_real (by positivity)]
  congr 1
  apply rpow_support_eq_max hq'
  · simp only [QuotientFiniteHeight.realCoordinates]
    exact_mod_cast h₁₁
  · simp only [QuotientFiniteHeight.realCoordinates]
    exact_mod_cast h₂₁
  · simp only [QuotientFiniteHeight.realCoordinates]
    exact_mod_cast h₁₂

end Finite

section Archimedean

open ArchimedeanQuotientLogarithm

/-- The paper's `|χ^m(x)|_w = ‖χ^m(x)‖²` at the complex place, from `q_w = e²`. -/
def archimedeanAbs (P : ArchimedeanQuotientLogarithm.Points) (m : ℤ × ℤ) : ℝ :=
  localAbs (Real.exp 2)
    ((order (localCharacter ℝ CyclotomicArchimedean.place.toRingHom P
      (Multiplicative.ofAdd m))).toAdd)

theorem archimedeanAbs_eq (P : ArchimedeanQuotientLogarithm.Points) (m : ℤ × ℤ) :
    archimedeanAbs P m =
      ‖((localCharacter ℝ CyclotomicArchimedean.place.toRingHom P (Multiplicative.ofAdd m) :
        ℂˣ) : ℂ)‖ ^ 2 := by
  set z := localCharacter ℝ CyclotomicArchimedean.place.toRingHom P (Multiplicative.ofAdd m)
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  simp only [archimedeanAbs, localAbs, order, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    neg_neg]
  rw [Real.rpow_def_of_pos (Real.exp_pos 2), Real.log_exp]
  change Real.exp (2 * Real.log ‖(z : ℂ)‖) = _
  rw [    show 2 * Real.log ‖(z : ℂ)‖ = Real.log (‖(z : ℂ)‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (by positivity)]

/-- `eqn:localHeight` at the complex place. -/
theorem archimedean_localHeight (P : ArchimedeanQuotientLogarithm.Points) :
    ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 P =
      ((max (max 1 (archimedeanAbs P (1, 1)))
        (max (archimedeanAbs P (2, 1)) (archimedeanAbs P (1, 2)))) ^ (1 / 2 : ℝ) : ℝ) := by
  have hpair := ArchimedeanQuotientLogarithm.localCocharacter_pairing P
  have h₁₁ := hpair (1, 1)
  have h₂₁ := hpair (2, 1)
  have h₁₂ := hpair (1, 2)
  simp only [CharacterLattice.pullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h₁₁ h₂₁ h₁₂
  norm_num at h₁₁ h₂₁ h₁₂
  rw [ArchimedeanQuotientLogarithm.inverseHeight, supportFunction_three,
    CyclotomicField.finrank_eq_two, show ((2 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) by simp,
    ← Complex.ofReal_div, cpow_real (Real.exp_pos 2).le]
  congr 1
  exact rpow_support_eq_max (by linarith [Real.add_one_lt_exp (two_ne_zero (α := ℝ))]) _ _ _ _
    h₁₁ h₂₁ h₁₂

end Archimedean

end Cubic.ToricHeights.LocalWeightHeight
