import Cubic.QuadraticCorrespondence.CyclotomicInertField

/-!
# The integral cyclotomic basis at an inert place

Prove `‖a+bζ‖ = max ‖a‖ ‖b‖` for the extension norm. Conjugation
preserves the spectral norm, and the root difference `2ζ+1` has norm one
because its square is `-3`. This supplies the unramified norm calculation
needed to construct the integer-valued local valuation.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicInertField

open Polynomial

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]

/-- The distinguished cube root in the quotient presentation. -/
def zeta : Extension p := AdjoinRoot.root (cyclotomic 3 ℚ_[p])

theorem zeta_relation : zeta p ^ 2 + zeta p + 1 = 0 := by
  have h : (AdjoinRoot.root (cyclotomic 3 ℚ_[p])) ^ 2 +
      AdjoinRoot.root (cyclotomic 3 ℚ_[p]) + 1 = 0 := by
    simpa [cyclotomic_three] using AdjoinRoot.eval₂_root (cyclotomic 3 ℚ_[p])
  exact congrArg (quotientEquiv p).symm h |>.trans (by simp)

private def conjugationHom : Extension p →ₐ[ℚ_[p]] Extension p :=
  AdjoinRoot.liftAlgHom (cyclotomic 3 ℚ_[p]) (Algebra.ofId ℚ_[p] (Extension p))
    (-1 - zeta p) (by
      simpa [cyclotomic_three] using
        CyclotomicLocalAlgebra.other_root (zeta p) (zeta_relation p))

@[simp]
private theorem conjugationHom_zeta : conjugationHom p (zeta p) = -1 - zeta p := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem conjugationHom_comp :
    (conjugationHom p).comp (conjugationHom p) = .id ℚ_[p] (Extension p) := by
  apply AdjoinRoot.algHom_ext
  change conjugationHom p (conjugationHom p (zeta p)) = zeta p
  simp only [conjugationHom_zeta, map_sub, map_neg, map_one]
  ring

/-- The nontrivial automorphism of the quadratic extension, specified on its root. -/
def conjugation : Extension p ≃ₐ[ℚ_[p]] Extension p :=
  AlgEquiv.ofAlgHom (conjugationHom p) (conjugationHom p)
    (conjugationHom_comp p) (conjugationHom_comp p)

@[simp]
theorem conjugation_zeta : conjugation p (zeta p) = -1 - zeta p := conjugationHom_zeta p

@[simp]
theorem norm_conjugation (x : Extension p) : ‖conjugation p x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv (conjugation p) x).symm

@[simp]
theorem norm_zeta : ‖zeta p‖ = 1 := by
  have h : zeta p ^ 3 = 1 := by linear_combination (zeta p - 1) * zeta_relation p
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 3 ≠ 0)).mp
  simpa only [norm_pow, norm_one] using congrArg norm h

/-- The two roots differ by an integral unit at every inert prime, including two. -/
theorem norm_root_difference : ‖2 * zeta p + 1‖ = 1 := by
  have hp3 : ¬ p ∣ 3 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · have := (Fact.out : p % 3 = 2)
      omega
  have hq : ‖(3 : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp3)
  have hthree : ‖(3 : Extension p)‖ = 1 := by
    simpa only [map_ofNat] using (norm_algebraMap p (3 : ℚ_[p])).trans hq
  have hs : (2 * zeta p + 1) ^ 2 = -3 := by linear_combination 4 * zeta_relation p
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 2 ≠ 0)).mp
  rw [← norm_pow, hs, norm_neg, hthree]

/-- Coordinates in the cyclotomic power basis. -/
def linear (a b : ℚ_[p]) : Extension p :=
  algebraMap ℚ_[p] (Extension p) a + algebraMap ℚ_[p] (Extension p) b * zeta p

theorem conjugation_linear (a b : ℚ_[p]) :
    conjugation p (linear p a b) =
      algebraMap ℚ_[p] (Extension p) a + algebraMap ℚ_[p] (Extension p) b * (-1 - zeta p) := by
  simp [linear]

private theorem norm_add_le_max (x y : Extension p) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  isNonarchimedean_spectralNorm x y

/-- Neither coefficient can have larger norm than the represented element. -/
theorem coefficients_norm_le (a b : ℚ_[p]) :
    ‖a‖ ≤ ‖linear p a b‖ ∧ ‖b‖ ≤ ‖linear p a b‖ := by
  have hb : algebraMap ℚ_[p] (Extension p) b * (2 * zeta p + 1) =
      linear p a b - conjugation p (linear p a b) := by
    rw [conjugation_linear]
    simp only [linear]
    ring
  have hbn : ‖b‖ ≤ ‖linear p a b‖ := by
    calc
      ‖b‖ = ‖algebraMap ℚ_[p] (Extension p) b * (2 * zeta p + 1)‖ := by
        simp [norm_mul, norm_root_difference]
      _ = ‖linear p a b - conjugation p (linear p a b)‖ := congrArg norm hb
      _ ≤ max ‖linear p a b‖ ‖conjugation p (linear p a b)‖ := by
        simpa only [sub_eq_add_neg, norm_neg] using
          norm_add_le_max p (linear p a b) (-conjugation p (linear p a b))
      _ = ‖linear p a b‖ := by simp
  refine ⟨?_, hbn⟩
  have ha : algebraMap ℚ_[p] (Extension p) a =
      linear p a b - algebraMap ℚ_[p] (Extension p) b * zeta p := by simp [linear]
  calc
    ‖a‖ = ‖algebraMap ℚ_[p] (Extension p) a‖ := (norm_algebraMap p a).symm
    _ = ‖linear p a b - algebraMap ℚ_[p] (Extension p) b * zeta p‖ := congrArg norm ha
    _ ≤ max ‖linear p a b‖ ‖b‖ := by
      simpa only [sub_eq_add_neg, norm_neg, norm_mul, norm_algebraMap, norm_zeta, mul_one] using
        norm_add_le_max p (linear p a b) (-(algebraMap ℚ_[p] (Extension p) b * zeta p))
    _ ≤ ‖linear p a b‖ := max_le le_rfl hbn

/-- The cyclotomic power basis is orthonormal for the extension of the p-adic norm. -/
theorem norm_linear (a b : ℚ_[p]) : ‖linear p a b‖ = max ‖a‖ ‖b‖ := by
  apply le_antisymm
  · simpa only [linear, norm_mul, norm_algebraMap, norm_zeta, mul_one] using
      norm_add_le_max p (algebraMap ℚ_[p] (Extension p) a)
        (algebraMap ℚ_[p] (Extension p) b * zeta p)
  · exact max_le (coefficients_norm_le p a b).1 (coefficients_norm_le p a b).2

/-- Every element has coordinates in the displayed cyclotomic basis. -/
theorem exists_linear (x : Extension p) : ∃ a b : ℚ_[p], x = linear p a b := by
  let pb : PowerBasis ℚ_[p] (Extension p) := AdjoinRoot.powerBasis' (cyclotomic.monic 3 ℚ_[p])
  obtain ⟨f, hdeg, hf⟩ := pb.exists_eq_aeval x
  have hd : f.natDegree < 2 := by
    simpa only [pb, AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic] using hdeg
  have he := f.eq_X_add_C_of_degree_le_one
    (degree_le_of_natDegree_le (Nat.le_of_lt_succ hd))
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hf, he]
  simp [linear, pb, zeta, add_comm]

/-- The extension norm takes the same values as the p-adic norm on the base field. -/
theorem exists_norm_eq_padic (x : Extension p) : ∃ a : ℚ_[p], ‖x‖ = ‖a‖ := by
  obtain ⟨a, b, rfl⟩ := exists_linear p x
  rcases le_total ‖a‖ ‖b‖ with h | h
  · exact ⟨b, (norm_linear p a b).trans (max_eq_right h)⟩
  · exact ⟨a, (norm_linear p a b).trans (max_eq_left h)⟩

end Cubic.QuadraticCorrespondence.CyclotomicInertField
