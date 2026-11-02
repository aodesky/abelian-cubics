import Cubic.SurfaceGeometry.AffineModelData
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree

noncomputable section

namespace Cubic.SurfaceGeometry.AffineModelIntegrality

open MvPolynomial AffineModelData

theorem equation_at {K : Type*} [CommRing K] (P : CoordinateRing ℤ →+* K) :
    CubicData.affineRelation (P (coordinate ℤ 0)) (P (coordinate ℤ 1))
      (P (coordinate ℤ 2)) = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span {equation ℤ}) (equation ℤ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have he := congrArg P h
  simpa only [equation, CubicData.affineRelation, coordinate, map_add, map_sub,
    map_mul, map_pow, map_ofNat, map_zero] using he

/-- The monic quadratic and integral closedness used in both integrality tests. -/
theorem root_in_base (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsIntegrallyClosed R]
    (a b : R) (d : K)
    (h : CubicData.affineRelation (algebraMap R K a) (algebraMap R K b) d = 0) :
    ∃ c : R, algebraMap R K c = d := by
  apply IsIntegrallyClosed.algebraMap_eq_of_integral
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (-(a + 3 * b)) * Polynomial.X +
    Polynomial.C (a ^ 3 + 6 * a * b + 9 * b ^ 2 - b), ?_, ?_⟩
  · monicity!
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow]
    simp only [map_neg, map_add, map_sub, map_mul, map_pow, map_ofNat]
    dsimp [CubicData.affineRelation] at h
    linear_combination h

theorem functions_mem {K : Type*} [CommRing K] (P : CoordinateRing ℤ →+* K)
    (S : Subring K) (hc : ∀ i, P (coordinate ℤ i) ∈ S) : ∀ f, P f ∈ S := by
  intro f
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective f
  let φ : AffinePolynomial ℤ →+* K := P.comp (Ideal.Quotient.mk _)
  change φ p ∈ S
  induction p using MvPolynomial.induction_on with
  | C z => rw [MvPolynomial.hom_C]; exact intCast_mem S z
  | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact S.mul_mem hp (hc i)

theorem global_integrality (P : CoordinateRing ℤ →+* ℚ) :
    (∀ f, ∃ z : ℤ, P f = z) ↔
      (∃ a : ℤ, P (coordinate ℤ 0) = a) ∧ (∃ b : ℤ, P (coordinate ℤ 1) = b) := by
  refine ⟨fun h => ⟨h _,h _⟩, ?_⟩
  rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  have he := equation_at P
  rw [ha,hb] at he
  obtain ⟨d,hd⟩ := root_in_base ℤ ℚ a b (P (coordinate ℤ 2)) he
  have hmem := functions_mem P (Int.castRingHom ℚ).range (by
    intro i
    fin_cases i
    · exact ⟨a,ha.symm⟩
    · exact ⟨b,hb.symm⟩
    · exact ⟨d,hd⟩)
  intro f
  obtain ⟨z,hz⟩ := hmem f
  exact ⟨z,hz.symm⟩

theorem local_integrality (p : ℕ) [Fact p.Prime] (P : CoordinateRing ℤ →+* ℚ_[p]) :
    (∀ f, ‖P f‖ ≤ 1) ↔ ‖P (coordinate ℤ 0)‖ ≤ 1 ∧ ‖P (coordinate ℤ 1)‖ ≤ 1 := by
  refine ⟨fun h => ⟨h _,h _⟩, ?_⟩
  rintro ⟨ha,hb⟩
  let a : ℤ_[p] := ⟨P (coordinate ℤ 0),ha⟩
  let b : ℤ_[p] := ⟨P (coordinate ℤ 1),hb⟩
  obtain ⟨d,hd⟩ := root_in_base ℤ_[p] ℚ_[p] a b (P (coordinate ℤ 2)) (equation_at P)
  have hc : P (coordinate ℤ 2) ∈ PadicInt.subring p := by
    rw [← hd]
    exact d.property
  exact functions_mem P (PadicInt.subring p) (by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc)

theorem integral_in_torus (P : CoordinateRing ℤ →+* ℚ)
    (h : ∀ f, ∃ z : ℤ, P f = z) : 1 - 3 * P (coordinate ℤ 0) ≠ 0 := by
  obtain ⟨a,ha⟩ := h (coordinate ℤ 0)
  rw [ha]
  exact_mod_cast (show (1 - 3 * a : ℤ) ≠ 0 by omega)

end Cubic.SurfaceGeometry.AffineModelIntegrality
