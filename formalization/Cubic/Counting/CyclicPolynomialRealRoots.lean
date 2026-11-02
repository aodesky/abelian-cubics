import Cubic.QuadraticCorrespondence.CorrespondencePolynomials
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The paper's complex-conjugation argument for cyclic cubic polynomials

Complex conjugation restricts to an element of the Galois group of the
splitting field. Its square is one, so a group of order three forces it to be
the identity. Consequently every complex root is real.
-/

noncomputable section

namespace Cubic.Counting.CyclicPolynomialRealRoots

open Polynomial Cubic.QuadraticCorrespondence.CorrespondencePolynomials

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

theorem conjugation_eq_one {f : ℚ[X]} (hf : HasCyclicCubicGaloisGroup f) :
    Polynomial.Gal.restrict f ℂ (Complex.conjAe.restrictScalars ℚ) = 1 := by
  obtain ⟨e⟩ := hf
  let c := Polynomial.Gal.restrict f ℂ (Complex.conjAe.restrictScalars ℚ)
  have hc₂ : c ^ 2 = 1 := by
    change (Polynomial.Gal.restrict f ℂ _) ^ 2 = 1
    rw [← map_pow, show (Complex.conjAe.restrictScalars ℚ) ^ 2 = 1 from
      AlgEquiv.ext Complex.conj_conj, map_one]
  have hcard : Fintype.card f.Gal = 3 := by
    rw [Fintype.card_congr e.toEquiv]
    decide
  have hc₃ : c ^ 3 = 1 := by simpa only [hcard] using (pow_card_eq_one (x := c))
  change c = 1
  calc
    c = c ^ 2 * c := by rw [hc₂, one_mul]
    _ = c ^ 3 := (pow_succ c 2).symm
    _ = 1 := hc₃

theorem root_im_zero {f : ℚ[X]} (hf : HasCyclicCubicGaloisGroup f)
    (z : f.rootSet ℂ) : (z : ℂ).im = 0 := by
  have h := Polynomial.Gal.galActionHom_restrict
    (p := f) (E := ℂ) (Complex.conjAe.restrictScalars ℚ) z
  rw [conjugation_eq_one hf, map_one] at h
  exact Complex.conj_eq_iff_im.mp h.symm

theorem splits_real {f : ℚ[X]} (hf : HasCyclicCubicGaloisGroup f) :
    (f.map (algebraMap ℚ ℝ)).Splits := by
  apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _)
  intro z hz
  have he : ((f.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)) =
      f.map (algebraMap ℚ ℂ) := by rw [map_map, ← IsScalarTower.algebraMap_eq]
  rw [he] at hz
  have hroot : z ∈ f.rootSet ℂ := by
    simpa only [rootSet, Finset.mem_coe, Multiset.mem_toFinset] using hz
  have hi := root_im_zero hf ⟨z, hroot⟩
  exact ⟨z.re, Complex.ext (by rfl) (by simpa using hi.symm)⟩

end Cubic.Counting.CyclicPolynomialRealRoots
