import Cubic.QuadraticCorrespondence.QuotientPolynomialConverse
import CubicTargets.Introduction.PolynomialWeights

/-!
# Proof of `eqn:polynomialWeights`

The paper proves the weights through `prop:cyclotomicParametrization`: the fibre of
the characteristic-polynomial map over an admissible `f` has two points when `f` is
separable and one point otherwise (`QuotientPolynomialConverse.separable_fibre_card`,
`repeated_fibre_card`). Here we add that a rational polynomial is inseparable exactly
when it has a double complex root.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.PolynomialWeights

open Polynomial CorrespondencePolynomials
open CubicTargets.Introduction.PolynomialWeights (HasDoubleRoot)

/-- A rational polynomial `f ≠ 0` is inseparable iff it has a repeated complex root. -/
theorem not_separable_iff {f : ℚ[X]} (hf : f ≠ 0) : ¬ f.Separable ↔ HasDoubleRoot f := by
  have hm : f.map (algebraMap ℚ ℂ) ≠ 0 := (Polynomial.map_ne_zero_iff
    (algebraMap ℚ ℂ).injective).mpr hf
  rw [← Polynomial.separable_map (algebraMap ℚ ℂ),
    ← Polynomial.nodup_roots_iff_of_splits hm (IsAlgClosed.splits _)]
  classical
  constructor
  · intro h
    rw [Multiset.nodup_iff_count_le_one] at h
    push_neg at h
    obtain ⟨r, hr⟩ := h
    refine ⟨r, (le_rootMultiplicity_iff hm).mp ?_⟩
    rw [← count_roots]
    omega
  · classical
    rintro ⟨r, hr⟩ hnd
    have h2 : 2 ≤ (f.map (algebraMap ℚ ℂ)).roots.count r := by
      rw [count_roots]; exact (le_rootMultiplicity_iff hm).mpr hr
    have := Multiset.nodup_iff_count_le_one.mp hnd r
    omega

theorem cubic_ne_zero (a b : ℚ) : cubic a b ≠ 0 := by
  intro h
  have := congrArg (fun f : ℚ[X] => f.coeff 3) h
  simp [cubic, coeff_X_pow] at this

theorem «eqn:polynomialWeights» : CubicTargets.Introduction.PolynomialWeights.Claim := by
  intro a b h
  refine ⟨QuotientPolynomialConverse.finite_fibre, ?_⟩
  by_cases hs : (cubic a b).Separable
  · rw [if_neg (fun hd => (not_separable_iff (cubic_ne_zero a b)).mpr hd hs)]
    exact QuotientPolynomialConverse.separable_fibre_card h hs
  · rw [if_pos ((not_separable_iff (cubic_ne_zero a b)).mp hs)]
    exact QuotientPolynomialConverse.repeated_fibre_card h hs

end Cubic.QuadraticCorrespondence.PolynomialWeights
