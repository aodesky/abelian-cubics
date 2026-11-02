import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.MeasureTheory.Group.Integral

/-!
# Integration against a unitary character

A small shared interface for the local Fourier integrals in the paper. The measure,
test function and character are explicit; neither the cubic height nor a Haar
normalization is built into this definition. This uses mathlib's integral and dual
directly and does not introduce a second harmonic-analysis framework.
-/

noncomputable section

namespace Cubic.PoissonSummation

open MeasureTheory

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]

/-- Fourier integral with the inverse-character convention of the paper.
As for mathlib's integral, existence must be justified separately by integrability. -/
def characterIntegral (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) : ℂ :=
  ∫ x, f x * ((χ x : Circle) : ℂ)⁻¹ ∂μ

omit [MeasurableSpace G] in
/-- The unitary twist does not alter the pointwise norm. -/
theorem norm_mul_character_inv (f : G → ℂ) (χ : PontryaginDual G) (x : G) :
    ‖f x * ((χ x : Circle) : ℂ)⁻¹‖ = ‖f x‖ := by
  simp

/-- The elementary local bound underlying trivial-character domination.
Identifying this integral of norms with the real-parameter height is a separate step. -/
theorem norm_characterIntegral_le (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) :
    ‖characterIntegral μ f χ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  simpa [characterIntegral] using
    norm_integral_le_integral_norm (f := fun x => f x * ((χ x : Circle) : ℂ)⁻¹)

@[simp]
theorem characterIntegral_one (μ : Measure G) (f : G → ℂ) :
    characterIntegral μ f 1 = ∫ x, f x ∂μ := by
  have h : ∀ x : G, (1 : PontryaginDual G) x = 1 := fun _ => rfl
  simp [characterIntegral, h]

/-- Translation invariance forces the Fourier transform to vanish at a character
which is nontrivial on an invariant direction. -/
theorem characterIntegral_eq_zero_of_invariant [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (f : G → ℂ) (χ : PontryaginDual G)
    (k : G) (hf : ∀ x, f (k * x) = f x) (hχ : χ k ≠ 1) :
    characterIntegral μ f χ = 0 := by
  have h := integral_mul_left_eq_self (μ := μ)
    (fun x => f x * ((χ x : Circle) : ℂ)⁻¹) k
  simp only [hf, map_mul, Circle.coe_mul, mul_inv] at h
  have he : (fun x => f x * (((χ k : Circle) : ℂ)⁻¹ * ((χ x : Circle) : ℂ)⁻¹)) =
      (fun x => ((χ k : Circle) : ℂ)⁻¹ * (f x * ((χ x : Circle) : ℂ)⁻¹)) := by
    funext x
    ring
  rw [he, integral_const_mul] at h
  by_contra hn
  have hc : ((χ k : Circle) : ℂ)⁻¹ = 1 :=
    mul_right_cancel₀ hn (h.trans (one_mul _).symm)
  exact hχ (Circle.coe_injective (inv_eq_one.mp hc))

end Cubic.PoissonSummation
