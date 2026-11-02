import Cubic.ToricHeights.ComplexifiedCartierClasses
import Cubic.PoissonSummation.HeightParameterShift

/-!
# Divisor-class normalization of the original rational height

The integral Cartier quotient and its complexification fix the scalar
coordinate by sending the primitive strictly convex class to three. The
actual height descends through the character-divisor quotient by the proved
rational product formula. We define its value on that quotient by descent,
then prove that the height in the normalized scalar coordinate agrees with
the previously constructed height at `(s,0)`.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightDivisorNormalization

open Cubic.ToricHeights.DivisorParameters
open Cubic.ToricHeights.ComplexifiedCartierClasses
open AdelicHeightZetaData

theorem height_eq_normalized (d : ℂ × ℂ) (P : RationalPoints) :
    height d.1 d.2 (RationalAdelicEmbedding.diagonal P) =
      height (classParameter ℂ (classOf ℂ d)) 0
        (RationalAdelicEmbedding.diagonal P) := by
  rw [classParameter_classOf]
  simpa only [sub_self] using
    (HeightParameterShift.rational_height_shift d.1 d.2 d.2 P).symm

theorem height_eq_of_same_class (d e : ℂ × ℂ)
    (h : classOf ℂ d = classOf ℂ e) (P : RationalPoints) :
    height d.1 d.2 (RationalAdelicEmbedding.diagonal P) =
      height e.1 e.2 (RationalAdelicEmbedding.diagonal P) := by
  rw [height_eq_normalized, height_eq_normalized, h]

/-- The normalization used in the introductory theorem: `-sK` has scalar parameter `3s`. -/
theorem anticanonical_height (s : ℂ) (P : RationalPoints) :
    height s s (RationalAdelicEmbedding.diagonal P) =
      height (3 * s) 0 (RationalAdelicEmbedding.diagonal P) := by
  have h := height_eq_normalized (s, s) P
  simpa only [classParameter_classOf, show s + 2 * s = 3 * s by ring] using h

/-- Descend the original height itself, using the proved product-formula invariance. -/
def heightOnClass (P : RationalPoints) : Class ℂ → ℂ :=
  Quotient.lift (fun d : ℂ × ℂ => height d.1 d.2 (RationalAdelicEmbedding.diagonal P))
    (fun d e h => height_eq_of_same_class d e (Quotient.sound h) P)

@[simp]
theorem heightOnClass_classOf (P : RationalPoints) (d : ℂ × ℂ) :
    heightOnClass P (classOf ℂ d) = height d.1 d.2 (RationalAdelicEmbedding.diagonal P) := rfl

/-- The descended height on the complexified integral Cartier lattice. -/
def heightOnComplexifiedClass (P : RationalPoints) (c : ComplexifiedClass) : ℂ :=
  heightOnClass P (scalarExtension c)

theorem heightOnComplexifiedClass_ofDivisor (P : RationalPoints) (d : ℂ × ℂ) :
    heightOnComplexifiedClass P (ofDivisor d) =
      height d.1 d.2 (RationalAdelicEmbedding.diagonal P) := by
  unfold heightOnComplexifiedClass ofDivisor
  simp

/-- Height in the introductory coordinate, fixed by the primitive positive class. -/
def normalizedHeight (s : ℂ) (P : RationalPoints) : ℂ :=
  heightOnComplexifiedClass P (normalizedCoordinate.symm s)

/-- The original `s D₀` line realizes the independently normalized class height. -/
theorem normalizedHeight_eq (s : ℂ) (P : RationalPoints) :
    normalizedHeight s P = height s 0 (RationalAdelicEmbedding.diagonal P) := by
  have he : normalizedCoordinate.symm s = ofDivisor (s, 0) := by
    apply normalizedCoordinate.injective
    simp
  unfold normalizedHeight
  rw [he, heightOnComplexifiedClass_ofDivisor]

end Cubic.PoissonSummation.HeightDivisorNormalization
