import Cubic.ToricHeights.TraceOneCharacters

/-!
# Splitting the original cyclic group algebra by its characters

Over a commutative rational algebra containing a root of `X²+X+1`, evaluation
at `1, ζ, ζ²` identifies the convolution algebra with three copies of
the coefficient algebra. The inverse is explicit three-term Fourier interpolation.
This includes coefficient algebras with nilpotents or zero divisors.
This gives injectivity of the two nontrivial characters on augmentation-one
units, needed to determine the kernel of the quotient-character map.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.GroupAlgebraSplitting

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters

variable {K : Type*} [CommRing K] [Algebra ℚ K]
variable (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0)

/-- All three evaluations, with coordinatewise multiplication in the target. -/
def toSpectral : GroupAlgebra K →ₐ[K] K × K × K :=
  (augmentation K).prod ((evaluation K ζ (root_cube ζ hζ)).prod
    (evaluation K (ζ ^ 2) (square_root_cube ζ hζ)))

omit [Algebra ℚ K] in
theorem toSpectral_coordinates (x y z : K) :
    toSpectral ζ hζ (coordinates K x y z) =
      (x + y + z, x + y * ζ + z * ζ ^ 2, x + y * ζ ^ 2 + z * ζ) := by
  have hfour : (ζ ^ 2) ^ 2 = ζ := by rw [← pow_mul, root_fourth ζ hζ]
  simp [toSpectral, augmentation, evaluation_coordinates, hfour]

/-- Interpolation from the three character values. -/
def ofSpectral (v : K × K × K) : GroupAlgebra K :=
  coordinates K (algebraMap ℚ K (1 / 3) * (v.1 + v.2.1 + v.2.2))
    (algebraMap ℚ K (1 / 3) * (v.1 + ζ ^ 2 * v.2.1 + ζ * v.2.2))
    (algebraMap ℚ K (1 / 3) * (v.1 + ζ * v.2.1 + ζ ^ 2 * v.2.2))

private theorem three_mul_third : (3 : K) * algebraMap ℚ K (1 / 3) = 1 := by
  have h := congrArg (algebraMap ℚ K) (show (3 : ℚ) * (1 / 3) = 1 by norm_num)
  simpa only [map_mul, map_ofNat, map_one] using h

theorem toSpectral_ofSpectral (v : K × K × K) :
    toSpectral ζ hζ (ofSpectral ζ v) = v := by
  obtain ⟨u, v, w⟩ := v
  have hsq : ζ ^ 2 = -1 - ζ := by linear_combination hζ
  rw [ofSpectral, toSpectral_coordinates]
  dsimp
  rw [hsq]
  apply Prod.ext
  · dsimp
    linear_combination u * (three_mul_third (K := K))
  · apply Prod.ext
    · dsimp
      linear_combination v * (three_mul_third (K := K)) +
        2 * algebraMap ℚ K (1 / 3) * (w - v) * hζ
    · dsimp
      linear_combination w * (three_mul_third (K := K)) +
        2 * algebraMap ℚ K (1 / 3) * (v - w) * hζ

theorem ofSpectral_toSpectral (f : GroupAlgebra K) :
    ofSpectral ζ (toSpectral ζ hζ f) = f := by
  have hsq : ζ ^ 2 = -1 - ζ := by linear_combination hζ
  have hfour : (ζ ^ 2) ^ 2 = ζ := by rw [← pow_mul, root_fourth ζ hζ]
  calc
    _ = coordinates K (f 0) (f 1) (f 2) := by
      simp only [ofSpectral, toSpectral, AlgHom.prod_apply, augmentation_coefficients,
        evaluation_coefficients, hfour]
      rw [hsq]
      congr 1
      · linear_combination f 0 * (three_mul_third (K := K))
      · linear_combination f 1 * (three_mul_third (K := K)) +
          2 * algebraMap ℚ K (1 / 3) * (f 2 - f 1) * hζ
      · linear_combination f 2 * (three_mul_third (K := K)) +
          2 * algebraMap ℚ K (1 / 3) * (f 1 - f 2) * hζ
    _ = f := coordinates_coefficients K f

/-- The original group algebra is diagonalized by its characters. -/
def spectralEquiv : GroupAlgebra K ≃ₐ[K] K × K × K :=
  AlgEquiv.ofBijective (toSpectral ζ hζ)
    ⟨Function.LeftInverse.injective (ofSpectral_toSpectral ζ hζ),
      Function.RightInverse.surjective (toSpectral_ofSpectral ζ hζ)⟩

/-- On augmentation-one units the two nontrivial character values determine
the element, since the remaining character is already one. -/
theorem characters_injective :
    Function.Injective ((firstCharacter ζ hζ).prod (secondCharacter ζ hζ)) := by
  intro g h hchars
  apply Subtype.ext
  apply Units.ext
  apply (spectralEquiv ζ hζ).injective
  change (augmentation K (g.val : GroupAlgebra K), evaluation K ζ _ (g.val : GroupAlgebra K),
    evaluation K (ζ ^ 2) _ (g.val : GroupAlgebra K)) =
      (augmentation K (h.val : GroupAlgebra K), evaluation K ζ _ (h.val : GroupAlgebra K),
        evaluation K (ζ ^ 2) _ (h.val : GroupAlgebra K))
  rw [augmentation_traceOneUnit, augmentation_traceOneUnit]
  have h₁ := congrArg (fun q : Kˣ × Kˣ => (q.1 : K)) hchars
  have h₂ := congrArg (fun q : Kˣ × Kˣ => (q.2 : K)) hchars
  exact Prod.ext rfl (Prod.ext h₁ h₂)

/-- Arbitrary invertible spectral values give an augmentation-one unit, by the
inverse algebra isomorphism. This concerns the cover, not its quotient. -/
theorem characters_surjective :
    Function.Surjective ((firstCharacter ζ hζ).prod (secondCharacter ζ hζ)) := by
  rintro ⟨a, b⟩
  let v : (K × K × K)ˣ :=
    ⟨(1, (a : K), (b : K)), (1, (↑a⁻¹ : K), (↑b⁻¹ : K)),
      by ext <;> simp, by ext <;> simp⟩
  let u : (GroupAlgebra K)ˣ := Units.map (spectralEquiv ζ hζ).symm.toMonoidHom v
  have hu : toSpectral ζ hζ (u : GroupAlgebra K) = (1, (a : K), (b : K)) := by
    exact (spectralEquiv ζ hζ).apply_symm_apply _
  have hunit : u ∈ traceOneUnits K := by
    apply Units.ext
    exact congrArg Prod.fst hu
  refine ⟨⟨u, hunit⟩, ?_⟩
  apply Prod.ext
  · apply Units.ext
    exact congrArg (fun q : K × K × K => q.2.1) hu
  · apply Units.ext
    exact congrArg (fun q : K × K × K => q.2.2) hu

/-- The augmentation-one cover is the split two-dimensional multiplicative
group over a commutative rational algebra containing the third roots of unity. -/
def charactersEquiv : traceOneUnits K ≃* Kˣ × Kˣ :=
  MulEquiv.ofBijective ((firstCharacter ζ hζ).prod (secondCharacter ζ hζ))
    ⟨characters_injective ζ hζ, characters_surjective ζ hζ⟩

end Cubic.QuadraticCorrespondence.GroupAlgebraSplitting
