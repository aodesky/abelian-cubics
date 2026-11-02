import Cubic.SurfaceGeometry.BoundaryData

/-! The reduced A=0 section of the cubic is exactly the projective line A=B=0.
The calculation takes place in the original homogeneous coordinate ring. -/

noncomputable section

namespace Cubic.SurfaceGeometry.BoundaryLine

open MvPolynomial CubicPresentationData BoundaryData

theorem restriction_X (i : Fin 4) : restriction (X i) = ![0, 0, X 0, X 1] i := by
  simp only [restriction, aeval_X]

theorem restriction_inclusion (p : MvPolynomial (Fin 2) ℤ) :
    restriction (inclusion p) = p := by
  have h : restriction.comp inclusion = AlgHom.id ℤ _ := by
    ext i : 1
    fin_cases i <;> simp [restriction, inclusion]
  exact DFunLike.congr_fun h p

theorem restriction_surjective : Function.Surjective restriction :=
  fun p => ⟨inclusion p, restriction_inclusion p⟩

theorem restriction_kernel : RingHom.ker restriction.toRingHom = lineIdeal := by
  have hA : (X 0 : CubicRing) ∈ lineIdeal := Ideal.subset_span (by simp)
  have hB : (X 1 : CubicRing) ∈ lineIdeal := Ideal.subset_span (by simp)
  have hA' : Ideal.Quotient.mk lineIdeal (X 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hA
  have hB' : Ideal.Quotient.mk lineIdeal (X 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hB
  have h : ((Ideal.Quotient.mkₐ ℤ lineIdeal).comp inclusion).comp restriction =
      Ideal.Quotient.mkₐ ℤ lineIdeal := by
    ext i : 1
    fin_cases i <;> simp [restriction, inclusion, Ideal.Quotient.mkₐ_eq_mk, hA', hB']
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := DFunLike.congr_fun h p
    change Ideal.Quotient.mk lineIdeal (inclusion (restriction p)) =
      Ideal.Quotient.mk lineIdeal p at he
    have hp' : restriction p = 0 := hp
    simpa [hp'] using he.symm
  · rw [lineIdeal, Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> exact show restriction _ = 0 from by simp [restriction]

def presentation : (CubicRing ⧸ lineIdeal) ≃ₐ[ℤ] MvPolynomial (Fin 2) ℤ :=
  (Ideal.quotientEquivAlgOfEq ℤ restriction_kernel.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective restriction_surjective)

theorem line_prime : lineIdeal.IsPrime := by
  rw [← restriction_kernel]
  exact RingHom.ker_isPrime _

theorem cubic_restricts_zero : restriction cubic = 0 := by
  simp only [cubic, CubicData.F, map_add, map_sub, map_mul, map_pow,
    map_ofNat, restriction_X]
  norm_num

theorem hyperplane_le_line : hyperplaneIdeal ≤ lineIdeal := by
  rw [hyperplaneIdeal, Ideal.span_le]
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · rw [← restriction_kernel]
    exact cubic_restricts_zero
  · exact Ideal.subset_span (by simp)

theorem reduced_hyperplane : hyperplaneIdeal.radical = lineIdeal := by
  apply le_antisymm ((line_prime.radical_le_iff).mpr hyperplane_le_line)
  rw [lineIdeal, Ideal.span_le]
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have hA : (X 0 : CubicRing) ∈ hyperplaneIdeal := Ideal.subset_span (by simp)
  rcases hp with rfl | rfl
  · exact Ideal.le_radical hA
  · refine ⟨3, ?_⟩
    have hc : cubic ∈ hyperplaneIdeal := Ideal.subset_span (by simp)
    have he : (X 1 : CubicRing) ^ 3 = cubic - X 0 *
        (X 3 ^ 2 - X 1 * X 3 + 3 * X 2 * X 3 + X 0 * X 2 -
          6 * X 1 * X 2 + 9 * X 2 ^ 2) := by
      dsimp [cubic, CubicData.F]
      ring
    rw [he]
    exact hyperplaneIdeal.sub_mem hc (hyperplaneIdeal.mul_mem_right _ hA)

/-- The scheme-theoretic hyperplane section retains the multiplicity three. -/
theorem hyperplane_equation {R : Type*} [CommRing R] (B C D : R) :
    CubicData.F 0 B C D = B ^ 3 := by simp [CubicData.F]

end Cubic.SurfaceGeometry.BoundaryLine
