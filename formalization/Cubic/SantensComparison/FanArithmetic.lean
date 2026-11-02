import Cubic.SantensComparison.FanData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Cubic.SantensComparison.FanArithmetic

open FanData Cubic.SurfaceGeometry.ResolutionData

theorem conjugate_ray (i : Fin 9) :
    rays (conjugateRay i) = ((rays i).2, (rays i).1) := by
  fin_cases i <;> decide

theorem conjugation_involutive : Function.Involutive conjugateRay := by
  intro i
  fin_cases i <;> decide

theorem conjugate_next (i : Fin 9) :
    conjugateRay (next i) = prev (conjugateRay i) := by
  fin_cases i <;> decide

theorem orbits_iff (i j : Fin 9) :
    orbitIndex i = orbitIndex j ↔ i = j ∨ conjugateRay i = j := by
  fin_cases i <;> fin_cases j <;> decide

theorem orbit_representative (i : Fin 5) :
    orbitIndex (orbitRepresentative i) = i := by
  fin_cases i <;> decide

theorem open_rays (j : Fin 9) : (∃ i, openRay i = j) ↔ boundary j = 0 := by
  fin_cases j <;> decide

theorem open_conjugation (i : Fin 4) :
    openRay (openConjugation i) = conjugateRay (openRay i) := by
  fin_cases i <;> decide

theorem invariant_characters (m : ℤ × ℤ) :
    (m.2,m.1) = m ↔ ∃ a : ℤ, m = (a,a) := by
  constructor
  · intro h
    exact ⟨m.1, Prod.ext rfl (congrArg Prod.fst h)⟩
  · rintro ⟨a, rfl⟩
    rfl

theorem units (m : ℤ × ℤ) (h : ∀ i, pairing m (openRay i) = 0) : m = 0 := by
  have h₁ := h 2
  have h₂ := h 3
  simp [pairing, openRay, rays] at h₁ h₂
  exact Prod.ext h₁ h₂

theorem regular_functions (m : ℤ × ℤ)
    (h : ∀ i, 0 ≤ pairing m (openRay i)) (h₀ : 0 ≤ pairing m 0) : m = 0 := by
  have h₁ := h 0
  have h₂ := h 1
  simp [pairing, openRay, rays] at h₀ h₁ h₂
  apply Prod.ext <;> dsimp <;> omega

theorem norm_pairing_boundary : pairing normCharacter 0 = -2 := rfl

theorem norm_pairing_open (i : Fin 4) : pairing normCharacter (openRay i) = 1 := by
  fin_cases i <;> decide

theorem exceptional_conjugates_disjoint (i : Fin 9)
    (hi : boundary i = 1) (hi₀ : i ≠ 0) :
    intersectionMatrix i (conjugateRay i) = 0 := by
  revert hi hi₀
  fin_cases i <;> decide

private theorem stable_boundary_ray (i j : Fin 9)
    (hi : boundary i = 1) (hij : i ∈ ({j, next j} : Finset (Fin 9)))
    (hc : conjugateRay i ∈ ({j, next j} : Finset (Fin 9))) : i = 0 := by
  revert hi hij hc
  fin_cases i <;> fin_cases j <;> decide

/-- All Galois-stable boundary strata are the empty face and the rational
component. The conjugate exceptional components cannot meet a real point. -/
theorem stable_faces (A : Finset (Fin 9)) : StableFace A ↔ A = ∅ ∨ A = {0} := by
  constructor
  · rintro ⟨⟨hb, j, hj⟩, hc⟩
    have hA : A ⊆ {0} := by
      intro i hi
      have h := stable_boundary_ray i j (hb i hi) (hj hi) (hj ((hc i).mp hi))
      simpa using h
    exact Finset.subset_singleton_iff.mp hA
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp, 0, by simp⟩, by simp⟩
    · constructor
      · exact ⟨by simp [boundary], 0, by simp⟩
      · intro i
        fin_cases i <;> decide

end Cubic.SantensComparison.FanArithmetic
