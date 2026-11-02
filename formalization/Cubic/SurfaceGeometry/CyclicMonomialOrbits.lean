import Cubic.ToricHeights.TernaryCyclicInvariants
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.FinCases

noncomputable section

namespace Cubic.SurfaceGeometry.CyclicMonomialOrbits

open MvPolynomial
open scoped Classical

abbrev Exponent := Fin 3 →₀ ℕ

def rotation : Exponent ≃+ Exponent := Finsupp.domCongr (finRotate 3)

theorem rotation_eq (d : Exponent) :
    rotation d = Finsupp.mapDomain (finRotate 3) d :=
  Finsupp.equivMapDomain_eq_mapDomain _ _

theorem rotation_cube (d : Exponent) : rotation (rotation (rotation d)) = d := by
  simp only [rotation_eq]
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  have he : (finRotate 3 : Fin 3 → Fin 3) ∘ finRotate 3 ∘ finRotate 3 = id := by
    funext i
    fin_cases i <;> rfl
  rw [Function.comp_assoc, he, Finsupp.mapDomain_id]

def orbit (d : Exponent) : Finset Exponent := {d, rotation d, rotation (rotation d)}

theorem mem_orbit_self (d : Exponent) : d ∈ orbit d := by simp [orbit]

theorem orbit_rotation (d : Exponent) : orbit (rotation d) = orbit d := by
  ext e
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton, rotation_cube]
  tauto

def Orbit := {s : Finset Exponent // ∃ d, orbit d = s}

def projection (d : Exponent) : Orbit := ⟨orbit d, d, rfl⟩

theorem projection_surjective : Function.Surjective projection := by
  rintro ⟨s, d, hd⟩
  exact ⟨d, Subtype.ext hd⟩

theorem projection_rotation (d : Exponent) : projection (rotation d) = projection d :=
  Subtype.ext (orbit_rotation d)

theorem finite_fibres (s : Orbit) : (projection ⁻¹' {s}).Finite := by
  apply s.val.finite_toSet.subset
  intro d hd
  have he : orbit d = s.val := congrArg Subtype.val hd
  change d ∈ s.val
  rw [← he]
  exact mem_orbit_self d

theorem same_orbit {d e : Exponent} (h : projection d = projection e) :
    d = e ∨ d = rotation e ∨ d = rotation (rotation e) := by
  have he : orbit d = orbit e := congrArg Subtype.val h
  have hm := mem_orbit_self d
  rw [he] at hm
  simpa only [orbit, Finset.mem_insert, Finset.mem_singleton] using hm

variable {R : Type*} [CommRing R]

theorem invariant_iff_coefficients (f : MvPolynomial (Fin 3) R) :
    rename (finRotate 3) f = f ↔
      ∀ d e, projection d = projection e → f.coeff d = f.coeff e := by
  constructor
  · intro hf
    have hc (d : Exponent) : f.coeff (rotation d) = f.coeff d := by
      have he := coeff_rename_mapDomain (finRotate 3) (finRotate 3).injective f d
      rw [hf] at he
      simpa only [rotation_eq] using he
    intro d e he
    rcases same_orbit he with rfl | rfl | rfl
    · rfl
    · exact hc e
    · exact (hc (rotation e)).trans (hc e)
  · intro hf
    apply MvPolynomial.ext
    intro e
    obtain ⟨d, rfl⟩ := rotation.surjective e
    rw [rotation_eq, coeff_rename_mapDomain _ (finRotate 3).injective]
    simpa only [rotation_eq] using (hf (rotation d) d (projection_rotation d)).symm

end Cubic.SurfaceGeometry.CyclicMonomialOrbits
