import Cubic.ToricHeights.IntegralCartierParameters
import Cubic.ToricHeights.SupportFunction

/-!
# The Cartier support data recover the height's original support function

Each maximal cone is specified as a region in the real cocharacter plane.
An original integral character with the prescribed ray values evaluates to
the support function of `SupportFunction` everywhere on that cone. Thus the Cartier and strict-convexity computations concern the
same support function used in all local height and Fourier constructions.
-/

namespace Cubic.ToricHeights.CartierSupportFunction

open Cubic.QuadraticCorrespondence DivisorParameters IntegralCartierParameters

/-- The cone opposite a boundary ray, in the original real ray coordinates. -/
def InCone (omitted : Fin 3) (n : ℝ × ℝ) : Prop :=
  if omitted = 0 then 0 ≤ n.1 ∧ 0 ≤ n.2
  else if omitted = 1 then n.1 ≤ 0 ∧ n.1 ≤ n.2
  else n.2 ≤ 0 ∧ n.2 ≤ n.1

theorem cones_cover (n : ℝ × ℝ) : ∃ omitted : Fin 3, InCone omitted n := by
  by_cases h1 : 0 ≤ n.1
  · by_cases h2 : 0 ≤ n.2
    · exact ⟨0, by simpa [InCone] using And.intro h1 h2⟩
    · exact ⟨2, by simp [InCone]; exact ⟨le_of_not_ge h2, (le_of_not_ge h2).trans h1⟩⟩
  · by_cases h12 : n.1 ≤ n.2
    · exact ⟨1, by simp [InCone]; exact ⟨le_of_not_ge h1, h12⟩⟩
    · exact ⟨2, by simp [InCone]; exact ⟨(le_of_not_ge h12).trans (le_of_not_ge h1), le_of_not_ge h12⟩⟩

def characterLinear (m : ℤ × ℤ) (n : ℝ × ℝ) : ℂ :=
  ((CharacterLattice.pullback m).1 : ℂ) * (n.1 : ℂ) +
    ((CharacterLattice.pullback m).2 : ℂ) * (n.2 : ℂ)

theorem characterLinear_eq (m : ℤ × ℤ) (n : ℝ × ℝ) :
    characterLinear m n = (2 * (m.1 : ℂ) - m.2) * (n.1 : ℂ) +
      (-(m.1 : ℂ) + 2 * m.2) * (n.2 : ℂ) := by
  simp [characterLinear, CharacterLattice.pullback]

theorem supportFunction_eq_character (d : ℤ × ℤ) (omitted : Fin 3)
    (m : ℤ × ℤ)
    (hm : ∀ i : Fin 3, i ≠ omitted →
      boundaryOrders m i = -(coefficients ℤ d i : ℚ))
    (n : ℝ × ℝ) (hn : InCone omitted n) :
    supportFunction (d.1 : ℂ) (d.2 : ℂ) n = characterLinear m n := by
  fin_cases omitted
  · have h1 := hm 1 (by decide)
    have h2 := hm 2 (by decide)
    rw [orders_one] at h1
    rw [orders_two] at h2
    simp [coefficients] at h1 h2
    have h1' : 2 * (m.1 : ℂ) - m.2 = -d.2 := by exact_mod_cast h1
    have h2' : -(m.1 : ℂ) + 2 * m.2 = -d.2 := by exact_mod_cast h2
    have hn' : 0 ≤ n.1 ∧ 0 ≤ n.2 := by simpa [InCone] using hn
    rw [supportFunction_on_integralCone _ _ hn'.1 hn'.2]
    rw [characterLinear_eq, h1', h2']
    ring
  · have h0 := hm 0 (by decide)
    have h2 := hm 2 (by decide)
    rw [orders_zero] at h0
    rw [orders_two] at h2
    simp [coefficients] at h0 h2
    have h1 : 2 * (m.1 : ℚ) - m.2 = (d.1 : ℚ) + d.2 := by linarith
    have h1' : 2 * (m.1 : ℂ) - m.2 = (d.1 : ℂ) + d.2 := by exact_mod_cast h1
    have h2' : -(m.1 : ℂ) + 2 * m.2 = -d.2 := by exact_mod_cast h2
    have hn' : n.1 ≤ 0 ∧ n.1 ≤ n.2 := by simpa [InCone] using hn
    rw [supportFunction_on_cone02 _ _ hn'.1 hn'.2]
    rw [characterLinear_eq, h1', h2']
    ring
  · have h0 := hm 0 (by decide)
    have h1 := hm 1 (by decide)
    rw [orders_zero] at h0
    rw [orders_one] at h1
    simp [coefficients] at h0 h1
    have h2 : -(m.1 : ℚ) + 2 * m.2 = (d.1 : ℚ) + d.2 := by linarith
    have h1' : 2 * (m.1 : ℂ) - m.2 = -d.2 := by exact_mod_cast h1
    have h2' : -(m.1 : ℂ) + 2 * m.2 = (d.1 : ℂ) + d.2 := by exact_mod_cast h2
    have hn' : n.2 ≤ 0 ∧ n.2 ≤ n.1 := by simpa [InCone] using hn
    rw [supportFunction_on_cone01 _ _ hn'.1 hn'.2]
    rw [characterLinear_eq, h1', h2']
    ring

theorem compatible_on_overlap (d : ℤ × ℤ) (i j : Fin 3) (m l : ℤ × ℤ)
    (hm : ∀ r : Fin 3, r ≠ i → boundaryOrders m r = -(coefficients ℤ d r : ℚ))
    (hl : ∀ r : Fin 3, r ≠ j → boundaryOrders l r = -(coefficients ℤ d r : ℚ))
    (n : ℝ × ℝ) (hi : InCone i n) (hj : InCone j n) :
    characterLinear m n = characterLinear l n :=
  (supportFunction_eq_character d i m hm n hi).symm.trans
    (supportFunction_eq_character d j l hl n hj)

/-- The original Galois action swaps both the character and ray coordinates. -/
theorem characterLinear_conjugate (m : ℤ × ℤ) (n : ℝ × ℝ) :
    characterLinear m.swap n.swap = characterLinear m n := by
  simp [characterLinear, CharacterLattice.pullback_swap, add_comm]

/-- The nontrivial Galois element exchanges the two nonfixed rays and cones. -/
def conjugateCone (i : Fin 3) : Fin 3 := if i = 0 then 0 else if i = 1 then 2 else 1

theorem inCone_conjugate (i : Fin 3) (n : ℝ × ℝ) :
    InCone (conjugateCone i) n.swap ↔ InCone i n := by
  fin_cases i <;> simp [conjugateCone, InCone, and_comm]

/-- Local support characters on conjugate cones agree under the original Galois action. -/
theorem galois_compatible (d : ℤ × ℤ) (i : Fin 3) (m l : ℤ × ℤ)
    (hm : ∀ r : Fin 3, r ≠ i → boundaryOrders m r = -(coefficients ℤ d r : ℚ))
    (hl : ∀ r : Fin 3, r ≠ conjugateCone i →
      boundaryOrders l r = -(coefficients ℤ d r : ℚ))
    (n : ℝ × ℝ) (hn : InCone i n) :
    characterLinear l n.swap = characterLinear m n := by
  rw [← supportFunction_eq_character d (conjugateCone i) l hl n.swap
    ((inCone_conjugate i n).mpr hn), supportFunction_swap]
  exact supportFunction_eq_character d i m hm n hn

end Cubic.ToricHeights.CartierSupportFunction
