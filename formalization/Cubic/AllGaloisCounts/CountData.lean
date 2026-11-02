import Cubic.Counting.GeneralMonicCount
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The actual counts and constants in the all-Galois appendix

Galois types refer to the automorphism group of the actual splitting field of
the polynomial over `ℚ`. No separability condition is imposed on the height box:
in particular the trivial-group count includes repeated-root cubics.
The polynomial `P` uses the coefficients already proved in `thm:generalMonicCount`.
-/

noncomputable section

namespace Cubic.AllGaloisCounts.CountData

open Polynomial MeasureTheory
open Cubic.Counting.GeneralMonicData

inductive GaloisType
  | trivial | quadratic | cyclic | symmetric
  deriving DecidableEq

/-- The four isomorphism types, using the actual polynomial Galois group. -/
def HasGaloisType (G : GaloisType) (f : ℚ[X]) : Prop :=
  match G with
  | .trivial => Nonempty (f.Gal ≃* Multiplicative (ZMod 1))
  | .quadratic => Nonempty (f.Gal ≃* Multiplicative (ZMod 2))
  | .cyclic => Nonempty (f.Gal ≃* Multiplicative (ZMod 3))
  | .symmetric => Nonempty (f.Gal ≃* Equiv.Perm (Fin 3))

/-- All monic integral cubics in the weighted coefficient-height box. -/
def cubicBox (H : ℝ) : Set ℤ[X] :=
  {f | (∃ a₂ a₁ a₀ : ℤ, f = monicCubic a₂ a₁ a₀) ∧ weightedHeight f ≤ H}

def galoisSet (G : GaloisType) (H : ℝ) : Set ℤ[X] :=
  {f | f ∈ cubicBox H ∧ HasGaloisType G (f.map (Int.castRingHom ℚ))}

/-- `N_G(H)`; finiteness is a separate assertion, not part of this definition. -/
def N (G : GaloisType) (H : ℝ) : ℕ := Nat.card (galoisSet G H)

/-- A marked integral root is counted once, irrespective of its multiplicity. -/
def markedSet (H : ℝ) : Set (ℤ[X] × ℤ) :=
  {fr | fr.1 ∈ cubicBox H ∧ fr.1.eval fr.2 = 0}

def markedCount (H : ℝ) : ℕ := Nat.card (markedSet H)

/-- Existence of the root used to define the appendix's constant. -/
theorem exists_vartheta : ∃ x : ℝ, 1 < x ∧ x < 2 ∧ x ^ 3 = x ^ 2 + x + 1 := by
  have hc : Continuous (fun x : ℝ => (x ^ 3 - x ^ 2 - x - 1 : ℝ)) := by fun_prop
  have h := intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ 3 - 1 ^ 2 - 1 - 1)
      ((2 : ℝ) ^ 3 - 2 ^ 2 - 2 - 1) by norm_num)
  obtain ⟨x, hx, he⟩ := h
  refine ⟨x, lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_, by linarith⟩
  · intro heq
    rw [← heq] at he
    norm_num at he
  · intro heq
    rw [heq] at he
    norm_num at he

def vartheta : ℝ := Classical.choose exists_vartheta

theorem vartheta_spec : 1 < vartheta ∧ vartheta < 2 ∧
    vartheta ^ 3 = vartheta ^ 2 + vartheta + 1 :=
  Classical.choose_spec exists_vartheta

theorem vartheta_unique {x : ℝ} (hx : 1 < x) (he : x ^ 3 = x ^ 2 + x + 1) :
    x = vartheta := by
  have hy := vartheta_spec.1
  have hxy : 0 < x * vartheta - 1 := by
    nlinarith [mul_pos (by linarith : 0 < x - 1) (by linarith : 0 < vartheta - 1)]
  have hp : 0 < x ^ 2 + x * vartheta + vartheta ^ 2 - x - vartheta - 1 := by
    nlinarith [mul_pos (by linarith : 0 < x) (by linarith : 0 < x - 1),
      mul_pos (by linarith : 0 < vartheta) (by linarith : 0 < vartheta - 1)]
  have hm : (x - vartheta) *
      (x ^ 2 + x * vartheta + vartheta ^ 2 - x - vartheta - 1) = 0 := by
    nlinarith [vartheta_spec.2.2]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hp.ne')

def splitLeading : ℝ := 20 * Real.pi * Real.sqrt 3 / 81
def markedVolume : ℝ := 6 + vartheta - 11 / (3 * vartheta) + 4 * Real.log vartheta
def markedBoundary : ℝ := 1 + vartheta + 2 / (3 * vartheta) + 2 * Real.log vartheta

/-- The same polynomial as in the completed general monic count. -/
def P (t : ℝ) : ℝ :=
  Cubic.Counting.GeneralMonicCount.Cmon * t + Cubic.Counting.GeneralMonicCount.Dmon

/-- `ℛ(H)`, including the fractional-part boundary term for real heights. -/
def R (H : ℝ) : ℝ :=
  markedVolume * H ^ 4 + (1 - 2 * Int.fract H) * markedBoundary * H ^ 3

/-- The displayed coefficient-box formula; its equality to the count is proved separately. -/
def boxFormula (H : ℝ) : ℝ := ∏ j ∈ Finset.Icc 1 3, (2 * (⌊H ^ j⌋ : ℝ) + 1)

/-- The actual length of the intersection, with the prescribed value at `x = 0`. -/
def F (x y : ℝ) : ℝ :=
  if x = 0 then 2 else volume.real
    (Set.Icc (x ^ 2 + x * y - 1) (x ^ 2 + x * y + 1) ∩
      Set.Icc (-|x|⁻¹) |x|⁻¹)

def g (y : ℝ) : ℝ := ∫ x : ℝ, F x y

end Cubic.AllGaloisCounts.CountData
