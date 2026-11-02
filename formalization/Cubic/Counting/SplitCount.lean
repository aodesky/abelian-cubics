import Cubic.Counting.SplitPoints
import CubicTargets.Counting.EllipseLatticeCount

/-!
# Counting split points by the ellipse (`lemma:reducibles`)

"Writing `γ = 1-α-β`, we have `-a = α²+β²+αβ-α-β` and `H(f)² = 1-3a`. Hence the split
points of height at most `H` are the `C₃`-orbits of `E_H° ∩ ℤ²`, and their number is
`⅓ #(E_H° ∩ ℤ²)`."
-/

noncomputable section

namespace Cubic.Counting.SplitCount

open Cubic.OrbitParametrization Cubic.Counting.SplitPoints
open CubicTargets.Counting.EllipseLatticeCount

/-- The triple `(α, β, 1-α-β)`. -/
def ofPair (p : ℤ × ℤ) : Triple :=
  ⟨![p.1, p.2, 1 - p.1 - p.2], by simp⟩

theorem ofPair_val (p : ℤ × ℤ) :
    (ofPair p).val 0 = p.1 ∧ (ofPair p).val 1 = p.2 ∧ (ofPair p).val 2 = 1 - p.1 - p.2 := by
  refine ⟨rfl, rfl, rfl⟩

/-- The paper's identity `-a = α²+β²+αβ-α-β` on the trace-one plane. -/
theorem neg_secondCoeff (α β : ℤ) :
    -secondCoeff α β (1 - α - β) = α ^ 2 + β ^ 2 + α * β - α - β := by
  unfold secondCoeff; ring

/-- The height condition `1-3a ≤ H²` is the ellipse condition. -/
theorem height_iff_ellipse (α β : ℤ) (H : ℝ) :
    1 - 3 * ((secondCoeff α β (1 - α - β) : ℤ) : ℝ) ≤ H ^ 2 ↔
      (α : ℝ) ^ 2 + (β : ℝ) ^ 2 + α * β - α - β ≤ (H ^ 2 - 1) / 3 := by
  have h' := congrArg (Int.cast : ℤ → ℝ) (neg_secondCoeff α β)
  push_cast at h'
  constructor <;> intro hle <;> linarith

/-- Triples of height at most `H`. -/
def boundedTriples (H : ℝ) : Set Triple :=
  {v | 1 - 3 * ((secondCoeff (v.val 0) (v.val 1) (v.val 2) : ℤ) : ℝ) ≤ H ^ 2}

/-- Triples of height at most `H` correspond to lattice points of the closed ellipse. -/
def triplesEquiv (H : ℝ) : latticePoints H ≃ boundedTriples H where
  toFun p := ⟨ofPair p.val, by
    change 1 - 3 * ((secondCoeff (p.val.1) (p.val.2) (1 - p.val.1 - p.val.2) : ℤ) : ℝ) ≤ H ^ 2
    rw [height_iff_ellipse]
    exact p.property⟩
  invFun v := ⟨(v.val.val 0, v.val.val 1), by
    have hv := v.property
    have hsum := v.val.property
    change 1 - 3 * ((secondCoeff (v.val.val 0) (v.val.val 1) (v.val.val 2) : ℤ) : ℝ) ≤ H ^ 2 at hv
    rw [show v.val.val 2 = 1 - v.val.val 0 - v.val.val 1 by omega, height_iff_ellipse] at hv
    exact hv⟩
  left_inv p := rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have hsum := v.val.property
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases hi with rfl | rfl | rfl
    · rfl
    · rfl
    · change 1 - v.val.val 0 - v.val.val 1 = v.val.val 2
      omega

theorem boundedTriples_card (H : ℝ) :
    Nat.card (boundedTriples H) = Nat.card (latticePoints H) :=
  (Nat.card_congr (triplesEquiv H)).symm

/-- The cyclic shift of a triple. -/
def shift (c : ZMod 3) (v : Triple) : Triple :=
  ⟨fun h => v.val (h + c), by
    have hv := v.property
    rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) c with rfl | rfl | rfl
    · simpa using hv
    · simp only [zero_add, show (1 : ZMod 3) + 1 = 2 by decide,
        show (2 : ZMod 3) + 1 = 0 by decide]; omega
    · simp only [zero_add, show (1 : ZMod 3) + 2 = 0 by decide,
        show (2 : ZMod 3) + 2 = 1 by decide]; omega⟩

theorem secondCoeff_shift (c : ZMod 3) (v : Triple) :
    secondCoeff ((shift c v).val 0) ((shift c v).val 1) ((shift c v).val 2) =
      secondCoeff (v.val 0) (v.val 1) (v.val 2) := by
  simp only [shift]
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) c with rfl | rfl | rfl
  · simp
  · simp only [zero_add, show (1 : ZMod 3) + 1 = 2 by decide, show (2 : ZMod 3) + 1 = 0 by decide]
    unfold secondCoeff; ring
  · simp only [zero_add, show (1 : ZMod 3) + 2 = 0 by decide, show (2 : ZMod 3) + 2 = 1 by decide]
    unfold secondCoeff; ring

theorem shift_mem (H : ℝ) (c : ZMod 3) (v : Triple) (hv : v ∈ boundedTriples H) :
    shift c v ∈ boundedTriples H := by
  change 1 - 3 * ((secondCoeff _ _ _ : ℤ) : ℝ) ≤ H ^ 2
  rw [secondCoeff_shift]
  exact hv

theorem shift_injective (v : Triple) : Function.Injective (fun c : ZMod 3 => shift c v) := by
  intro c d hcd
  have hcd' : ∀ h, v.val (h + c) = v.val (h + d) := fun h =>
    congrFun (congrArg Subtype.val hcd) h
  have := shift_free v (c - d) (fun h => by
    have := hcd' (h - d)
    rwa [show h - d + c = h + (c - d) by ring, show h - d + d = h by ring] at this)
  exact sub_eq_zero.mp this

/-- The fibre of a triple's point among bounded triples is its orbit, with three elements. -/
theorem fibre_card (H : ℝ) (v : boundedTriples H) :
    Nat.card {w : boundedTriples H // triplePoint w.val = triplePoint v.val} = 3 := by
  have hset : {w : boundedTriples H | triplePoint w.val = triplePoint v.val} =
      Set.range (fun c : ZMod 3 => (⟨shift c v.val, shift_mem H c v.val v.property⟩ :
        boundedTriples H)) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro hw
      obtain ⟨c, hc⟩ := (triplePoint_eq_iff v.val w.val).mp hw.symm
      exact ⟨c, Subtype.ext (Subtype.ext (funext fun h => (hc h).symm))⟩
    · rintro ⟨c, rfl⟩
      exact ((triplePoint_eq_iff v.val _).mpr ⟨c, fun h => rfl⟩).symm
  change Set.ncard {w : boundedTriples H | triplePoint w.val = triplePoint v.val} = 3
  rw [hset, Set.ncard_range_of_injective (fun c d hcd => shift_injective v.val
    (congrArg Subtype.val hcd))]
  rw [Nat.card_eq_fintype_card, ZMod.card]

end Cubic.Counting.SplitCount
