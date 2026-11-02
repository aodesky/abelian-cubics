import Cubic.BoxAsymptotic.LocalAtThreeData

/-! Direct ramified divisibility for `lem:local3`. Dividing by `λ³` is proved
in coordinates from the norm congruences, without using ideal-count formulas. -/

noncomputable section

namespace Cubic.BoxAsymptotic.LocalNormAtThree

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount Cubic.Counting.TraceZeroLattice
open Cubic.BoxAsymptotic.EisensteinCoordinates Cubic.BoxAsymptotic.ZeroModeMass
open Cubic.BoxAsymptotic.LocalAtThreeData

theorem lambda_cube : lambda ^ 3 = coord (-3, -6) := by
  simp only [lambda, coord]
  push_cast
  linear_combination (4 - zetaInteger) * zetaInteger_sq

theorem coord_ramified (p : ℤ × ℤ) : coord (ramifiedMap p) = lambda ^ 3 * coord p := by
  rw [lambda_cube, ← coord_mulE]
  congr 1
  simp [mulE, ramifiedMap]
  ring

theorem lambda_six : lambda ^ 6 = -27 := by
  rw [show 6 = 3 * 2 by decide, pow_mul, lambda_cube, pow_two, ← coord_mulE]
  norm_num [mulE, coord]

theorem coord_iterate (e : ℕ) (p : ℤ × ℤ) :
    coord (ramifiedMap^[e] p) = lambda ^ (3 * e) * coord p := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', coord_ramified, ih]
    rw [show 3 * (e + 1) = 3 + 3 * e by ring, pow_add]
    ring

theorem norm_ramified (p : ℤ × ℤ) : nrm (ramifiedMap p) = 27 * nrm p := by
  simp only [nrm, ramifiedMap]
  ring

/-- Norm divisible by `27` forces divisibility by `λ³`. -/
theorem norm_preimage (m : ℕ) {p : ℤ × ℤ}
    (hp : p ∈ normSet ((3 * (m : ℤ)) ^ 3)) :
    ∃ q ∈ normSet ((m : ℤ) ^ 3), ramifiedMap q = p := by
  have h9 : (9 : ℤ) ∣ p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 := by
    refine ⟨3 * (m : ℤ) ^ 3, ?_⟩
    rw [hp]
    ring
  obtain ⟨hA, hB⟩ := three_dvd_of_nine_dvd h9
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hn : a ^ 2 - a * b + b ^ 2 = 3 * (m : ℤ) ^ 3 := by
    change p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = _ at hp
    rw [ha, hb] at hp
    nlinarith only [hp]
  have hab : (3 : ℤ) ∣ a + b := by
    apply (dvd_three_iff _).mpr
    have hf : ∀ x y : ZMod 3, x ^ 2 - x * y + y ^ 2 = 0 → x + y = 0 := by decide
    have hcast := congrArg (fun x : ℤ => (x : ZMod 3)) hn
    push_cast at hcast ⊢
    exact hf a b (by simpa only [show (3 : ZMod 3) = 0 by decide, zero_mul] using hcast)
  obtain ⟨c, hc⟩ := hab
  refine ⟨(c - b, 2 * c - b), ?_, ?_⟩
  · change (c - b) ^ 2 - (c - b) * (2 * c - b) + (2 * c - b) ^ 2 = (m : ℤ) ^ 3
    have ha' : a = 3 * c - b := by linarith
    rw [ha'] at hn
    nlinarith only [hn]
  · apply Prod.ext <;> simp only [ramifiedMap] <;> linarith

theorem ramified_norm_image (m : ℕ) :
    ramifiedMap '' normSet ((m : ℤ) ^ 3) = normSet ((3 * (m : ℤ)) ^ 3) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change nrm (ramifiedMap q) = _
    rw [norm_ramified]
    change nrm q = (m : ℤ) ^ 3 at hq
    rw [hq]
    ring
  · exact norm_preimage m

/-- Removing all ramified powers gives the unramified norm set. -/
theorem iterate_norm_image (e M : ℕ) :
    (ramifiedMap^[e]) '' normSet ((M : ℤ) ^ 3) =
      normSet (((3 ^ e * M : ℕ) : ℤ) ^ 3) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ', Function.comp_def, ← Set.image_image, ih, ramified_norm_image]
    congr 1
    push_cast
    ring

/-- The coordinate form of `λ⁶=-27`: two further ramified steps are divisible by `27`. -/
theorem iterate_divisible (e : ℕ) (p : ℤ × ℤ) :
    (27 : ℤ) ∣ (ramifiedMap^[e + 2] p).1 ∧ (27 : ℤ) ∣ (ramifiedMap^[e + 2] p).2 := by
  rw [show e + 2 = 2 + e by omega, Function.iterate_add_apply]
  change (27 : ℤ) ∣ (ramifiedMap (ramifiedMap (ramifiedMap^[e] p))).1 ∧
    (27 : ℤ) ∣ (ramifiedMap (ramifiedMap (ramifiedMap^[e] p))).2
  constructor
  · refine ⟨-(ramifiedMap^[e] p).1, ?_⟩
    simp only [ramifiedMap]
    ring
  · refine ⟨-(ramifiedMap^[e] p).2, ?_⟩
    simp only [ramifiedMap]
    ring

end Cubic.BoxAsymptotic.LocalNormAtThree
