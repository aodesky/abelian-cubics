import Cubic.BoxAsymptotic.LocalAtThreeData
import Cubic.BoxAsymptotic.AngularLocal

/-! The trace residues in `lem:local3`. For a primary element the calculation
follows the paper: write `α=1+3x`, prove `3 ∣ Tr(x)` and `3 ∣ N(x)`, and obtain
`Tr(α) ≡ 3M-1 (mod 27)`. The sign and ramified cases then use the original
congruences and the previously proved trace-class invariance. -/

noncomputable section

namespace Cubic.BoxAsymptotic.LocalTraceAtThree

open CubicTargets.BoxAsymptotic
open Cubic.Counting.EisensteinNormCount
open Cubic.BoxAsymptotic.AngularLocalData Cubic.BoxAsymptotic.AngularLocal
open Cubic.BoxAsymptotic.LocalAtThreeData Cubic.BoxAsymptotic.ZeroModeMass

theorem exists_trace_iff (n : ℕ) (β : ℤ × ℤ) :
    (∃ s : ℤ, AdmissiblePair n β s) ↔ β ∈ admissible n := by
  constructor
  · rintro ⟨s, hN, hB, h2, h27⟩
    exact ⟨hN, hB, s, h2, h27⟩
  · rintro ⟨hN, hB, s, h2, h27⟩
    exact ⟨s, hN, hB, h2, h27⟩

theorem trace_class {n : ℕ} {β : ℤ × ℤ} {s₀ : ℤ}
    (h₀ : AdmissiblePair n β s₀) (s : ℤ) :
    AdmissiblePair n β s ↔ s ≡ s₀ [ZMOD 3] := by
  have h := TraceClass.cong_iff h₀.2.2.1 h₀.2.2.2 (s := s)
  exact ⟨fun hs => h.mp hs.2.2, fun hs => ⟨h₀.1, h₀.2.1, h.mpr hs⟩⟩

theorem pair_neg {n : ℕ} {β : ℤ × ℤ} {s : ℤ} (h : AdmissiblePair n β s) :
    AdmissiblePair n (-β) (-s) := by
  refine ⟨neg_norm_mem h.1, by simpa using h.2.1.neg_right, by simpa using h.2.2.1, ?_⟩
  change 2 * (-β.1) - (-β.2) ≡ 3 * (-s) * n - (-s) ^ 3 [ZMOD 27]
  convert h.2.2.2.neg using 1 <;> ring

/-- The primary generator has trace residue `+1`, with its sign fixed modulo three. -/
theorem primary_pair {M : ℕ} {p : ℤ × ℤ} (hp : p ∈ primary M) :
    AdmissiblePair M p 1 := by
  obtain ⟨a, ha⟩ := hp.2.1.dvd.neg_right
  obtain ⟨b, hb⟩ := hp.2.2
  have ha' : p.1 = 1 + 3 * a := by linarith
  let t : ℤ := 2 * a - b
  let m : ℤ := a ^ 2 - a * b + b ^ 2
  have hn : (M : ℤ) ^ 3 = 1 + 3 * t + 9 * m := by
    have hN := hp.1
    change p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = _ at hN
    rw [ha', hb] at hN
    dsimp [t, m]
    linear_combination -hN
  have hM : (M : ℤ) ≡ 1 [ZMOD 3] := by
    have hf : ∀ x : ZMod 3, x ^ 3 = 1 → x = 1 := by decide
    have hc := congrArg (fun x : ℤ => (x : ZMod 3)) hn
    push_cast at hc
    have hm : (M : ZMod 3) = 1 := hf M (by
      simpa only [show (3 : ZMod 3) = 0 by decide, show (9 : ZMod 3) = 0 by decide,
        zero_mul, add_zero] using hc)
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using hm)
  obtain ⟨d, hd⟩ := hM.dvd.neg_right
  have hM' : (M : ℤ) = 1 + 3 * d := by linarith
  have ht : (3 : ℤ) ∣ t := by
    refine ⟨d + 3 * d ^ 2 + 3 * d ^ 3 - m, ?_⟩
    rw [hM'] at hn
    nlinarith only [hn]
  obtain ⟨c, hc⟩ := ht
  have hnorm : t ^ 2 - m = 3 * a * (a - b) := by dsimp [t, m]; ring
  have hm : (3 : ℤ) ∣ m := by
    refine ⟨3 * c ^ 2 - a * (a - b), ?_⟩
    rw [hc] at hnorm
    nlinarith only [hnorm]
  obtain ⟨f, hf⟩ := hm
  have hJ : 2 * p.1 - p.2 = 2 + 3 * t := by rw [ha', hb]; dsimp [t]; ring
  refine ⟨hp.1, hp.2.2, by simpa using hM.symm, ?_⟩
  apply Int.modEq_iff_dvd.mpr
  refine ⟨f - d ^ 2 - d ^ 3, ?_⟩
  rw [hJ, hM']
  rw [hM', hf] at hn
  nlinarith only [hn]

theorem primary_trace_iff {M : ℕ} {p : ℤ × ℤ} (hp : p ∈ primary M) (s : ℤ) :
    AdmissiblePair M p s ↔ s ≡ 1 [ZMOD 3] := trace_class (primary_pair hp) s

theorem negative_primary_trace_iff {M : ℕ} {p : ℤ × ℤ} (hp : p ∈ primary M) (s : ℤ) :
    AdmissiblePair M (-p) s ↔ s ≡ -1 [ZMOD 3] :=
  trace_class (pair_neg (primary_pair hp)) s

/-- At a ramified norm, existence of an admissible trace forces the zero class. -/
theorem pair_three_iff (m : ℕ) (p : ℤ × ℤ) (s : ℤ) :
    AdmissiblePair (3 * m) p s ↔ p ∈ admissible (3 * m) ∧ s ≡ 0 [ZMOD 3] := by
  constructor
  · intro h
    refine ⟨(exists_trace_iff _ _).mp ⟨s, h⟩, ?_⟩
    have hs : (3 : ℤ) ∣ s := by
      apply Int.prime_three.dvd_of_dvd_pow (n := 2)
      have hd := h.2.2.1.dvd
      push_cast at hd
      omega
    exact Int.modEq_iff_dvd.mpr (by simpa using hs.neg_right)
  · rintro ⟨hp, hs⟩
    obtain ⟨hN, hB, hJ⟩ := (admissible_three m p).mp hp
    have hzero : AdmissiblePair (3 * m) p 0 := by
      refine ⟨by simpa using hN, hB, ?_, ?_⟩
      · exact Int.modEq_iff_dvd.mpr ⟨m, by simp⟩
      · exact Int.modEq_iff_dvd.mpr (by simpa using hJ.neg_right)
    exact (trace_class hzero s).mpr hs

end Cubic.BoxAsymptotic.LocalTraceAtThree
