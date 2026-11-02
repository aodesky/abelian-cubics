import Cubic.BoxAsymptotic.LatticeSums
import Cubic.BoxAsymptotic.AngularSeriesData

/-! Canonical decomposition of a nonzero Eisenstein lattice vector as a
positive integer times a primitive vector. These are the rays in the angular
large-sieve argument; no quotient by units is used in these definitions. -/

noncomputable section

namespace Cubic.BoxAsymptotic.PrimitiveRays

open CubicTargets.BoxAsymptotic
open Cubic.BoxAsymptotic.EisensteinCoordinates Cubic.BoxAsymptotic.AngularSpacing
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.LatticeSums

def content (p : ℤ × ℤ) : ℕ := Int.gcd p.1 p.2

def primitivePart (p : ℤ × ℤ) : ℤ × ℤ := (p.1 / content p, p.2 / content p)

theorem content_pos {p : ℤ × ℤ} (hp : p ≠ 0) : 0 < content p := by
  rw [content, Int.gcd_pos_iff]
  by_contra h
  push_neg at h
  exact hp (Prod.ext h.1 h.2)

theorem decompose (p : ℤ × ℤ) : p = (content p : ℤ) • primitivePart p := by
  ext
  · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left p.1 p.2)).symm
  · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right p.1 p.2)).symm

theorem primitive {p : ℤ × ℤ} (hp : p ≠ 0) : prim (primitivePart p) :=
  Int.gcd_div_gcd_div_gcd (content_pos hp)

theorem norm_decompose (p : ℤ × ℤ) :
    nrm p = (content p : ℤ) ^ 2 * nrm (primitivePart p) := by
  calc
    nrm p = nrm ((content p : ℤ) • primitivePart p) := congrArg nrm (decompose p)
    _ = _ := nrm_smul _ _

theorem phase_decompose (k : ℤ) {p : ℤ × ℤ} (hp : p ≠ 0) :
    phase k (eis p) = phase k (eis (primitivePart p)) := by
  have hg : 0 < (content p : ℝ) := by exact_mod_cast content_pos hp
  have hv := prim_ne_zero (primitive hp)
  conv_lhs => rw [decompose p, eis_smul]
  rw [phase_mul k (by exact_mod_cast hg.ne') (eis_ne_zero hv)]
  simpa using congrArg (fun z : ℂ => z * phase k (eis (primitivePart p)))
    (phase_ofReal_pos k hg)

theorem primitivePart_mem {Y : ℝ} {p : ℤ × ℤ} (hp : p ∈ ball Y) :
    primitivePart p ∈ ball Y := by
  obtain ⟨hp0, hpY⟩ := mem_ball.mp hp
  have hv0 := prim_ne_zero (primitive hp0)
  have hg : (1 : ℤ) ≤ content p := by exact_mod_cast content_pos hp0
  have hn := nrm_nonneg (primitivePart p)
  have hle : nrm (primitivePart p) ≤ nrm p := by
    rw [norm_decompose p]
    have hgsq : (1 : ℤ) ≤ (content p : ℤ) ^ 2 := by nlinarith
    nlinarith
  exact mem_ball.mpr ⟨hv0, (by exact_mod_cast hle :
    (nrm (primitivePart p) : ℝ) ≤ nrm p).trans hpY⟩

theorem content_le {Y : ℝ} {p : ℤ × ℤ} (hp : p ∈ ball Y) :
    (content p : ℝ) ≤ Y := by
  have hp0 := (mem_ball.mp hp).1
  have hnp := one_le_nrm (prim_ne_zero (primitive hp0))
  have hg : (1 : ℤ) ≤ content p := by exact_mod_cast content_pos hp0
  have hle : (content p : ℤ) ≤ nrm p := by
    rw [norm_decompose]
    nlinarith [sq_nonneg (content p : ℤ)]
  exact (by exact_mod_cast hle : (content p : ℝ) ≤ nrm p).trans (mem_ball.mp hp).2

theorem content_injective_on_ray (v : ℤ × ℤ) :
    Set.InjOn content {p | primitivePart p = v} := by
  intro p hp q hq he
  change primitivePart p = v at hp
  change primitivePart q = v at hq
  calc
    p = (content p : ℤ) • primitivePart p := decompose p
    _ = (content q : ℤ) • primitivePart q := by rw [he, hp, hq]
    _ = q := (decompose q).symm

theorem sqrt_norm_decompose (p : ℤ × ℤ) :
    Real.sqrt (nrm p) = content p * Real.sqrt (nrm (primitivePart p)) := by
  have hg : (0 : ℝ) ≤ content p := Nat.cast_nonneg _
  have he : (nrm p : ℝ) = (content p : ℝ) ^ 2 * (nrm (primitivePart p) : ℝ) := by
    exact_mod_cast norm_decompose p
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hg]

end Cubic.BoxAsymptotic.PrimitiveRays
