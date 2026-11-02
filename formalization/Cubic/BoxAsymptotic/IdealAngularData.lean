import Cubic.BoxAsymptotic.AngularIdeals
import Cubic.BoxAsymptotic.BinaryRayEnergy

/-! Generator phases for all integral ideals. Away from three we use the
canonical primary generator; at three we choose any generator. Its phase is
independent of that choice for frequencies divisible by six. This supplies
the same lattice model for the ramified and unramified characters. -/

noncomputable section

namespace Cubic.BoxAsymptotic.IdealAngularData

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularIdealData
open Cubic.BoxAsymptotic.AngularIdeals Cubic.BoxAsymptotic.EisensteinCoordinates
open Cubic.BoxAsymptotic.LatticeSums Cubic.BoxAsymptotic.BinaryRayEnergy
open CubicTargets.BoxAsymptotic

def chosenGenerator (I : Ideal Integers) : Integers :=
  if 3 ∣ Ideal.absNorm I then gen I else PrimaryGenerator.generator I

def point (I : Ideal Integers) : ℤ × ℤ := coordinates (chosenGenerator I)

theorem span_chosen (I : Ideal Integers) : Ideal.span {chosenGenerator I} = I := by
  unfold chosenGenerator
  split_ifs with h
  · exact span_gen I
  · exact (PrimaryGenerator.generator_spec I h).1

@[simp] theorem span_point (I : Ideal Integers) : spanCoord (point I) = I := by
  simp only [spanCoord, point, coord_coordinates, span_chosen]

theorem point_injective : Function.Injective point := by
  intro I J h
  simpa using congrArg spanCoord h

theorem norm_span (p : ℤ × ℤ) : Ideal.absNorm (spanCoord p) = normIndex p := by
  rw [spanCoord, Ideal.absNorm_span_singleton, norm_coord]
  exact_mod_cast (Int.natAbs_of_nonneg (nrm_nonneg p)).trans
    (Int.toNat_of_nonneg (nrm_nonneg p)).symm

@[simp] theorem norm_point (I : Ideal Integers) : normIndex (point I) = Ideal.absNorm I := by
  rw [← norm_span, span_point]

theorem cast_normIndex (p : ℤ × ℤ) : (normIndex p : ℝ) = nrm p := by
  rw [normIndex, ← Int.cast_natCast, Int.toNat_of_nonneg (nrm_nonneg p)]

@[simp] theorem real_norm_point (I : Ideal Integers) :
    (nrm (point I) : ℝ) = Ideal.absNorm I := by
  rw [← cast_normIndex, norm_point]

theorem point_ne_zero {I : Ideal Integers} (hI : I ≠ ⊥) : point I ≠ 0 := by
  intro hp
  apply hI
  rw [← span_point I, hp]
  simp [spanCoord, coord]

theorem span_ne_bot {p : ℤ × ℤ} (hp : p ≠ 0) : spanCoord p ≠ ⊥ := by
  intro h
  have hc := Ideal.span_singleton_eq_bot.mp h
  have hz : coord (0 : ℤ × ℤ) = 0 := by simp [coord]
  exact hp (coord_injective (hc.trans hz.symm))

/-- Nonzero integral ideals of norm at most `Y`, represented independently as
the image of the finite lattice ball. -/
def idealBall (Y : ℝ) : Finset (Ideal Integers) := by
  classical
  exact (ball Y).image spanCoord

theorem mem_idealBall {Y : ℝ} {I : Ideal Integers} :
    I ∈ idealBall Y ↔ I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hp0, hpY⟩ := mem_ball.mp hp
    refine ⟨span_ne_bot hp0, ?_⟩
    simpa only [norm_span, cast_normIndex] using hpY
  · rintro ⟨hI, hY⟩
    exact Finset.mem_image.mpr ⟨point I,
      mem_ball.mpr ⟨point_ne_zero hI, by simpa only [real_norm_point] using hY⟩,
      span_point I⟩

/-- Angular value of a chosen generator, extended by zero at the zero ideal. -/
def generatorPhase (k : ℤ) (I : Ideal Integers) : ℂ := by
  classical
  exact if I = ⊥ then 0 else phase k (eis (point I))

theorem generatorPhase_eq (k : ℤ) {I : Ideal Integers} (hI : I ≠ ⊥) :
    generatorPhase k I = phase k (eis (point I)) := by simp [generatorPhase, hI]

theorem generatorPhase_away (k : ℤ) {I : Ideal Integers}
    (hI : ¬ 3 ∣ Ideal.absNorm I) : generatorPhase k I = psi k I := by
  have h0 : I ≠ ⊥ := by intro h; simp [h] at hI
  simp [generatorPhase, h0, psi, chosenGenerator, point, hI]

/-- The character inducing `ψ_k`: for frequencies divisible by six include
the prime above three; otherwise continue to omit it. Analytic use of this
definition requires the separate character/conductor verification. -/
def primitivePsi (k : ℤ) (I : Ideal Integers) : ℂ :=
  if 6 ∣ k then generatorPhase k I else psi k I

end Cubic.BoxAsymptotic.IdealAngularData
