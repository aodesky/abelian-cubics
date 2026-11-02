import Cubic.PoissonSummation.AdelicHeightLaws
import Cubic.PoissonSummation.AdelicRationalCharacter

/-!
# The principal-divisor shift of the actual height

The support function changes by the linear form of the norm character when
`(s₀,σ,σ)` is replaced by `(s₀+2a,σ-a,σ-a)`. At each place the resulting
exponential uses the original residue-weighted logarithm. The rational product
formula then cancels their sum. These identities hold before imposing the
integral cutoff, as required by the proof of `thm:heightZetaFunctionFormula2`.
-/

noncomputable section

namespace Cubic.PoissonSummation.HeightParameterShift

open Cubic.ToricHeights Cubic.QuadraticCorrespondence
open LocalLogarithmNormalization QuotientFiniteHeight QuotientFiniteFourierProduct QuotientLocalFourier
open AdelicHeightZetaData
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

/-- A single positive-base factor, with the logarithmic weight retained. -/
theorem cpow_shift (q : ℝ) (hq : 0 < q) (s₀ σ a : ℂ) (n : ℝ × ℝ) :
    (q : ℂ) ^ supportFunction (s₀ + 2 * a) (σ - a) n =
      (q : ℂ) ^ supportFunction s₀ σ n *
        Complex.exp (a * (((normalizedLog q n).1 : ℂ) + (normalizedLog q n).2)) := by
  rw [supportFunction_principal_shift, Complex.cpow_add _ _ (by exact_mod_cast hq.ne')]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne'),
    ← Complex.ofReal_log hq.le]
  congr 1
  simp only [normalizedLog, Complex.ofReal_mul]
  ring

/-- The linear norm-character pairing survives the split-place Galois average. -/
private theorem sum_conjugateAverage (n : ℝ × ℝ) :
    ((conjugateAverage n).1 : ℂ) + (conjugateAverage n).2 = (n.1 : ℂ) + n.2 := by
  simp only [conjugateAverage, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

/-- The shift at every original finite place, including the ramified place three. -/
theorem local_shift (p : Nat.Primes) (s₀ σ a : ℂ) :
    ∀ x : (family p).Carrier,
      (family p).inverseHeight (s₀ + 2 * a) (σ - a) x =
        (family p).inverseHeight s₀ σ x * Complex.exp (a *
          (((FiniteAdelicData.localLogarithm p x).1 : ℂ) +
            (FiniteAdelicData.localLogarithm p x).2)) := by
  apply FiniteAdelicData.localLogarithm_induction
    (fun D L => ∀ x : D.Carrier, D.inverseHeight (s₀ + 2 * a) (σ - a) x =
      D.inverseHeight s₀ σ x * Complex.exp (a * (((L x).1 : ℂ) + (L x).2)))
  · intro p x
    letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
    letI : Fact ((p.1 : ℕ) % 3 = 1) := ⟨p.2⟩
    simp only [splitData, splitInverseHeight_eq, splitLogarithm_eq,
      sum_conjugateAverage, SplitLocalModel.inverseHeight]
    exact cpow_shift p.1 (by exact_mod_cast p.1.2.pos) s₀ σ a _
  · intro p x
    letI : Fact (p.1 : ℕ).Prime := ⟨p.1.2⟩
    letI : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩
    simp only [inertData, inertInverseHeight_eq, inertLogarithm_eq,
      InertLocalModel.inverseHeight]
    exact cpow_shift p.1 (by exact_mod_cast p.1.2.pos) s₀ σ a _
  · intro x
    simp only [ramifiedData, ramifiedInverseHeight_eq, ramifiedLogarithm_eq,
      RamifiedLocalModel.inverseHeight]
    exact cpow_shift 3 (by norm_num) s₀ σ a _

/-- The complex place has logarithmic weight one after the global degree cancels. -/
theorem infinite_shift (s₀ σ a : ℂ) (x : ArchimedeanQuotientLogarithm.Points) :
    ArchimedeanQuotientLogarithm.inverseHeight (s₀ + 2 * a) (σ - a) x =
      ArchimedeanQuotientLogarithm.inverseHeight s₀ σ x * Complex.exp (a *
        (((ArchimedeanQuotientLogarithm.logarithm x).1 : ℂ) +
          (ArchimedeanQuotientLogarithm.logarithm x).2)) := by
  simp only [ArchimedeanQuotientLogarithm.inverseHeight_eq,
    ArchimedeanQuotientLogarithm.logarithm_eq, supportFunction_principal_shift,
    Complex.exp_add]

private theorem exp_coordinate_sum {ι : Type*} (S : Finset ι) (a : ℂ) (L : ι → ℝ × ℝ) :
    Complex.exp (a * ((((∑ i ∈ S, L i).1 : ℝ) : ℂ) + (∑ i ∈ S, L i).2)) =
      ∏ i ∈ S, Complex.exp (a * (((L i).1 : ℂ) + (L i).2)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi, Prod.fst_add, Prod.snd_add,
      Complex.ofReal_add]
    rw [show a * (((L i).1 + ((∑ j ∈ S, L j).1 : ℝ) : ℂ) +
        ((L i).2 + ((∑ j ∈ S, L j).2 : ℝ) : ℂ)) =
      a * (((L i).1 : ℂ) + (L i).2) +
        a * ((((∑ j ∈ S, L j).1 : ℝ) : ℂ) + (∑ j ∈ S, L j).2) by ring,
      Complex.exp_add, ih]

/-- Compact triviality makes the finite-place product formula a finite calculation. -/
theorem finite_shift (s₀ σ a : ℂ) (x : FiniteAdelicData.Points) :
    FiniteAdelicData.inverseHeight (s₀ + 2 * a) (σ - a) x =
      FiniteAdelicData.inverseHeight s₀ σ x * Complex.exp (a *
        (((FiniteAdelicData.logarithm x).1 : ℂ) + (FiniteAdelicData.logarithm x).2)) := by
  classical
  have hfin : {p | x p ∉ (family p).maxCompact}.Finite := x.property
  have hS : ∀ p ∉ hfin.toFinset, x p ∈ (family p).maxCompact := by
    intro p hp
    by_contra hn
    exact hp (hfin.mem_toFinset.mpr hn)
  rw [FiniteAdelicData.inverseHeight_eq_prod _ _ x _ hS,
    FiniteAdelicData.inverseHeight_eq_prod _ _ x _ hS,
    FiniteAdelicData.logarithm_eq_sum x _ hS, exp_coordinate_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => local_shift p s₀ σ a (x p)

/-- On arbitrary adeles the shift is exactly the exponential of the norm logarithm. -/
theorem adelic_shift (s₀ σ a : ℂ) (x : AdelicData.Points) :
    AdelicData.inverseHeight (s₀ + 2 * a) (σ - a) x =
      AdelicData.inverseHeight s₀ σ x * Complex.exp (a *
        (((AdelicData.logarithm x).1 : ℂ) + (AdelicData.logarithm x).2)) := by
  rw [AdelicData.inverseHeight, infinite_shift, finite_shift]
  simp only [AdelicData.inverseHeight, AdelicData.logarithm, Prod.fst_add, Prod.snd_add,
    Complex.ofReal_add]
  rw [show a *
      (((ArchimedeanQuotientLogarithm.logarithm x.1).1 + (FiniteAdelicData.logarithm x.2).1 : ℂ) +
       ((ArchimedeanQuotientLogarithm.logarithm x.1).2 + (FiniteAdelicData.logarithm x.2).2 : ℂ)) =
      a * (((ArchimedeanQuotientLogarithm.logarithm x.1).1 : ℂ) +
        (ArchimedeanQuotientLogarithm.logarithm x.1).2) +
      a * (((FiniteAdelicData.logarithm x.2).1 : ℂ) + (FiniteAdelicData.logarithm x.2).2) by ring,
    Complex.exp_add]
  ring

/-- The actual rational product formula removes the shift on every rational point. -/
theorem rational_inverseHeight_shift (s₀ σ a : ℂ) (P : RationalPoints) :
    AdelicData.inverseHeight (s₀ + 2 * a) (σ - a) (RationalAdelicEmbedding.diagonal P) =
      AdelicData.inverseHeight s₀ σ (RationalAdelicEmbedding.diagonal P) := by
  rw [adelic_shift, AdelicRationalCharacter.logarithm_diagonal]
  simp

/-- The equality of positive heights in the paper holds on all rational points. -/
theorem rational_height_shift (s₀ σ a : ℂ) (P : RationalPoints) :
    height (s₀ + 2 * a) (σ - a) (RationalAdelicEmbedding.diagonal P) =
      height s₀ σ (RationalAdelicEmbedding.diagonal P) := by
  apply inv_injective
  simp only [← AdelicHeightLaws.inverseHeight_eq_reciprocal, rational_inverseHeight_shift]

theorem zetaTerm_shift (s₀ σ a : ℂ) (P : IntegralRationalPoints) :
    zetaTerm (s₀ + 2 * a) (σ - a) P = zetaTerm s₀ σ P := by
  simp only [zetaTerm, ← AdelicHeightLaws.inverseHeight_eq_reciprocal,
    rational_inverseHeight_shift]

theorem heightZeta_shift (s₀ σ a : ℂ) :
    heightZeta (s₀ + 2 * a) (σ - a) = heightZeta s₀ σ :=
  tsum_congr fun P => zetaTerm_shift s₀ σ a P

end Cubic.PoissonSummation.HeightParameterShift
