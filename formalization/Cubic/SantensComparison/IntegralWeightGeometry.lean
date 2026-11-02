import Cubic.SurfaceGeometry.AffineModelIntegrality
import Cubic.QuadraticCorrespondence.RegularFunctionTopology
import Cubic.PoissonSummation.IntegralPointComparison
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Maps.Proper.Basic

/-! The finite-place weight on the original affine integral model. Its
support is compact and open in the actual rational point space defined by
the coordinate ring. Proper pullback preserves these properties. The toric
properness certificate itself is kept separate from this topological step. -/

noncomputable section

namespace Cubic.SantensComparison.IntegralWeightGeometry

open Cubic.SurfaceGeometry AffineModelData
open Cubic.QuadraticCorrespondence RegularFunctionTopology
open scoped RegularFunctionTopology

section Coordinates

variable (K : Type*) [CommRing K] [Algebra ℤ K]

abbrev Points := CoordinateRing ℤ →ₐ[ℤ] K
abbrev Coordinates := {x : Fin 3 → K | CubicData.affineRelation (x 0) (x 1) (x 2)=0}

def pointOfCoordinates (x : Coordinates K) : Points K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x.val) (by
    change Ideal.span {equation ℤ} ≤ RingHom.ker (MvPolynomial.aeval x.val).toRingHom
    rw [Ideal.span_le]
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    change MvPolynomial.aeval x.val (equation ℤ)=0
    simpa only [equation, CubicData.affineRelation, map_add, map_sub, map_mul,
      map_pow, map_ofNat, MvPolynomial.aeval_X] using x.property)

@[simp] theorem pointOfCoordinates_coordinate (x : Coordinates K) (i : Fin 3) :
    pointOfCoordinates K x (coordinate ℤ i) = x.val i := by
  simp [pointOfCoordinates, coordinate]

def pointCoordinatesEquiv : Points K ≃ Coordinates K where
  toFun P := ⟨fun i => P (coordinate ℤ i), AffineModelIntegrality.equation_at P.toRingHom⟩
  invFun := pointOfCoordinates K
  left_inv P := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change pointOfCoordinates K _ (coordinate ℤ i)=P (coordinate ℤ i)
    exact pointOfCoordinates_coordinate K _ i
  right_inv x := by ext i; simp

variable [TopologicalSpace K] [IsTopologicalRing K]

def pointCoordinatesHomeomorph : Points K ≃ₜ Coordinates K where
  toEquiv := pointCoordinatesEquiv K
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_eval (coordinate ℤ i)
  continuous_invFun := by
    apply (RegularFunctionTopology.continuous_iff _).mpr
    intro f
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective f
    change Continuous (fun x : Coordinates K => MvPolynomial.aeval x.val p)
    induction p using MvPolynomial.induction_on with
    | C c => simpa using (continuous_const : Continuous (fun _ : Coordinates K => (c:K)))
    | add p q hp hq => simpa only [map_add] using hp.add hq
    | mul_X p i hp =>
      simpa only [map_mul, MvPolynomial.aeval_X] using
        hp.mul ((continuous_apply i).comp continuous_subtype_val)

end Coordinates

section Padic

variable (p : ℕ) [Fact p.Prime]

def integralLocus : Set (Points ℚ_[p]) := {P | ∀ f, ‖P f‖ ≤ 1}

theorem integral_iff_coordinates (P : Points ℚ_[p]) :
    P ∈ integralLocus p ↔ ∀ i, ‖P (coordinate ℤ i)‖ ≤ 1 := by
  refine ⟨fun h i => h _,fun h => ?_⟩
  exact AffineModelIntegrality.functions_mem P.toRingHom (PadicInt.subring p) h

theorem integral_iff_coefficients (P : Points ℚ_[p]) :
    P ∈ integralLocus p ↔ ‖P (coordinate ℤ 0)‖ ≤ 1 ∧ ‖P (coordinate ℤ 1)‖ ≤ 1 :=
  AffineModelIntegrality.local_integrality p P.toRingHom

theorem compact_integral_locus : IsCompact (integralLocus p) := by
  let S : Set (Coordinates ℚ_[p]) := {x | ∀ i, ‖x.val i‖ ≤ 1}
  have hz : IsClosed {x : Fin 3 → ℚ_[p] |
      CubicData.affineRelation (x 0) (x 1) (x 2)=0} := by
    apply isClosed_eq _ continuous_const
    unfold CubicData.affineRelation
    fun_prop
  have hb : IsCompact {x : Fin 3 → ℚ_[p] | ∀ i, ‖x i‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right, Set.mem_setOf_eq,
      pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)] using
        (isCompact_closedBall (0 : Fin 3 → ℚ_[p]) 1)
  have hS : IsCompact S := by
    rw [Subtype.isCompact_iff]
    convert hb.inter_right hz using 1
    ext x
    simp only [S, Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy,y.property⟩
    · rintro ⟨hy,hz⟩
      exact ⟨⟨x,hz⟩,hy,rfl⟩
  have he : integralLocus p = (pointCoordinatesHomeomorph ℚ_[p]) ⁻¹' S := by
    ext P
    exact integral_iff_coordinates p P
  rw [he]
  exact (pointCoordinatesHomeomorph ℚ_[p]).isClosedEmbedding.isCompact_preimage hS

theorem open_integral_locus : IsOpen (integralLocus p) := by
  have hball : IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero
  have he : integralLocus p = ⋂ i : Fin 3,
      (fun P : Points ℚ_[p] => P (coordinate ℤ i)) ⁻¹' {x | ‖x‖ ≤ 1} := by
    ext P
    simpa only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq] using
      integral_iff_coordinates p P
  rw [he]
  exact isOpen_iInter_of_finite (fun i => hball.preimage (continuous_eval _))

theorem proper_pullback {Y : Type*} [TopologicalSpace Y]
    (π : Y → Points ℚ_[p]) (hπ : IsProperMap π) :
    IsCompact (π ⁻¹' integralLocus p) ∧ IsOpen (π ⁻¹' integralLocus p) :=
  ⟨hπ.isCompact_preimage (compact_integral_locus p),
    (open_integral_locus p).preimage hπ.continuous⟩

end Padic

/-- The product weight detects exactly the original all-functions integral
condition on rational torus points. -/
theorem rational_weight (P : Cubic.PoissonSummation.AdelicHeightZetaData.RationalPoints) :
    Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P ↔
      Cubic.PoissonSummation.RationalAdelicEmbedding.diagonal P ∈
        Cubic.PoissonSummation.AdelicHeightZetaData.integralLocus :=
  Cubic.PoissonSummation.IntegralPointComparison.integralPoint_iff P

end Cubic.SantensComparison.IntegralWeightGeometry
