import Wikipedia.HopfProblem.CuspCircleNormalTrivializationToricZeroSection
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRadius
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedAxis
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspRationalCurves

/-!
# The actual normal-product map through the cusp quotient

A single open normal-radius condition puts the entire base sphere in
the unchanged toric time tube. The map below is then the original cusp
quotient followed by its original inclusion in the glued threefold.
Its zero section is exactly the named fixed curve parametrization.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix OnePoint

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts ToricFan SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction

local notation "CD" => CuspGeometry.data

/-- A uniform open product domain lying in the original cusp time tube. -/
def smallNormalProduct : TopologicalSpace.Opens (RiemannSphere × Fibre) :=
  ⟨{p | radiusSq p.2 < 4 * (CD).radius},
    isOpen_lt ((contDiff_radiusSq (n := ω)).continuous.comp continuous_snd) continuous_const⟩

theorem zero_mem_smallNormalProduct (p : RiemannSphere) :
    (p, (0 : Fibre)) ∈ smallNormalProduct := by
  change radiusSq (0 : Fibre) < 4 * (CD).radius
  rw [radiusSq_zero]
  exact mul_pos (by norm_num) (CD).radius_pos

/-- The original zero section, valued in the actual uniform open product domain. -/
def zeroSection (p : RiemannSphere) : smallNormalProduct :=
  ⟨(p, 0), zero_mem_smallNormalProduct p⟩

theorem fromProduct_time_lt (p : smallNormalProduct) :
    ‖ToricSpace.time (fromProduct (p : RiemannSphere × Fibre))‖ < (CD).radius := by
  obtain ⟨b, q, hq⟩ := baseProductChart_cover (p : RiemannSphere × Fibre)
  have hnormal : radiusSq q.2 < 4 * (CD).radius := by
    have hp := p.property
    rw [← hq] at hp
    exact hp
  rw [← hq, fromProduct_baseProductChart]
  exact chartParameters_time_lt b q (CD).radius hnormal

/-- The actual inverse-normal-coordinate point of the unchanged toric tube. -/
def toTube (p : smallNormalProduct) : ToricSpace.Tube (CuspQuotient.disc (CD).radius) :=
  ⟨fromProduct p, by
    change ToricSpace.time (fromProduct p) ∈ Metric.ball 0 (CD).radius
    simpa only [Metric.mem_ball, dist_zero_right] using fromProduct_time_lt p⟩

@[simp] theorem toTube_coe (p : smallNormalProduct) :
    (toTube p : ToricSpace.Space) = fromProduct p := rfl

theorem toTube_continuous : Continuous toTube :=
  (continuous_fromProduct.comp continuous_subtype_val).subtype_mk _

/-- The genuine product map into the original glued threefold. -/
def globalProductMap (p : smallNormalProduct) : Threefold.Space :=
  CuspGeometry.inclusion
    (CuspQuotient.quotientMap (CD).correction (CD).radius (toTube p))

theorem globalProductMap_continuous : Continuous globalProductMap :=
  CuspGeometry.inclusion_continuous.comp
    ((CuspQuotient.quotientMap_continuous (CD).correction (CD).radius).comp toTube_continuous)

/-- The inverse coordinates give a point of the original affine cusp domain. -/
def coordinatePoint (b : Bool) (q : Model) (hq : radiusSq q.2 < 4 * (CD).radius) :
    FixedCoordinates.Domain :=
  ⟨(chartCoordinates b).symm q, by
    change ‖Triangle.time ((chartCoordinates b).symm q)‖ < (CD).radius
    simpa only [ToricSpace.time_inclusion] using
      chartParameters_time_lt b q (CD).radius hq⟩

@[simp] theorem toTube_baseProductChart (b : Bool) (q : Model)
    (hq : radiusSq q.2 < 4 * (CD).radius) :
    toTube ⟨baseProductChart b q, hq⟩ =
      FixedCoordinates.tubeMap (chartTriangle b) (coordinatePoint b q hq) := by
  apply Subtype.ext
  exact fromProduct_baseProductChart b q

/-- The global product map is literally the preexisting native coordinate cover on both charts. -/
@[simp] theorem globalProductMap_baseProductChart (b : Bool) (q : Model)
    (hq : radiusSq q.2 < 4 * (CD).radius) :
    globalProductMap ⟨baseProductChart b q, hq⟩ =
      FixedCoordinates.globalMap (chartTriangle b) (coordinatePoint b q hq) := by
  unfold globalProductMap
  rw [toTube_baseProductChart]
  rfl

@[simp] theorem coordinatePoint_zero (b : Bool) (a : ℂ)
    (h : radiusSq (0 : Fibre) < 4 * (CD).radius) :
    coordinatePoint b (a, 0) h = FixedCoordinates.axis a := by
  apply Subtype.ext
  change (chartCoordinates b).symm (a, 0) = FixedCoordinates.axisLinear a
  rw [chartCoordinates_symm_zero, FixedCoordinates.axisLinear_apply]

/-- The native lower and upper middle axes are the actual product zero section. -/
theorem globalProductMap_zero_affine (b : Bool) (a : ℂ) :
    globalProductMap (zeroSection (RiemannSphere.standardCharts.affineMap b a)) =
      FixedCoordinates.globalAxis (chartTriangle b) a := by
  have h0 : radiusSq (0 : Fibre) < 4 * (CD).radius := by
    rw [radiusSq_zero]
    exact mul_pos (by norm_num) (CD).radius_pos
  have hp : zeroSection (RiemannSphere.standardCharts.affineMap b a) =
      (⟨baseProductChart b (a, 0), h0⟩ : smallNormalProduct) := Subtype.ext rfl
  rw [hp, globalProductMap_baseProductChart, coordinatePoint_zero]
  rfl

/-- The zero section is exactly the original named fixed-curve parametrization. -/
theorem globalProductMap_zeroSection (p : RiemannSphere) :
    globalProductMap (zeroSection p) = CuspGeometry.doubleCurveParametrization 1 p := by
  induction p using OnePoint.rec with
  | infty =>
      have h := globalProductMap_zero_affine true (0 : ℂ)
      change globalProductMap (zeroSection (RiemannSphere.infinityParametrization 0)) = _ at h
      rw [RiemannSphere.infinityParametrization_zero] at h
      calc
        globalProductMap (zeroSection ∞) = FixedCoordinates.globalAxis (chartTriangle true) 0 := h
        _ = CuspGeometry.doubleCurveParametrization 1 ∞ := by
          rw [FixedCoordinates.globalAxis_eq_native]
          rfl
  | coe a =>
      calc
        globalProductMap (zeroSection (a : RiemannSphere)) =
            FixedCoordinates.globalAxis (chartTriangle false) a :=
          globalProductMap_zero_affine false a
        _ = CuspGeometry.doubleCurveParametrization 1 (a : RiemannSphere) := by
          rw [FixedCoordinates.globalAxis_eq_native]
          rfl

/-- Injectivity on the actual compact zero section comes from the proved native curve embedding. -/
theorem globalProductMap_injective_zeroSection :
    Function.Injective (globalProductMap ∘ zeroSection) := by
  have he : globalProductMap ∘ zeroSection = CuspGeometry.doubleCurveParametrization 1 :=
    funext globalProductMap_zeroSection
  rw [he]
  exact (CuspGeometry.doubleCurveParametrization_isEmbedding 1).injective

theorem globalProductMap_zeroSection_range :
    range (globalProductMap ∘ zeroSection) = CuspGeometry.doubleCurve 1 := by
  have he : globalProductMap ∘ zeroSection = CuspGeometry.doubleCurveParametrization 1 :=
    funext globalProductMap_zeroSection
  rw [he, CuspGeometry.doubleCurveParametrization_range]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
