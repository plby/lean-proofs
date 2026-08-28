import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticSpecial
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticGaugeComparison
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionRegular

/-!
# Vertical-flow compatibility on the actual small elliptic overlaps

The small overlap used to construct the threefold is the restriction of
the actual logarithmic-gauge comparison.  Its equivariance therefore
follows from the proved literal translation calculation, with no new
identification of the filling or its atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  specialRegularFamilyChartedSpace

/-- The actual attaching map intertwines the genuine elliptic filling
flow and the genuine regular-family flow. -/
theorem specialEllipticOverlap_specialFlow (j : Kind) (s : ℂ)
    (x : EllipticGeometry.LocalSpace j) (hx : x ∈ (specialEllipticOverlap j).source) :
    specialEllipticOverlap j (specialFlow j s x) =
      Regular.flow s (specialEllipticOverlap j x) := by
  have hx0 : (specialFullFillingProjection j x.val : ℂ) ≠ 0 :=
    (smallOverlap_mem_source specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j x).mp hx
  have hs0 : (specialFullFillingProjection j (specialFlow j s x).val : ℂ) ≠ 0 := by
    rw [specialFlow_coe, specialFullFlow_projection]
    exact hx0
  change smallOverlap specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j (specialFlow j s x) =
    Regular.flow s (smallOverlap specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j x)
  rw [smallOverlap_apply_mainStar specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j (specialFlow j s x) hs0,
    smallOverlap_apply_mainStar specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j x hx0]
  exact Gauge.puncturedFillingBiholomorph_fillingStarFlow specialPeriodMap j
    specialPeriodMap_generator₁ specialPeriodMap_generator₂ s ⟨x.val, hx0⟩

/-- The original target of the attaching map is invariant under the
regular-family translation. -/
theorem regularFlow_mem_overlap_target (j : Kind) (s : ℂ) (y : SpecialRegularFamily)
    (hy : y ∈ (specialEllipticOverlap j).target) :
    Regular.flow s y ∈ (specialEllipticOverlap j).target := by
  have hx := (specialEllipticOverlap j).map_target hy
  have hsx := (specialFlow_mem_overlap_source_iff j s _).mpr hx
  have he := specialEllipticOverlap_specialFlow j s ((specialEllipticOverlap j).symm y) hx
  have he' : specialEllipticOverlap j
      (specialFlow j s ((specialEllipticOverlap j).symm y)) = Regular.flow s y :=
    he.trans (congrArg (Regular.flow s) ((specialEllipticOverlap j).right_inv hy))
  exact he' ▸ (specialEllipticOverlap j).map_source hsx

/-- Compatibility also holds in the inverse attaching direction, on
the complete original overlap target. -/
theorem specialEllipticOverlap_symm_regularFlow (j : Kind) (s : ℂ)
    (y : SpecialRegularFamily) (hy : y ∈ (specialEllipticOverlap j).target) :
    (specialEllipticOverlap j).symm (Regular.flow s y) =
      specialFlow j s ((specialEllipticOverlap j).symm y) := by
  have hx := (specialEllipticOverlap j).map_target hy
  have hsx := (specialFlow_mem_overlap_source_iff j s _).mpr hx
  have he := specialEllipticOverlap_specialFlow j s ((specialEllipticOverlap j).symm y) hx
  have he' : specialEllipticOverlap j
      (specialFlow j s ((specialEllipticOverlap j).symm y)) = Regular.flow s y :=
    he.trans (congrArg (Regular.flow s) ((specialEllipticOverlap j).right_inv hy))
  exact (congrArg (fun z => (specialEllipticOverlap j).symm z) he'.symm).trans
    ((specialEllipticOverlap j).left_inv hsx)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic
