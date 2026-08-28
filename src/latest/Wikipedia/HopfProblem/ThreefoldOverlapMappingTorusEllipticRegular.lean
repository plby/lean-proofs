import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusSpaces
import Wikipedia.HopfProblem.EllipticLogGaugeSource

/-!
# The actual elliptic boundary map into the regular period family

This identifies the literal global attachment map with the original
logarithmic gauge and inverse Cayley map, on every cylinder point and
every real-period torus coordinate.  The gauge translation is not
discarded when identifying the affine monodromy.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.EllipticFilling
open Wikipedia.HopfProblem.Elliptic TrianglePeriodFamily

attribute [local instance] specialRegularFamilyChartedSpace specialEllipticPieceChartedSpace
  specialFullFillingChartedSpace

/-- The original global overlap map is exactly the constructed native elliptic overlap. -/
theorem puncturedPieceToRegular_elliptic (j : Kind) (x : PuncturedPiece (some j)) :
    puncturedPieceToRegular (some j) x = specialEllipticOverlap j x.val := by
  apply (inclusion_openEmbedding none).injective
  have hx : x.val ∈ (specialEllipticOverlap j).source := by
    rw [specialEllipticOverlap_source]
    exact x.property
  refine (puncturedPieceToRegular_inclusion (some j) x).trans ?_
  change gluingData.inclusion (some (some j)) x.val =
    gluingData.inclusion none (specialEllipticOverlap j x.val)
  exact (gluingData.inclusion_eq_iff (some (some j)) none _ _).mpr ⟨hx, rfl⟩

/-- The actual root of the positive native boundary loop. -/
def specialBoundaryRoot (j : Kind) (t : ℝ) : Disc :=
  root j.order (specialBaseCover.radius (some j)) (specialRootRadius j)
    ((t / j.order : ℝ) : Circle)

theorem specialBoundaryRoot_ne_zero (j : Kind) (t : ℝ) :
    (specialBoundaryRoot j t : ℂ) ≠ 0 := root_ne_zero _ _ _ _

/-- A boundary representative in the unchanged local flat period family. -/
def specialBoundaryFamilyStar (j : Kind) (t : ℝ) (x : RealTorus₄) :
    LogGauge.FamilyStar (specialLocalData j).periods :=
  ⟨(specialBoundaryRoot j t, x), specialBoundaryRoot_ne_zero j t⟩

/-- The full actual elliptic overlap applies the original logarithmic gauge. -/
theorem specialBoundaryCylinder_overlap (j : Kind) (t : ℝ) (x : RealTorus₄) :
    specialEllipticOverlap j (specialBoundaryCylinder j (t, x)) =
      regularMap specialPeriodMap j specialPeriodMap_generator₁ specialPeriodMap_generator₂
        (LogGauge.gaugeMap (specialLocalData j).periods j.twist
          (specialBoundaryFamilyStar j t x)) := by
  have hx : (specialFullFillingProjection j (specialBoundaryCylinder j (t, x)).val : ℂ) ≠ 0 :=
    (specialPiece_regular_iff j _).mp
      (specialBoundaryInclusion j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x))).property
  have hstar : (⟨(specialBoundaryCylinder j (t, x)).val, hx⟩ :
      MainFillingStar specialPeriodMap j specialPeriodMap_generator₁ specialPeriodMap_generator₂) =
    LogGauge.fillingStarProject (specialLocalData j) j.twist (mainTwist_admissible j)
      (specialBoundaryFamilyStar j t x) := by
    apply Subtype.ext
    exact specialBoundaryInclusion_mk j t x
  change smallOverlap specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
    specialBaseCover j _ = _
  rw [smallOverlap_apply_mainStar specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j _ hx, hstar]
  change (tautologicalOverlapBiholomorph specialPeriodMap j specialPeriodMap_generator₁
    specialPeriodMap_generator₂
    (LogGauge.fillingToTautologicalBiholomorph (specialLocalData j) j.twist
      (mainTwist_admissible j)
      (LogGauge.fillingStarProject (specialLocalData j) j.twist (mainTwist_admissible j)
        (specialBoundaryFamilyStar j t x)))).val = _
  rw [LogGauge.fillingToTautologicalBiholomorph_project]
  exact congrArg Subtype.val (tautologicalOverlapBiholomorph_project specialPeriodMap j
    specialPeriodMap_generator₁ specialPeriodMap_generator₂
    (LogGauge.gaugeMap (specialLocalData j).periods j.twist (specialBoundaryFamilyStar j t x)))

/-- The global coefficient map is the original small-overlap map on every cylinder point. -/
theorem boundaryToRegularFamily_elliptic_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    boundaryToRegularFamily (some j) (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      specialEllipticOverlap j (specialBoundaryCylinder j (t, x)) := by
  change puncturedPieceToRegular (some j)
    (specialBoundaryInclusion j (MappingTorus.mk _ (t, x))) = _
  exact puncturedPieceToRegular_elliptic j _

/-- The exact regular quotient representative, including its original flat gauge translation. -/
theorem boundaryToRegularFamily_elliptic_flat (j : Kind) (t : ℝ) (x : RealTorus₄) :
    boundaryToRegularFamily (some j) (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      (regularData specialPeriodMap specialPeriodMap_generator₁
        specialPeriodMap_generator₂).quotient
        (localBase j ⟨specialBoundaryRoot j t, specialBoundaryRoot_ne_zero j t⟩,
          x + LogGauge.sectionCoordinate (specialLocalData j).periods j.twist
            (specialBoundaryRoot j t)) := by
  rw [boundaryToRegularFamily_elliptic_mk, specialBoundaryCylinder_overlap]
  rfl

/-- A genuine continuous logarithm along the entire real boundary cylinder. -/
def specialBoundaryLog (j : Kind) (t : ℝ) : ℂ :=
  CuspUniformization.logarithm ((specialRootRadius j : ℝ) : ℂ) +
    (t : ℂ) / (j.order : ℂ)

theorem specialBoundaryLog_exponential (j : Kind) (t : ℝ) :
    CuspUniformization.exponential (specialBoundaryLog j t) =
      (specialBoundaryRoot j t : ℂ) := by
  have ha : (((specialRootRadius j : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (specialRootRadius j).property.1.ne'
  rw [specialBoundaryLog, CuspUniformization.exponential_add,
    CuspUniformization.exponential_logarithm ha]
  change ((specialRootRadius j : ℝ) : ℂ) * CuspUniformization.exponential ((t : ℂ) / j.order) =
    (specialRootRadius j : ℝ) • (phase (((t / j.order : ℝ) : Circle)) : ℂ)
  rw [phase_real, Complex.real_smul]
  push_cast
  rfl

/-- The displayed continuous logarithm gives the exact original period-vector translation. -/
theorem specialBoundary_sectionCoordinate (j : Kind) (t : ℝ) :
    LogGauge.sectionCoordinate (specialLocalData j).periods j.twist (specialBoundaryRoot j t) =
      standardLattice.mkQ
        (((specialLocalData j).periods.periodEquiv (specialBoundaryRoot j t)).symm
          (specialBoundaryLog j t •
            LogGauge.periodVector (specialLocalData j).periods j.twist
              (specialBoundaryRoot j t))) := by
  have h := LogGauge.sectionMap_formula_of_exponential
    (specialLocalData j).periods j.twist
    ⟨specialBoundaryRoot j t, specialBoundaryRoot_ne_zero j t⟩ (specialBoundaryLog j t)
    (specialBoundaryLog_exponential j t)
  have hs := congrArg (fun y : (specialLocalData j).periods.TotalSpace => y.2) h
  change (0 : RealTorus₄) + LogGauge.sectionCoordinate (specialLocalData j).periods j.twist
    (specialBoundaryRoot j t) = standardLattice.mkQ
      (((specialLocalData j).periods.periodEquiv (specialBoundaryRoot j t)).symm
        (specialBoundaryLog j t • LogGauge.periodVector
          (specialLocalData j).periods j.twist (specialBoundaryRoot j t))) at hs
  simpa only [zero_add] using hs

/-- The actual boundary-to-regular map on all real-period representatives. -/
theorem boundaryToRegularFamily_elliptic_realCoordinates
    (j : Kind) (t : ℝ) (x : RealCoordinates) :
    boundaryToRegularFamily (some j)
        (MappingTorus.mk (flatTorusAffine j j.twist) (t, standardLattice.mkQ x)) =
      (regularData specialPeriodMap specialPeriodMap_generator₁
        specialPeriodMap_generator₂).quotient
        (localBase j ⟨specialBoundaryRoot j t, specialBoundaryRoot_ne_zero j t⟩,
          standardLattice.mkQ (x +
            ((specialLocalData j).periods.periodEquiv (specialBoundaryRoot j t)).symm
              (specialBoundaryLog j t • LogGauge.periodVector
                (specialLocalData j).periods j.twist (specialBoundaryRoot j t)))) := by
  rw [boundaryToRegularFamily_elliptic_flat, specialBoundary_sectionCoordinate, ← map_add]

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic
