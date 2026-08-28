import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticOverlaps

/-!
# The exact logarithmic gauge on the genuine elliptic covering maps

The punctured root cover has two maps to the actual global threefold:
the affine filling map and the untwisted regular-family map.  Their
comparison is the original logarithmic period translation, on every
complex fibre and with the original period coordinates unchanged.
Local logarithms give the same comparison without requiring a global
holomorphic logarithm on the punctured root disc.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic EllipticFilling TrianglePeriodFamily CuspUniformization

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  specialRegularFamilyChartedSpace Threefold.chartedSpace coverChartedSpace discCoverChartedSpace

/-- The literal puncture of the same root domain. -/
def rootStarDomain (j : Kind) : TopologicalSpace.Opens (Root j) :=
  ⟨{z | rootCoordinate j z ≠ 0},
    isOpen_ne_fun (rootCoordinate_holomorphic j).continuous continuous_const⟩

abbrev RootStar (j : Kind) := rootStarDomain j

/-- Forget only the small radius bound, retaining the nonzero disc root. -/
def starToBase (j : Kind) (z : RootStar j) : LogGauge.BaseStar :=
  ⟨z.val.val, z.property⟩

@[simp] theorem starToBase_coe (j : Kind) (z : RootStar j) :
    (starToBase j z : Disc) = (z.val : Disc) := rfl

theorem starToBase_holomorphic (j : Kind) :
    ContMDiff I₁ I₁ ω (starToBase j) := by
  intro z
  have he : ContMDiffAt I₁ I₁ ω (Subtype.val ∘ starToBase j) z ↔
      ContMDiffAt I₁ I₁ ω (starToBase j) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_subtype_val.comp contMDiff_subtype_val) z)

/-- The original inverse Cayley chart, now in the actual regular source. -/
def regularBase (j : Kind) : RootStar j → TriangleRegularPoint :=
  localBase j ∘ starToBase j

theorem regularBase_holomorphic (j : Kind) :
    ContMDiff I₁ I₁ ω (regularBase j) :=
  (localBase_holomorphic j).comp (starToBase_holomorphic j)

@[simp] theorem regularBase_val (j : Kind) (z : RootStar j) :
    (regularBase j z : ℍ) = neighborhoodLift j z.val.val := rfl

abbrev CoverStar (j : Kind) := RootStar j × ComplexPlane₂

/-- The unchanged inherited product atlas of the punctured cover. -/
@[instance_reducible] def starCoverChartedSpace (j : Kind) :
    ChartedSpace FamilyModel (CoverStar j) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (CoverStar j))

attribute [local instance] starCoverChartedSpace

theorem starCover_isManifold (j : Kind) : IsManifold IF ω (CoverStar j) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) (RootStar j) ComplexPlane₂

/-- The open inclusion forgets just the puncture. -/
def starCoverInclusion (j : Kind) (x : CoverStar j) : Cover j := (x.1.val, x.2)

theorem starCoverInclusion_holomorphic (j : Kind) :
    ContMDiff IF IF ω (starCoverInclusion j) := by
  rw [modelWithCornersSelf_prod]
  exact (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd

/-- The same complex period-vector point in the full punctured disc cover. -/
def toLogCover (j : Kind) (x : CoverStar j) : LogGauge.CoverStar :=
  ⟨(x.1.val.val, x.2), x.1.property⟩

theorem toLogCover_holomorphic (j : Kind) : ContMDiff IF IF ω (toLogCover j) := by
  have hb : ContMDiff IF I₁ ω (fun x : CoverStar j => x.1.val.val) := by
    have hfst : ContMDiff IF I₁ ω (Prod.fst : CoverStar j → RootStar j) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_fst
    exact contMDiff_subtype_val.comp (contMDiff_subtype_val.comp hfst)
  have hv : ContMDiff IF I₂ ω (Prod.snd : CoverStar j → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hp : ContMDiff IF IF ω
      (fun x : CoverStar j => (x.1.val.val, x.2)) := by
    simpa only [← modelWithCornersSelf_prod] using hb.prodMk hv
  intro x
  have he : ContMDiffAt IF IF ω (Subtype.val ∘ toLogCover j) x ↔
      ContMDiffAt IF IF ω (toLogCover j) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hp x)

/-- The untwisted regular-family covering map on the same punctured
root coordinates and the same complex fibre vector. -/
def regularCover (j : Kind) (x : CoverStar j) : Threefold.Space :=
  regularFamilyInclusion
    (regularMap specialPeriodMap j specialPeriodMap_generator₁ specialPeriodMap_generator₂
      (LogGauge.project (specialLocalData j).periods (toLogCover j x)))

theorem regularCover_holomorphic (j : Kind) : ContMDiff IF IF ω (regularCover j) := by
  let := (specialLocalData j).periods.totalChartedSpace
  exact regularFamilyInclusion_holomorphic.comp
    ((regularMap_holomorphic specialPeriodMap j specialPeriodMap_generator₁
      specialPeriodMap_generator₂).comp
      ((LogGauge.project_holomorphic (specialLocalData j).periods).comp
        (toLogCover_holomorphic j)))

/-- Fibre translation by a selected scalar logarithm branch. -/
def gaugeLift (j : Kind) (a : ℂ → ℂ) (x : CoverStar j) : CoverStar j :=
  (x.1, x.2 + a (rootCoordinate j x.1.val) •
    LogGauge.periodVector (specialLocalData j).periods j.twist x.1.val.val)

@[simp] theorem toLogCover_gaugeLift (j : Kind) (a : ℂ → ℂ) (x : CoverStar j) :
    toLogCover j (gaugeLift j a x) =
      LogGauge.gaugeLift (specialLocalData j).periods j.twist a (toLogCover j x) := rfl

/-- The actual small affine quotient followed by its actual overlap is
the original logarithmic gauge, followed by the untwisted regular map. -/
theorem overlap_localCover (j : Kind) (x : CoverStar j) :
    specialEllipticOverlap j (localCover j (starCoverInclusion j x)) =
      regularMap specialPeriodMap j specialPeriodMap_generator₁ specialPeriodMap_generator₂
        (LogGauge.gaugeMap (specialLocalData j).periods j.twist
          (LogGauge.project (specialLocalData j).periods (toLogCover j x))) := by
  have hx : (fillingProjection specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ j (localCover j (starCoverInclusion j x)).val : ℂ) ≠ 0 :=
    pow_ne_zero j.order x.1.property
  change smallOverlap specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j _ = _
  rw [smallOverlap_apply_mainStar specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j _ hx]
  change (tautologicalOverlapBiholomorph specialPeriodMap j specialPeriodMap_generator₁
    specialPeriodMap_generator₂
    (LogGauge.fillingToTautologicalBiholomorph (specialLocalData j) j.twist
      (mainTwist_admissible j)
      (LogGauge.fillingStarProject (specialLocalData j) j.twist (mainTwist_admissible j)
        (LogGauge.project (specialLocalData j).periods (toLogCover j x))))).val = _
  rw [LogGauge.fillingToTautologicalBiholomorph_project]
  exact congrArg Subtype.val (tautologicalOverlapBiholomorph_project specialPeriodMap j
    specialPeriodMap_generator₁ specialPeriodMap_generator₂
    (LogGauge.gaugeMap (specialLocalData j).periods j.twist
      (LogGauge.project (specialLocalData j).periods (toLogCover j x))))

/-- The actual global gluing identifies the two maps on the full
punctured root cover, not merely on a selected path or zero section. -/
theorem globalCover_eq_regular_gauge (j : Kind) (x : CoverStar j) :
    globalCover j (starCoverInclusion j x) =
      regularFamilyInclusion
        (regularMap specialPeriodMap j specialPeriodMap_generator₁
          specialPeriodMap_generator₂
          (LogGauge.gaugeMap (specialLocalData j).periods j.twist
            (LogGauge.project (specialLocalData j).periods (toLogCover j x)))) := by
  have hx : localCover j (starCoverInclusion j x) ∈ (specialEllipticOverlap j).source := by
    rw [specialEllipticOverlap_source]
    exact (localCover_projection_mem_regular_iff j (starCoverInclusion j x)).mpr
      x.1.property
  have he : globalCover j (starCoverInclusion j x) =
      regularFamilyInclusion (specialEllipticOverlap j
        (localCover j (starCoverInclusion j x))) := by
    change gluingData.inclusion (some (some j)) _ = gluingData.inclusion none _
    exact (gluingData.inclusion_eq_iff (some (some j)) none _ _).mpr ⟨hx, rfl⟩
  exact he.trans (congrArg regularFamilyInclusion (overlap_localCover j x))

/-- Every local logarithm gives exactly the same genuine global map.
The branch center is arbitrary nonzero; no global holomorphic logarithm
is assumed on the punctured root disc. -/
theorem globalCover_eq_regularCover_localLog (j : Kind) {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (x : CoverStar j) :
    globalCover j (starCoverInclusion j x) =
      regularCover j (gaugeLift j (localLog z₀) x) := by
  rw [globalCover_eq_regular_gauge,
    LogGauge.gaugeMap_project_localLog (specialLocalData j).periods j.twist hz₀]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
