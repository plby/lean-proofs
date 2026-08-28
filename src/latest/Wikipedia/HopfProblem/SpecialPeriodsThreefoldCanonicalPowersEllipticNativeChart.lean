import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersEllipticDiscUnit
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistCoordinates

/-!
# The quartic comparison in the actual native elliptic charts

The original root coordinate of every native filling chart gives the
actual normalized sphere coordinate.  The effective-divisor section's
coefficient in the corresponding glued chart is exactly the previously
constructed weighted canonical coefficient.  Consequently its square
and the actual pulled-back point equation differ by the proved
holomorphic nowhere-zero disc unit on the entire chart source.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic

open Triangle EllipticFilling TrianglePeriodFamily.Canonical GlobalEllipticComparison

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  specialEllipticPieceChartedSpace specialFullFillingChartedSpace
  triangleCompactifiedChartedSpace

local instance powersNativeFullManifold (j : Wikipedia.HopfProblem.Elliptic.Kind) :
    IsManifold IF ω (SpecialFullFilling j) := (specialFullFilling_construction j).2.2.1

local instance powersNativeSmallManifold (j : Wikipedia.HopfProblem.Elliptic.Kind) :
    IsManifold IF ω (SpecialEllipticPiece j) := specialEllipticPiece_isManifold j

/-- The original compactified elliptic chart inverts the actual full-disc
lift at precisely its original power coordinate, including root zero. -/
theorem neighborhoodLift_projection (j : Wikipedia.HopfProblem.Elliptic.Kind) (s : Disc) :
    triangleCompactifiedProjection (neighborhoodLift j s) =
      (punctureChart (some j)).symm ((s : ℂ) ^ j.order) := by
  have hs : triangleCompactifiedProjection (neighborhoodLift j s) ∈
      (punctureChart (some j)).source := by
    change triangleOpenInclusion (triangleOrbitProjection (neighborhoodLift j s)) ∈
      (ellipticCompactifiedChart j).source
    apply (openInclusion_mem_ellipticCompactifiedChart_source j _).mpr
    rw [ellipticFullChart_source]
    exact ⟨neighborhoodLift j s, ((ellipticNeighborhoodChart j).symm s).property, rfl⟩
  have hc : punctureChart (some j)
      (triangleCompactifiedProjection (neighborhoodLift j s)) = (s : ℂ) ^ j.order := by
    change ellipticCompactifiedChart j
      (triangleCompactifiedProjection ((ellipticNeighborhoodChart j).symm s)) = _
    rw [ellipticCompactifiedChart_projection]
    change (((ellipticNeighborhoodChart j ((ellipticNeighborhoodChart j).symm s) : Disc) : ℂ) ^
      j.order) = _
    rw [Diffeomorph.apply_symm_apply]
  exact ((punctureChart (some j)).left_inv hs).symm.trans
    (congrArg (punctureChart (some j)).symm hc)

abbrev SmallChart (a : SpecialEllipticPiece .four) :
    TopologicalSpace.Opens (SpecialEllipticPiece .four) :=
  ⟨(chartAt Model a).source, (chartAt Model a).open_source⟩

/-- Forgetting the small-piece restriction retains the actual full chart. -/
def smallChartToFull (a : SpecialEllipticPiece .four) (x : SmallChart a) :
    Elliptic.fullChartSource .four a.val :=
  ⟨x.val.val, Elliptic.pieceInclusion_mem_chart_source .four a x.val x.property⟩

theorem smallChartToFull_holomorphic (a : SpecialEllipticPiece .four) :
    ContMDiff IF IF ω (smallChartToFull a) := by
  have hh : ContMDiff IF IF ω (fun x : SmallChart a => x.val.val) :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  intro x
  have he : ContMDiffAt IF IF ω (Subtype.val ∘ smallChartToFull a) x ↔
      ContMDiffAt IF IF ω (smallChartToFull a) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hh x)

/-- The literal first native coordinate, as a point of the original disc. -/
def smallChartBase (a : SpecialEllipticPiece .four) (x : SmallChart a) : Disc :=
  Sections.fullChartBase .four a.val (smallChartToFull a x)

theorem smallChartBase_holomorphic (a : SpecialEllipticPiece .four) :
    ContMDiff IF 𝓘(ℂ) ω (smallChartBase a) :=
  (Sections.fullChartBase_holomorphic .four a.val).comp (smallChartToFull_holomorphic a)

theorem smallChartBase_parameter (a : SpecialEllipticPiece .four) (x : SmallChart a) :
    EllipticGeometry.parameter .four x.val = (smallChartBase a x : ℂ) ^ 4 := by
  rw [smallChartBase, Sections.fullChartBase_coe]
  exact (specialLocalData .four).projection_chart
    (Wikipedia.HopfProblem.Elliptic.Kind.twist .four)
    (Wikipedia.HopfProblem.Elliptic.mainTwist_admissible .four) a.val x.val.val
    (Elliptic.pieceInclusion_mem_chart_source .four a x.val x.property)

/-- The finite sphere coordinate is the actual disc coordinate in every
native chart, with the original projection and original gluing. -/
theorem finiteCoordinate_inclusion (a : SpecialEllipticPiece .four) (x : SmallChart a) :
    CanonicalGlobal.BaseTwist.finiteCoordinate
        (Threefold.projectionSphere (EllipticGeometry.inclusion .four x.val)) =
      discCoordinate .four (smallChartBase a x) := by
  have hb : Threefold.projection (EllipticGeometry.inclusion .four x.val) =
      triangleCompactifiedProjection (neighborhoodLift .four (smallChartBase a x)) := by
    rw [EllipticGeometry.projection_inclusion, neighborhoodLift_projection]
    change (punctureChart (some .four)).symm (EllipticGeometry.parameter .four x.val) = _
    rw [smallChartBase_parameter]
    rfl
  have hs : Threefold.projectionSphere (EllipticGeometry.inclusion .four x.val) =
      (discCoordinate .four (smallChartBase a x) : RiemannSphere) := by
    rw [discCoordinate_coe]
    exact congrArg triangleSphereUniformization hb
  rw [hs, CanonicalGlobal.BaseTwist.finiteCoordinate_coe]

/-- The adapted chart is one of the actual original global manifold charts. -/
abbrev nativeChart (a : SpecialEllipticPiece .four) : atlas Model Threefold.Space :=
  Threefold.Canonical.patchChart (some (some .four)) a

theorem divisorCoefficient_native (a : SpecialEllipticPiece .four) (x : SmallChart a) :
    GlobalEllipticDivisor.transitions.localCoefficient GlobalEllipticDivisor.canonicalSection
        (some (nativeChart a)) (EllipticGeometry.inclusion .four x.val) =
      SectionsUnit.specialCoefficient .four (smallChartBase a x) := by
  have hpatch : EllipticGeometry.inclusion .four x.val ∈ GlobalEllipticDivisor.patch :=
    (EllipticGeometry.nativePatchBiholomorph .four x.val).property
  have hi : EllipticGeometry.inclusion .four x.val ∈ (nativeChart a).val.source :=
    Threefold.Canonical.inclusion_mem_patchChart_source (some (some .four)) a x.val x.property
  rw [GlobalEllipticDivisor.canonicalSection_localCoefficient (some (nativeChart a))
    ⟨hpatch, hi⟩]
  change GlobalEllipticDivisor.patchCoefficient (nativeChart a)
    (EllipticGeometry.inclusion .four x.val) = _
  have he := GlobalEllipticDivisor.patchCoefficient_eq_topCovector (nativeChart a)
    (EllipticGeometry.nativePatchBiholomorph .four x.val)
  change GlobalEllipticDivisor.patchCoefficient (nativeChart a)
      (EllipticGeometry.inclusion .four x.val) =
    coefficient (Threefold.Canonical.inCoordinates (nativeChart a)
      (EllipticGeometry.inclusion .four x.val)
      (Sections.patchSection .four (EllipticGeometry.nativePatchBiholomorph .four x.val))) at he
  rw [he]
  rw [Sections.patchSection_inCoordinates .four a x.val x.property,
    Sections.fullSection_inCoordinates .four a.val x.val.val
      (Elliptic.pieceInclusion_mem_chart_source .four a x.val x.property)]
  simp only [coefficient_smul, coefficient_volume, mul_one]
  rfl

def nativeCoefficientUnit (a : SpecialEllipticPiece .four) (x : SmallChart a) : ℂ :=
  squaredCoefficientUnit (smallChartBase a x)

theorem nativeCoefficientUnit_holomorphic (a : SpecialEllipticPiece .four) :
    ContMDiff IF 𝓘(ℂ) ω (nativeCoefficientUnit a) :=
  squaredCoefficientUnit_holomorphic.comp (smallChartBase_holomorphic a)

theorem nativeCoefficientUnit_ne_zero (a : SpecialEllipticPiece .four) (x : SmallChart a) :
    nativeCoefficientUnit a x ≠ 0 := squaredCoefficientUnit_ne_zero (smallChartBase a x)

/-- The exact local divisor comparison, throughout the original native
chart source and in particular at every central point. -/
theorem nativeCoefficientUnit_equation (a : SpecialEllipticPiece .four) (x : SmallChart a) :
    nativeCoefficientUnit a x *
        (GlobalEllipticDivisor.transitions.localCoefficient GlobalEllipticDivisor.canonicalSection
          (some (nativeChart a)) (EllipticGeometry.inclusion .four x.val)) ^ 2 =
      CanonicalGlobal.BaseTwist.finiteCoordinate
        (Threefold.projectionSphere (EllipticGeometry.inclusion .four x.val)) - 1 := by
  rw [divisorCoefficient_native, finiteCoordinate_inclusion, nativeCoefficientUnit, mul_comm]
  exact (squaredCoefficientUnit_factor (smallChartBase a x)).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic
