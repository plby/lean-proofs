import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonBaseJacobian
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonCoverRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonCoverSections
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonPatches

/-!
# Exact compatibility of the regular form with the elliptic extensions

Both sections are pulled back by the same actual elliptic covering map.
The genuine logarithmic gauge has determinant one, and the base derivative
is the derivative of the actual global finite coordinate.  Equality of
the resulting alternating covectors therefore gives equality in the
original global canonical fibre.  The covering differential is invertible,
including above the central fibre; no Jacobian or gluing identity is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical
open HolomorphicForms.EllipticCover

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] coverChartedSpace starCoverChartedSpace cover_isManifold
  starCover_isManifold Threefold.chartedSpace Threefold.space_isManifold
  specialFullFillingChartedSpace specialEllipticPieceChartedSpace

/-- Pullback of the actual global canonical fibre by the genuine covering
differential, as an equivalence of full alternating three-covectors. -/
def coverPullbackEquiv (j : Kind) (x : Cover j) :
    Threefold.Canonical.bundle.Fiber (globalCover j x) ≃L[ℂ] TopCovector :=
  (Threefold.Canonical.intrinsicEquiv (globalCover j x)).trans
    (globalCoverDerivativeEquiv j x).symm.continuousAlternatingMapCongrLeft

@[simp] theorem coverPullbackEquiv_apply (j : Kind) (x : Cover j)
    (v : Threefold.Canonical.bundle.Fiber (globalCover j x)) :
    coverPullbackEquiv j x v =
      (Threefold.Canonical.intrinsicEquiv (globalCover j x) v).compContinuousLinearMap
        (mfderiv IF IF (globalCover j) x) := rfl

/-- The quotient function recovers its actual disc value on the original root cover. -/
@[simp] theorem fullRatio_fullCover (j : Kind) (x : Cover j) :
    fullRatio j (fullCover j x) = ratio j x.1.val := rfl

/-- The scalar comparison is the exact native base chain rule together
with the proved cancellation of the actual three local orders. -/
theorem coverRegularCoefficient_eq_ratio (j : Kind) (s : RootStar j) :
    coverRegularCoefficient j s =
      ratio j s.val.val * SectionsUnit.specialCoefficient j s.val.val := by
  rw [coverRegularCoefficient,
    ← baseDerivative_eq_regularCoordinateDerivative_mul_baseJacobian j s]
  exact coefficient_eq_ratio_mul j s.val.val s.property

/-- Equality in the literal global canonical fibre above each punctured
root-cover point follows from the invertible actual differential. -/
theorem globalSection_cover_eq (j : Kind) (x : CoverStar j) :
    GlobalRegular.globalSection (puncturedCoverPoint j x) =
      fullRatio j (fullCover j (starCoverInclusion j x)) •
        Sections.sectionAlongInclusion j (localCover j (starCoverInclusion j x)) := by
  let e := coverPullbackEquiv j (starCoverInclusion j x)
  have ho : e (GlobalRegular.globalSection (puncturedCoverPoint j x)) =
      coverRegularCoefficient j x.1 • volume := globalRegular_cover_pullback j x
  have hl : e (Sections.sectionAlongInclusion j (localCover j (starCoverInclusion j x))) =
      SectionsUnit.specialCoefficient j x.1.val.val • volume :=
    localSection_cover_pullback j (starCoverInclusion j x)
  have hc : coverRegularCoefficient j x.1 • volume =
      fullRatio j (fullCover j (starCoverInclusion j x)) •
        (SectionsUnit.specialCoefficient j x.1.val.val • volume) := by
    rw [coverRegularCoefficient_eq_ratio, fullRatio_fullCover, smul_smul]
    rfl
  apply e.injective
  exact ho.trans (hc.trans ((e.map_smul
    (fullRatio j (fullCover j (starCoverInclusion j x)))
    (Sections.sectionAlongInclusion j (localCover j (starCoverInclusion j x)))).trans
      (congrArg (fun α : TopCovector =>
        fullRatio j (fullCover j (starCoverInclusion j x)) • α) hl)).symm)

/-- The equality holds at every regular point of the entire original elliptic piece. -/
theorem globalSection_on_elliptic_piece (j : Kind) (x : SpecialEllipticPiece j)
    (hx : EllipticGeometry.inclusion j x ∈ regularLocus) :
    GlobalRegular.globalSection ⟨EllipticGeometry.inclusion j x, hx⟩ =
      fullRatio j x.val • Sections.sectionAlongInclusion j x := by
  obtain ⟨z, rfl⟩ := localCover_surjective j x
  have hz : rootCoordinate j z.1 ≠ 0 :=
    (globalCover_projection_mem_regular_iff j z).mp hx
  let w : CoverStar j := (⟨z.1, hz⟩, z.2)
  exact globalSection_cover_eq j w

/-- The genuine holomorphic section on the full global elliptic patch
extends the original regular form through its actual logarithmic overlap. -/
theorem globalSection_eq_extendedSection (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) (hy : y.val ∈ regularLocus) :
    GlobalRegular.globalSection ⟨y.val, hy⟩ = extendedSection j y := by
  obtain ⟨x, rfl⟩ := (EllipticGeometry.nativePatchBiholomorph j).surjective y
  exact (globalSection_on_elliptic_piece j x hy).trans (extendedSection_inclusion j x).symm

/-- Exact whole-overlap comparison with the already constructed local canonical section. -/
theorem globalSection_eq_patchRatio_smul (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) (hy : y.val ∈ regularLocus) :
    GlobalRegular.globalSection ⟨y.val, hy⟩ = patchRatio j y • Sections.patchSection j y :=
  globalSection_eq_extendedSection j y hy

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
