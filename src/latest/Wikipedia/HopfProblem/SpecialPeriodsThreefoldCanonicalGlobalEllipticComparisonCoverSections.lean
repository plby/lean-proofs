import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonCoverGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonCoverPeriod

/-!
# Pullback of the actual elliptic canonical section to its root cover

The original finite quotient, lattice quotient, radius restriction and
global patch inclusion give the asserted full three-covector identity.
It remains valid on the central fibre, with the actual vanishing
coefficient of the constructed elliptic section.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical
open HolomorphicForms.EllipticCover

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] coverChartedSpace cover_isManifold Threefold.chartedSpace
  Threefold.space_isManifold specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  discProductChartedSpace discProductManifold

local instance ellipticUpstairsChartedSpace (j : Kind) :
    ChartedSpace Model (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalChartedSpace

local instance ellipticUpstairsManifold (j : Kind) :
    IsManifold I₃ ω (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalSpace_isManifold

/-- The original two quotient maps before the small-radius restriction. -/
def fullPeriodCover (j : Kind) (x : Disc × ComplexPlane₂) : SpecialFullFilling j :=
  Sections.fullQuotient j ((specialLocalData j).periods.quotientMap x)

theorem fullPeriodCover_holomorphic (j : Kind) :
    ContMDiff I₃ I₃ ω (fullPeriodCover j) :=
  (Sections.fullQuotient_isLocalDiffeomorph j).contMDiff.comp
    (specialLocalData j).periods.quotientMap_holomorphic

/-- Both quotient differentials are the actual native differentials. -/
theorem fullSection_period_cover_pullback (j : Kind) (x : Disc × ComplexPlane₂) :
    (Elliptic.fullIntrinsicEquiv j (fullPeriodCover j x)
      (Sections.fullSection j (fullPeriodCover j x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (fullPeriodCover j) x) =
          SectionsUnit.specialCoefficient j x.1 • volume := by
  have hd : mfderiv I₃ I₃ (fullPeriodCover j) x =
      (mfderiv I₃ I₃ (Sections.fullQuotient j)
        ((specialLocalData j).periods.quotientMap x)).comp
          (mfderiv I₃ I₃ (specialLocalData j).periods.quotientMap x) :=
    mfderiv_comp x
      ((Sections.fullQuotient_isLocalDiffeomorph j).contMDiff.mdifferentiable (by simp) _)
      ((specialLocalData j).periods.quotientMap_holomorphic.mdifferentiable (by simp) x)
  have hchain := congrArg (fun L : Model →L[ℂ] Model =>
    (Elliptic.fullIntrinsicEquiv j (fullPeriodCover j x)
      (Sections.fullSection j (fullPeriodCover j x))).compContinuousLinearMap L) hd
  change _ = ((Elliptic.fullIntrinsicEquiv j (fullPeriodCover j x)
      (Sections.fullSection j (fullPeriodCover j x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (Sections.fullQuotient j)
          ((specialLocalData j).periods.quotientMap x))).compContinuousLinearMap
            (mfderiv I₃ I₃ (specialLocalData j).periods.quotientMap x) at hchain
  have hp := Sections.fullSection_intrinsic_pullback j
    ((specialLocalData j).periods.quotientMap x)
  exact hchain.trans ((congrArg (fun α : TopCovector => α.compContinuousLinearMap
    (mfderiv I₃ I₃ (specialLocalData j).periods.quotientMap x)) hp).trans
      (periodQuotient_topCovector_pullback (fun s : Disc => (s : ℂ))
        (fun _ _ => rfl) (specialLocalData j).periods
        (SectionsUnit.specialCoefficient j x.1 • volume) x))

/-- Radius restriction has the identity differential, without changing either quotient. -/
theorem fullCover_mfderiv_eq_period (j : Kind) (x : Cover j) :
    mfderiv I₃ I₃ (fullCover j) x =
      mfderiv I₃ I₃ (fullPeriodCover j) (coverToPeriod j x) := by
  have h := mfderiv_comp x
    ((fullPeriodCover_holomorphic j).mdifferentiable (by simp) (coverToPeriod j x))
    ((coverToPeriod_holomorphic j).mdifferentiable (by simp) x)
  have hi := coverToPeriod_mfderiv j x
  have he : (mfderiv I₃ I₃ (fullPeriodCover j) (coverToPeriod j x)).comp
      (mfderiv I₃ I₃ (coverToPeriod j) x) =
        mfderiv I₃ I₃ (fullPeriodCover j) (coverToPeriod j x) := by
    exact (congrArg (fun L : Model →L[ℂ] Model =>
      (show Model →L[ℂ] Model from
        mfderiv I₃ I₃ (fullPeriodCover j) (coverToPeriod j x)).comp L) hi).trans
          (by ext v <;> rfl)
  exact h.trans he

/-- Exact pullback of the full-filling section, also above root zero. -/
theorem fullSection_cover_pullback (j : Kind) (x : Cover j) :
    (Elliptic.fullIntrinsicEquiv j (fullCover j x)
      (Sections.fullSection j (fullCover j x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (fullCover j) x) =
          SectionsUnit.specialCoefficient j x.1.val • volume := by
  exact (congrArg (fun L : Model →L[ℂ] Model =>
    (Elliptic.fullIntrinsicEquiv j (fullCover j x)
      (Sections.fullSection j (fullCover j x))).compContinuousLinearMap L)
        (fullCover_mfderiv_eq_period j x)).trans
          (fullSection_period_cover_pullback j (coverToPeriod j x))

/-- Restriction and global inclusion retain the actual full-filling differential pullback. -/
theorem sectionAlongInclusion_cover_pullback (j : Kind) (x : Cover j) :
    (Threefold.Canonical.intrinsicEquiv (globalCover j x)
      (Sections.sectionAlongInclusion j (localCover j x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (globalCover j) x) =
          SectionsUnit.specialCoefficient j x.1.val • volume := by
  have hd : mfderiv I₃ I₃ (globalCover j) x =
      (mfderiv I₃ I₃ (EllipticGeometry.inclusion j) (localCover j x)).comp
        (mfderiv I₃ I₃ (localCover j) x) :=
    mfderiv_comp x
      ((EllipticGeometry.inclusion_holomorphic j).mdifferentiable (by simp) _)
      ((localCover_holomorphic j).mdifferentiable (by simp) x)
  have hfull : mfderiv I₃ I₃ (fullCover j) x =
      (mfderiv I₃ I₃ (Elliptic.pieceInclusion j) (localCover j x)).comp
        (mfderiv I₃ I₃ (localCover j) x) :=
    mfderiv_comp x
      ((Elliptic.pieceInclusion_holomorphic j).mdifferentiable (by simp) _)
      ((localCover_holomorphic j).mdifferentiable (by simp) x)
  have hchain := congrArg (fun L : Model →L[ℂ] Model =>
    (Threefold.Canonical.intrinsicEquiv (globalCover j x)
      (Sections.sectionAlongInclusion j (localCover j x))).compContinuousLinearMap L) hd
  change _ = ((Threefold.Canonical.intrinsicEquiv (globalCover j x)
      (Sections.sectionAlongInclusion j (localCover j x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (EllipticGeometry.inclusion j) (localCover j x))).compContinuousLinearMap
          (mfderiv I₃ I₃ (localCover j) x) at hchain
  have hs := (Sections.sectionAlongInclusion_intrinsic_pullback j (localCover j x)).trans
    (Sections.smallSection_intrinsic j (localCover j x))
  have he := congrArg (fun α : TopCovector => α.compContinuousLinearMap
    (mfderiv I₃ I₃ (localCover j) x)) hs
  have hfinish := congrArg (fun L : Model →L[ℂ] Model =>
    (Elliptic.fullIntrinsicEquiv j (fullCover j x)
      (Sections.fullSection j (fullCover j x))).compContinuousLinearMap L) hfull.symm
  exact hchain.trans (he.trans (hfinish.trans (fullSection_cover_pullback j x)))

/-- The local section has its prescribed coefficient in the actual root cover. -/
theorem localSection_cover_pullback (j : Kind) (x : Cover j) :
    (Threefold.Canonical.intrinsicEquiv (globalCover j x)
      (Sections.sectionAlongInclusion j (localCover j x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (globalCover j) x) =
          SectionsUnit.specialCoefficient j x.1.val • volume :=
  sectionAlongInclusion_cover_pullback j x

/-- The identical statement for the section of the literal full global patch. -/
theorem patchSection_cover_pullback (j : Kind) (x : Cover j) :
    (Threefold.Canonical.intrinsicEquiv (globalCover j x)
      (Sections.patchSection j
        (EllipticGeometry.nativePatchBiholomorph j (localCover j x)))).compContinuousLinearMap
          (mfderiv I₃ I₃ (globalCover j) x) =
            SectionsUnit.specialCoefficient j x.1.val • volume := by
  rw [Sections.patchSection_inclusion]
  exact sectionAlongInclusion_cover_pullback j x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
