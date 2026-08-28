import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsPatches
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticCoordinates

/-!
# Native coordinates for the actual elliptic patch sections

The genuine global canonical section has exactly the same top-covector
coordinates as the full-filling section in the matching native chart.
The comparison uses the actual inclusion derivative, already proved to
be identity in these charts.  The inverse-chart identities retain the
original small-piece, full-filling, and global glued atlases.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  Threefold.chartedSpace

local instance patchSectionCoordinatesGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- In matching native and glued charts, the actual transported section
has exactly the original full-filling top-covector coordinates. -/
theorem sectionAlongInclusion_inCoordinates (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    Threefold.Canonical.inCoordinates (Threefold.Canonical.patchChart (some (some j)) a)
        (EllipticGeometry.inclusion j x) (sectionAlongInclusion j x) =
      Elliptic.fullInCoordinates j (achart Model a.val) x.val (fullSection j x.val) := by
  have hk := Threefold.Canonical.inclusion_mem_patchChart_source (some (some j)) a x hx
  have h := Elliptic.patchPullback_inCoordinates j (achart Model a)
    (Threefold.Canonical.patchChart (some (some j)) a) hx hk (sectionAlongInclusion j x)
  have hd : fderiv ℂ
      ((Threefold.Canonical.patchChart (some (some j)) a).val ∘
        EllipticGeometry.inclusion j ∘ (chartAt Model a).symm) (chartAt Model a x) =
      ContinuousLinearMap.id ℂ Model :=
    Threefold.Canonical.patchChart_inclusion_fderiv (some (some j)) a
      ((chartAt Model a).map_source hx)
  rw [sectionAlongInclusion_pullback] at h
  have hcomp := congrArg (fun A : Model →L[ℂ] Model =>
    (Threefold.Canonical.inCoordinates (Threefold.Canonical.patchChart (some (some j)) a)
      (EllipticGeometry.inclusion j x) (sectionAlongInclusion j x)).compContinuousLinearMap A) hd
  exact (h.trans hcomp).symm.trans (smallSection_inCoordinates j a x hx)

/-- The literal section over the global patch has the same exact native
chart coefficients, under the actual patch biholomorphism. -/
theorem patchSection_inCoordinates (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    Threefold.Canonical.inCoordinates (Threefold.Canonical.patchChart (some (some j)) a)
        (EllipticGeometry.inclusion j x)
        (patchSection j (EllipticGeometry.nativePatchBiholomorph j x)) =
      Elliptic.fullInCoordinates j (achart Model a.val) x.val (fullSection j x.val) := by
  rw [patchSection_inclusion]
  exact sectionAlongInclusion_inCoordinates j a x hx

/-- On the actual inherited chart target, the small-piece inverse chart
is the original full-filling inverse chart after subtype inclusion. -/
theorem smallChart_symm_val (j : Kind) (a : SpecialEllipticPiece j) {u : Model}
    (hu : u ∈ (chartAt Model a).target) :
    ((chartAt Model a).symm u).val = (chartAt Model a.val).symm u := by
  have hx := Elliptic.pieceInclusion_mem_chart_source j a ((chartAt Model a).symm u)
    ((chartAt Model a).map_target hu)
  have hc : chartAt Model a.val ((chartAt Model a).symm u).val = u :=
    Elliptic.pieceInclusion_chart_expression j a hu
  exact ((chartAt Model a.val).left_inv hx).symm.trans
    (congrArg (chartAt Model a.val).symm hc)

/-- The actual glued inverse chart is the native inverse chart followed
by inclusion, as an identity on the entire model space. -/
theorem patchChart_symm_native (j : Kind) (a : SpecialEllipticPiece j) (u : Model) :
    (Threefold.Canonical.patchChart (some (some j)) a).val.symm u =
      EllipticGeometry.inclusion j ((chartAt Model a).symm u) := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections
