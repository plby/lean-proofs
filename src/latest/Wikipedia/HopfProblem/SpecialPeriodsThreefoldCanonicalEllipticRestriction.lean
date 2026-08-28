import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalElliptic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackLocal

/-!
# Restricting the ambient canonical bundle to the actual elliptic piece

The small elliptic filling is the genuine selected open subset of the
full ambient threefold.  Its inclusion is a local biholomorphism for the
original inherited charts.  In those charts the inclusion has identity
derivative, so restriction of ambient alternating three-covectors is
exactly pullback along its actual manifold derivative.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

local instance restrictionFullManifold (j : Kind) :
    IsManifold IF ω (SpecialFullFilling j) := (specialFullFilling_construction j).2.2.1

local instance restrictionPieceManifold (j : Kind) :
    IsManifold IF ω (SpecialEllipticPiece j) := specialEllipticPiece_isManifold j

/-- The literal inclusion of the small open piece into the full filling. -/
def pieceInclusion (j : Kind) : SpecialEllipticPiece j → SpecialFullFilling j := Subtype.val

@[simp] theorem pieceInclusion_apply (j : Kind) (x : SpecialEllipticPiece j) :
    pieceInclusion j x = x.val := rfl

theorem pieceInclusion_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph IF IF ω (pieceInclusion j) :=
  isLocalDiffeomorph_subtypeVal IF
    (pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
      specialBaseCover j)

theorem pieceInclusion_holomorphic (j : Kind) : ContMDiff IF IF ω (pieceInclusion j) :=
  contMDiff_subtype_val

/-- The inherited chart is the actual ambient chart after subtype inclusion. -/
theorem pieceInclusion_chartAt (j : Kind) (x y : SpecialEllipticPiece j) :
    chartAt Model x.val (pieceInclusion j y) = chartAt Model x y := rfl

/-- A point in an inherited chart lies in its original full-filling chart. -/
theorem pieceInclusion_mem_chart_source (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    x.val ∈ (chartAt Model a.val).source := hx.2

/-- On the actual small-chart target, the inclusion's chart expression is identity. -/
theorem pieceInclusion_chart_expression (j : Kind) (x : SpecialEllipticPiece j)
    {u : Model} (hu : u ∈ (chartAt Model x).target) :
    chartAt Model x.val (pieceInclusion j ((chartAt Model x).symm u)) = u :=
  (chartAt Model x).right_inv hu

theorem pieceInclusion_inCharts_eventuallyEq (j : Kind) (x : SpecialEllipticPiece j) :
    (chartAt Model x.val ∘ pieceInclusion j ∘ (chartAt Model x).symm)
      =ᶠ[𝓝 (chartAt Model x x)] id := by
  filter_upwards [(chartAt Model x).open_target.mem_nhds (mem_chart_target Model x)]
    with u hu
  exact pieceInclusion_chart_expression j x hu

/-- The derivative is calculated from the unchanged native chart expression. -/
theorem pieceInclusion_chart_derivative (j : Kind) (x : SpecialEllipticPiece j) :
    fderiv ℂ (chartAt Model x.val ∘ pieceInclusion j ∘ (chartAt Model x).symm)
      (chartAt Model x x) = ContinuousLinearMap.id ℂ Model := by
  rw [(pieceInclusion_inCharts_eventuallyEq j x).fderiv_eq]
  exact fderiv_id

/-- The same identity derivative holds throughout every inherited chart,
not only at that chart's selected point. -/
theorem pieceInclusion_native_chartDerivative (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    Pullback.chartDerivative (pieceInclusion j) (achart Model a) (achart Model a.val) x =
      ContinuousLinearMap.id ℂ Model := by
  have he : (chartAt Model a.val ∘ pieceInclusion j ∘ (chartAt Model a).symm)
      =ᶠ[𝓝 (chartAt Model a x)] id := by
    filter_upwards [(chartAt Model a).open_target.mem_nhds ((chartAt Model a).map_source hx)]
      with u hu
    exact pieceInclusion_chart_expression j a hu
  exact he.fderiv_eq.trans fderiv_id

theorem pieceInclusion_mfderiv (j : Kind) (x : SpecialEllipticPiece j) :
    mfderiv IF IF (pieceInclusion j) x = ContinuousLinearMap.id ℂ Model := by
  have hf := (pieceInclusion_isLocalDiffeomorph j x).mdifferentiableAt (by simp)
  rw [hf.mfderiv]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ]
  exact pieceInclusion_chart_derivative j x

theorem pieceInclusion_determinant (j : Kind) (x : SpecialEllipticPiece j) :
    LinearMap.det (mfderiv IF IF (pieceInclusion j) x).toLinearMap = 1 := by
  rw [pieceInclusion_mfderiv]
  exact LinearMap.det_id

/-- Restriction of the full ambient canonical bundle to the actual small
open piece, defined by pullback along the genuine inclusion differential. -/
def restriction (j : Kind) (x : SpecialEllipticPiece j) :
    (fullBundle j).Fiber x.val ≃L[ℂ] (bundle j).Fiber x :=
  Pullback.pullbackEquiv (pieceInclusion_isLocalDiffeomorph j) x

/-- The restriction acts on the full intrinsic alternating three-covector
space by the actual manifold derivative, also over the central surface. -/
theorem intrinsic_restriction (j : Kind) (x : SpecialEllipticPiece j)
    (v : (fullBundle j).Fiber x.val) :
    intrinsicEquiv j x (restriction j x v) =
      (fullIntrinsicEquiv j x.val v).compContinuousLinearMap
        (mfderiv IF IF (pieceInclusion j) x) :=
  Pullback.intrinsic_pullbackEquiv (pieceInclusion_isLocalDiffeomorph j) x v

/-- Identity in preferred tangent coordinates follows from the native
inherited-chart derivative, rather than being supplied as restriction data. -/
theorem restriction_preferred_coefficient (j : Kind) (x : SpecialEllipticPiece j)
    (v : (fullBundle j).Fiber x.val) :
    id (α := ℂ) (restriction j x v) = id (α := ℂ) v := by
  exact (Pullback.pullbackLinear_preferred_coefficient (pieceInclusion j) x v).trans
    (by rw [pieceInclusion_determinant, one_mul])

theorem restriction_inCoordinates_preferred (j : Kind) (x : SpecialEllipticPiece j)
    (v : (fullBundle j).Fiber x.val) :
    inCoordinates j (achart Model x) x (restriction j x v) =
      fullInCoordinates j (achart Model x.val) x.val v := by
  change Atlas.inCoordinates (SpecialEllipticPiece j) (achart Model x) x _ =
    Atlas.inCoordinates (SpecialFullFilling j) (achart Model x.val) x.val v
  rw [Atlas.inCoordinates_preferred, Atlas.inCoordinates_preferred]
  exact congrArg coefficientEquiv (restriction_preferred_coefficient j x v)

/-- Restriction has identity coefficient in every corresponding pair of
native ambient and inherited open-piece charts. -/
theorem restriction_inCoordinates_native (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) (v : (fullBundle j).Fiber x.val) :
    inCoordinates j (achart Model a) x (restriction j x v) =
      fullInCoordinates j (achart Model a.val) x.val v := by
  calc
    _ = (fullInCoordinates j (achart Model a.val) x.val v).compContinuousLinearMap
        (Pullback.chartDerivative (pieceInclusion j)
          (achart Model a) (achart Model a.val) x) :=
      Pullback.inCoordinates_pullbackEquiv (pieceInclusion_isLocalDiffeomorph j)
        (achart Model a) (achart Model a.val) hx (pieceInclusion_mem_chart_source j a x hx) v
    _ = _ := by rw [pieceInclusion_native_chartDerivative j a x hx]; rfl

/-- Restriction carries the actual ambient preferred local volume frame
to the preferred local volume frame on the genuine small piece. -/
theorem restriction_preferred_localFrame (j : Kind) (x : SpecialEllipticPiece j) :
    restriction j x
        (fullLocalFrame j x.val ⟨x.val, mem_chart_source Model x.val⟩) =
      localFrame j x ⟨x, mem_chart_source Model x⟩ := by
  apply (coordinateEquiv j (achart Model x) (mem_chart_source Model x)).injective
  exact (restriction_inCoordinates_preferred j x _).trans
    ((fullLocalFrame_inCoordinates j x.val ⟨x.val, mem_chart_source Model x.val⟩).trans
      (localFrame_inCoordinates j x ⟨x, mem_chart_source Model x⟩).symm)

/-- Every actual ambient native local volume frame restricts to the
corresponding native local volume frame of the small open piece. -/
theorem restriction_native_localFrame (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    restriction j x
        (fullLocalFrame j a.val ⟨x.val, pieceInclusion_mem_chart_source j a x hx⟩) =
      localFrame j a ⟨x, hx⟩ := by
  apply (coordinateEquiv j (achart Model a) hx).injective
  exact (restriction_inCoordinates_native j a x hx _).trans
    ((fullLocalFrame_inCoordinates j a.val
      ⟨x.val, pieceInclusion_mem_chart_source j a x hx⟩).trans
        (localFrame_inCoordinates j a ⟨x, hx⟩).symm)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic
