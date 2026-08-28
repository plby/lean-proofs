import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepCentralAction
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepFlat
import Wikipedia.HopfProblem.EllipticHigherHomologyRetractionSpecial
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedPeriods

/-!
# The genuine central finite cover intertwines delta translation

The original finite covering is retained verbatim. Its real-coordinate
version uses the actual period-coordinate homeomorphism. The original
root-and-period formula for vertical flow, at root zero, proves that both
covering maps intertwine the newly restricted central action with literal
delta translation. In particular this fixes its period and positive sign.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open Elliptic EllipticFilling FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

local notation "Circle" => CircleTopology.Circle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The unchanged real period coordinates on the actual special
central complex period torus. -/
def centralPeriodCoordinateHomeomorph (j : Kind) :
    RealTorus₄ ≃ₜ SpecialCentralPeriodTorus j :=
  flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val

@[simp] theorem centralPeriodCoordinateHomeomorph_mkQ (j : Kind) (x : RealCoordinates) :
    centralPeriodCoordinateHomeomorph j (standardLattice.mkQ x) =
      flatProjection (specialLocalData j).centralPeriod.val x := rfl

/-- These native coordinates preserve addition, not just topology. -/
theorem centralPeriodCoordinateHomeomorph_add (j : Kind) (x y : RealTorus₄) :
    centralPeriodCoordinateHomeomorph j (x + y) =
      centralPeriodCoordinateHomeomorph j x + centralPeriodCoordinateHomeomorph j y := by
  obtain ⟨a, rfl⟩ := standardLattice.mkQ_surjective x
  obtain ⟨b, rfl⟩ := standardLattice.mkQ_surjective y
  rw [← map_add, centralPeriodCoordinateHomeomorph_mkQ,
    centralPeriodCoordinateHomeomorph_mkQ, centralPeriodCoordinateHomeomorph_mkQ]
  simp only [flatProjection, map_add]

/-- The original finite cover, preceded only by its actual real period
coordinates. No quotient surface or covering map is replaced. -/
def centralFlatPeriodCover (j : Kind) : C(RealTorus₄, SpecialCentralSurface j) :=
  (specialCentralPeriodCover j).comp
    (centralPeriodCoordinateHomeomorph j : C(RealTorus₄, SpecialCentralPeriodTorus j))

@[simp] theorem centralFlatPeriodCover_apply (j : Kind) (x : RealTorus₄) :
    centralFlatPeriodCover j x =
      specialCentralPeriodCover j (centralPeriodCoordinateHomeomorph j x) := rfl

theorem centralFlatPeriodCover_isCoveringMap (j : Kind) :
    IsCoveringMap (centralFlatPeriodCover j) :=
  (specialCentralPeriodCover_isCoveringMap j).comp_homeomorph
    (centralPeriodCoordinateHomeomorph j)

/-- The finite cover followed by the original full central inclusion
has its literal root-zero and unchanged-flat-coordinate formula. -/
theorem specialCentralInclusion_flatPeriodCover (j : Kind) (y : RealTorus₄) :
    specialCentralInclusion j (centralFlatPeriodCover j y) =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (SpecialPeriods.discZero, y) := by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  change (specialLocalData j).centralFibreInclusion j.twist (mainTwist_admissible j)
    (surfaceProjection j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)
      (flatProjection (specialLocalData j).centralPeriod.val x)) = _
  rw [Equivariant.Data.centralFibreInclusion_surfaceProjection,
    Equivariant.Data.centralInclusion_flatProjection]

/-- The original real vertical flow through the central finite cover
is literal delta translation, including at the multiple-fibre support. -/
theorem specialFlow_flatPeriodCover_real (j : Kind) (t : ℝ) (y : RealTorus₄) :
    VerticalAction.Elliptic.specialFlow j (t : ℂ)
        (EllipticGeometry.pieceCentralInclusion j (centralFlatPeriodCover j y)) =
      EllipticGeometry.pieceCentralInclusion j
        (centralFlatPeriodCover j (deltaCircle (t : Circle) + y)) := by
  have hp : VerticalAction.Period.flow (specialLocalData j).periods (t : ℂ)
      (SpecialPeriods.discZero, y) = (SpecialPeriods.discZero, deltaCircle (t : Circle) + y) := by
    rw [deltaCircle_real_apply]
    simp only [VerticalAction.Period.flow, FiniteActionFixed.Period.inverse_vector_real]
    exact Prod.ext rfl (add_comm _ _)
  apply Subtype.ext
  change VerticalAction.Elliptic.specialFullFlow j (t : ℂ)
    (specialCentralInclusion j (centralFlatPeriodCover j y)) =
      specialCentralInclusion j (centralFlatPeriodCover j (deltaCircle (t : Circle) + y))
  rw [specialCentralInclusion_flatPeriodCover,
    VerticalAction.Elliptic.specialFullFlow_quotient, hp,
    specialCentralInclusion_flatPeriodCover]

/-- The actual native inclusion of the central finite cover into the
threefold intertwines the unchanged real-time flow. -/
theorem actionMap_real_centralFlatPeriodCover (j : Kind) (t : ℝ) (y : RealTorus₄) :
    actionMap ((t : Circle), centralInclusionMap j (centralFlatPeriodCover j y)) =
      centralInclusionMap j (centralFlatPeriodCover j (deltaCircle (t : Circle) + y)) := by
  rw [actionMap_real]
  change VerticalAction.flow (t : ℂ)
    (EllipticGeometry.inclusion j
      (EllipticGeometry.pieceCentralInclusion j (centralFlatPeriodCover j y))) = _
  rw [VerticalAction.flow_elliptic, specialFlow_flatPeriodCover_real]
  rfl

theorem actionMap_centralFlatPeriodCover (j : Kind) (t : Circle) (y : RealTorus₄) :
    actionMap (t, centralInclusionMap j (centralFlatPeriodCover j y)) =
      centralInclusionMap j (centralFlatPeriodCover j (deltaCircle t + y)) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact actionMap_real_centralFlatPeriodCover j s y

/-- The actual finite cover is equivariant for the entire positive
period-one circle action on the original central surface. -/
theorem centralActionMap_flatPeriodCover (j : Kind) (t : Circle) (y : RealTorus₄) :
    centralActionMap j (t, centralFlatPeriodCover j y) =
      centralFlatPeriodCover j (deltaCircle t + y) := by
  apply EllipticGeometry.centralSurfaceInclusion_injective j
  change centralInclusionMap j (centralActionMap j (t, centralFlatPeriodCover j y)) =
    centralInclusionMap j (centralFlatPeriodCover j (deltaCircle t + y))
  rw [centralInclusionMap_actionMap]
  exact actionMap_centralFlatPeriodCover j t y

/-- The positive delta circle in the original complex period torus. -/
def centralPeriodDeltaCircle (j : Kind) : C(Circle, SpecialCentralPeriodTorus j) :=
  (centralPeriodCoordinateHomeomorph j : C(RealTorus₄, SpecialCentralPeriodTorus j)).comp
    deltaCircle

@[simp] theorem centralPeriodDeltaCircle_apply (j : Kind) (t : Circle) :
    centralPeriodDeltaCircle j t = centralPeriodCoordinateHomeomorph j (deltaCircle t) := rfl

/-- The original complex-period finite cover has the same exact
translation formula, without replacing it by the real-coordinate cover. -/
theorem centralActionMap_periodCover (j : Kind) (t : Circle)
    (y : SpecialCentralPeriodTorus j) :
    centralActionMap j (t, specialCentralPeriodCover j y) =
      specialCentralPeriodCover j (centralPeriodDeltaCircle j t + y) := by
  obtain ⟨z, rfl⟩ := (centralPeriodCoordinateHomeomorph j).surjective y
  calc
    _ = centralFlatPeriodCover j (deltaCircle t + z) :=
      centralActionMap_flatPeriodCover j t z
    _ = _ := congrArg (specialCentralPeriodCover j)
      (centralPeriodCoordinateHomeomorph_add j (deltaCircle t) z)

/-- The degree-one class of this actual circle is the positive delta
marking transported by the actual period-coordinate homeomorphism. -/
theorem centralPeriodDeltaCircle_positiveLoop_singularHomology (j : Kind) :
    singularHomologyMap (centralPeriodDeltaCircle j) 1
        (loopHomologyClass CirclePaths.positiveLoop) =
      singularHomologyMap
        (centralPeriodCoordinateHomeomorph j : C(RealTorus₄, SpecialCentralPeriodTorus j)) 1
        (TrianglePeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice) := by
  rw [centralPeriodDeltaCircle, singularHomologyMap_comp, LinearMap.comp_apply,
    deltaCircle_positiveLoop_singularHomology]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
