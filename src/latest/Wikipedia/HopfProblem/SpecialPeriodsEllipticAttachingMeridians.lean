import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansComparison
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansParameters
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansHomomorphism
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingGlobalPaths

/-!
# Actual elliptic attaching meridians and the fixed free basis

The actual logarithmic attaching loop, projected through its original
small overlap, is the clockwise circle in the genuine elliptic base
coordinate. Its image in the normalized plane is therefore the actual
analytic chart circle used in the constructed two-stage deformation.

Pulling that deformation back gives a genuine path from its local
basepoint to the fixed common regular basepoint, together with the
oriented peripheral homotopy. Both elliptic loops have the same sign
relative to the fixed jointly free compatible basis. An arbitrary
independently marked attaching tail appears only in the displayed
conjugating loop, and its image cancels in a commuting target group.

Positive sufficiently small parameters are constructed here. The chosen
loop, tail, and homotopy thus have no parameter-existence, loop-comparison,
or endpoint-only homotopy hypothesis.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic TrianglePeriodFamily.Meridians EllipticAttachingMeridians CuspUniformization

variable (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
  (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))

/-- The genuine regular-base path has the complete clockwise analytic
coordinate formula, not merely a specified lifted endpoint. -/
theorem attachingRegularBaseLoop_plane (t : I) :
    (Triangle.triangleRegularPlaneHomeomorph (attachingRegularBaseLoop j s₀ hs₀ hr t) : ℂ) =
      attachingPlaneCoordinate j (exponential s₀ ^ j.order * clockwiseUnit t) := by
  have h := attachingPlaneCoordinate_eq_regularPlane j _
    (attachingRegularBaseLoop j s₀ hs₀ hr t)
    (attachingRegularBaseLoop_compact j s₀ hs₀ hr t)
  rwa [attaching_log_parameter_clockwise] at h

variable (hsmall : ‖exponential s₀‖ ^ j.order < attachingMeridianRadius j)

/-- An actual continuous square from the actual attaching base loop to
the clockwise version of the fixed jointly free compatible meridian. -/
def attachingMeridianSquare :
    LoopSquare (attachingRegularBaseLoop j s₀ hs₀ hr)
      (clockwiseRegularMeridian (attachingMeridianIndex j)) :=
  (attachingPlaneControl j).regularMeridianSquare (attachingMeridianIndex j)
    (attachingPlaneCoordinate_zero_eq_center j) (exponential s₀ ^ j.order)
    (attaching_initial_coordinate_ne_zero j s₀) (attaching_parameters_control_bound j hsmall)
    (attachingRegularBaseLoop j s₀ hs₀ hr) (attachingRegularBaseLoop_plane j s₀ hs₀ hr)

/-- The explicit basepoint trajectory of the two-stage geometric deformation. -/
def attachingMeridianTail :
    Path (triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0))
      (triangleRegularProject normalizedRegularMeridianBasepoint) :=
  (attachingMeridianSquare j s₀ hs₀ hr hsmall).tail

/-- The actual peripheral homotopy, retaining its genuine conjugating path. -/
theorem attachingMeridian_homotopic_conjugate :
    (attachingRegularBaseLoop j s₀ hs₀ hr).Homotopic
      ((attachingMeridianTail j s₀ hs₀ hr hsmall).trans
        ((clockwiseRegularMeridian (attachingMeridianIndex j)).trans
          (attachingMeridianTail j s₀ hs₀ hr hsmall).symm)) :=
  (attachingMeridianSquare j s₀ hs₀ hr hsmall).homotopic_conjugate

/-- The external attaching tail remains exactly as chosen by the actual
upstairs period-column transport; its effect is the displayed conjugator. -/
theorem attachingMeridian_whisker_conjugate
    (τ : Path (triangleRegularProject normalizedRegularMeridianBasepoint)
      (triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0))) :
    (τ.trans ((attachingRegularBaseLoop j s₀ hs₀ hr).trans τ.symm)).Homotopic
      ((τ.trans (attachingMeridianTail j s₀ hs₀ hr hsmall)).trans
        ((clockwiseRegularMeridian (attachingMeridianIndex j)).trans
          (τ.trans (attachingMeridianTail j s₀ hs₀ hr hsmall)).symm)) :=
  (attachingMeridianSquare j s₀ hs₀ hr hsmall).homotopic_whisker_conjugate τ

/-- The exact path-change formula has one common orientation choice
for the original order-three and order-four free generators. -/
theorem attachingMeridian_fundamentalGroup_pathChange :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        (attachingMeridianTail j s₀ hs₀ hr hsmall)
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (attachingRegularBaseLoop j s₀ hs₀ hr))) =
      if normalizationReversesMeridians then
        compatibleRegularMeridianClass (attachingMeridianIndex j)
      else (compatibleRegularMeridianClass (attachingMeridianIndex j))⁻¹ :=
  (attachingMeridianSquare j s₀ hs₀ hr hsmall).fundamentalGroup_pathChange.trans
    (clockwiseRegularMeridian_class (attachingMeridianIndex j))

include hsmall in
/-- In a commuting target, the proven geometric conjugator cancels.
This preserves any separately constructed upstairs attaching tail and
the original jointly free meridian marking. -/
theorem attachingMeridian_map_whisker {G : Type*} [Group G]
    (τ : Path (triangleRegularProject normalizedRegularMeridianBasepoint)
      (triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0)))
    (φ : FundamentalGroup TriangleRegularQuotient
      (triangleRegularProject normalizedRegularMeridianBasepoint) →* G)
    (hcomm : ∀ g h : G, Commute g h) :
    φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (τ.trans ((attachingRegularBaseLoop j s₀ hs₀ hr).trans τ.symm)))) =
      if normalizationReversesMeridians then
        φ (compatibleRegularMeridianClass (attachingMeridianIndex j))
      else (φ (compatibleRegularMeridianClass (attachingMeridianIndex j)))⁻¹ := by
  have h := (attachingMeridianSquare j s₀ hs₀ hr hsmall).map_whisker_eq τ φ hcomm
  rw [clockwiseRegularMeridian_class] at h
  simpa only [apply_ite, map_inv] using h

/-- A genuine logarithmic parameter satisfying both proved small-radius
requirements, chosen from the unconditional existence theorem. -/
def chosenAttachingParameter (j : Kind) : ℂ :=
  (exists_small_attaching_parameters j).choose

theorem chosenAttachingParameter_im_pos (j : Kind) : 0 < (chosenAttachingParameter j).im :=
  (exists_small_attaching_parameters j).choose_spec.1

theorem chosenAttachingParameter_bound (j : Kind) :
    ‖exponential (chosenAttachingParameter j)‖ ^ j.order < attachingMeridianRadius j :=
  (exists_small_attaching_parameters j).choose_spec.2

theorem chosenAttachingParameter_filling_bound (j : Kind) :
    ‖exponential (chosenAttachingParameter j)‖ ^ j.order < specialBaseCover.radius (some j) :=
  attaching_parameters_filling_bound j (chosenAttachingParameter_bound j)

/-- The actual regular-base point beneath the chosen logarithmic
attaching path, in its original upstream marking. -/
def chosenAttachingBasepoint (j : Kind) : TriangleRegularQuotient :=
  triangleRegularProject
    (attachingUpstairsPoint j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j) 0)

def chosenAttachingBaseLoop (j : Kind) :
    Path (chosenAttachingBasepoint j) (chosenAttachingBasepoint j) :=
  attachingRegularBaseLoop j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j)
    (chosenAttachingParameter_filling_bound j)

/-- The actual chosen attaching loop and fixed compatible meridian are
joined by a constructed continuous loop square, with no further input. -/
def chosenAttachingSquare (j : Kind) :
    LoopSquare (chosenAttachingBaseLoop j) (clockwiseRegularMeridian (attachingMeridianIndex j)) :=
  attachingMeridianSquare j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j)
    (chosenAttachingParameter_filling_bound j) (chosenAttachingParameter_bound j)

def chosenAttachingTail (j : Kind) :
    Path (chosenAttachingBasepoint j)
      (triangleRegularProject normalizedRegularMeridianBasepoint) :=
  (chosenAttachingSquare j).tail

/-- The unconditional geometric comparison for the two actual selected
attaching meridians. The original free generators are never reselected. -/
theorem chosenAttachingMeridian_homotopic_conjugate (j : Kind) :
    (chosenAttachingBaseLoop j).Homotopic
      ((chosenAttachingTail j).trans
        ((clockwiseRegularMeridian (attachingMeridianIndex j)).trans
          (chosenAttachingTail j).symm)) :=
  (chosenAttachingSquare j).homotopic_conjugate

theorem chosenAttachingMeridian_fundamentalGroup_pathChange (j : Kind) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (chosenAttachingTail j)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (chosenAttachingBaseLoop j))) =
      if normalizationReversesMeridians then
        compatibleRegularMeridianClass (attachingMeridianIndex j)
      else (compatibleRegularMeridianClass (attachingMeridianIndex j))⁻¹ :=
  attachingMeridian_fundamentalGroup_pathChange j (chosenAttachingParameter j)
    (chosenAttachingParameter_im_pos j) (chosenAttachingParameter_filling_bound j)
    (chosenAttachingParameter_bound j)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
