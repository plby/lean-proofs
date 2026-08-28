import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryVarying
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexVarying
import Wikipedia.HopfProblem.CuspControlledRetractionFibre

/-!
# The literal circle cylinder and its controlled endpoint

The compensated complex-level phase coordinates form a jointly
continuous cylinder in the original closed quotient.  A single
retraction prescribed on the whole norm-time sphere has the exact
rotating central endpoint on this cylinder, at every real angle.

The ambient quotient radius is independent of the auxiliary small-drift
radius.  The endpoint calculation is first made in the actual central
toric fibre, before projecting to the original-radius central quotient.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishingCircle

open ToricSpace CuspRetraction CuspControlledRetraction CuspCollapse CuspHoneycomb CuspPositive
open CuspCentralHomology.SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hCε : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRF : SmallDrift (frozen C) ε)
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ < ε) (η : ℝ) (hρη : ρ ≤ η) (hηr : η < r)

/-- The actual varying-twist point in the punctured closed tube, at a
jointly varying real angle and phase-plane coordinate. -/
def phaseCircleToricPoint (p : ℝ × PhasePlane) : PuncturedClosedTube η :=
  toricFibrePunctured η (rotatedLevel ρ p.1) (rotatedLevel_ne_zero ρ p.1 hρ)
    (rotatedLevel_norm_le ρ p.1 hρ.le η hρη)
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hCε hRC hRF p.1 p.2)

@[simp] theorem phaseCircleToricPoint_coe (p : ℝ × PhasePlane) :
    ((phaseCircleToricPoint C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη p).1 : Space) =
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hCε hRC hRF p.1 p.2 : Space) := rfl

/-- The cylinder retains the original complex base coordinate. -/
@[simp] theorem phaseCircleToricPoint_base (p : ℝ × PhasePlane) :
    time ((phaseCircleToricPoint C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη p).1 : Space) =
      rotatedLevel ρ p.1 :=
  (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hCε hRC hRF p.1 p.2).2

/-- Every angle lies on the same norm-time sphere. -/
@[simp] theorem phaseCircleToricPoint_norm_time (p : ℝ × PhasePlane) :
    ‖time ((phaseCircleToricPoint C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη p).1 : Space)‖ =
      ρ := by
  rw [phaseCircleToricPoint_base, norm_rotatedLevel ρ p.1 hρ.le]

/-- Joint continuity uses the genuine inverse straightening, with the
inherited topology of the original punctured tube. -/
theorem phaseCircleToricPoint_continuous :
    Continuous (phaseCircleToricPoint C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact varyingComplexPhaseHomeomorph_joint_continuous C ρ hρ ε hε hε1 hρε hCε hRC hRF

/-- The independent prescribed collapse has the rotating central
formula before any quotient, at every angle of the same cylinder. -/
theorem phaseCircleToricPoint_prescribed (a : ℝ) (p : PhasePlane) :
    straightenedPrescribedCollapse C η
        (phaseCircleToricPoint C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη (a, p)) =
      rotatingCentralPoint (C 0) a p := by
  change prescribedCollapse (C 0) η
    (puncturedStraightening C η
      (toricFibrePunctured η (rotatedLevel ρ a) (rotatedLevel_ne_zero ρ a hρ)
        (rotatedLevel_norm_le ρ a hρ.le η hρη)
        (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hCε hRC hRF a p))) = _
  rw [puncturedStraightening_varyingComplexPhase C ρ hρ ε hε hε1 hρε hCε hRC hRF a η hρη p,
    prescribedCollapse_complexPhase (C 0) ρ hρ ε hε1 hρε
      (smallDrift_positiveTwist (C 0) hRF) a η hρη p]

/-- The jointly continuous actual cylinder inside the original-radius
closed quotient, using its original toric representatives. -/
def phaseCirclePoint : C(ℝ × PhasePlane, ClosedQuotient C r η) where
  toFun p := closedQuotientMap C hηr
    (phaseCircleToricPoint C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη p).1
  continuous_toFun := by
    have hq : Continuous (closedQuotientMap C hηr) := by
      apply Continuous.subtype_mk
      exact (CuspQuotient.quotientMap_continuous C r).comp
        (continuous_subtype_val.subtype_mk _)
    exact hq.comp (continuous_subtype_val.comp
      (phaseCircleToricPoint_continuous C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη))

@[simp] theorem phaseCirclePoint_apply (p : ℝ × PhasePlane) :
    phaseCirclePoint C r ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη hηr p =
      closedQuotientMap C hηr
        (phaseCircleToricPoint C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη p).1 := rfl

@[simp] theorem phaseCirclePoint_base (p : ℝ × PhasePlane) :
    CuspQuotient.projection C r
        (phaseCirclePoint C r ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη hηr p) =
      rotatedLevel ρ p.1 :=
  phaseCircleToricPoint_base C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη p

@[simp] theorem phaseCirclePoint_norm_base (p : ℝ × PhasePlane) :
    ‖CuspQuotient.projection C r
        (phaseCirclePoint C r ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη hηr p)‖ = ρ := by
  rw [phaseCirclePoint_base, norm_rotatedLevel ρ p.1 hρ.le]

variable (R : C(ClosedQuotient C r η, QuotientCentralFibre C r))
    (hEnd : ∀ x : PuncturedClosedTube η, ‖time (x.1 : Space)‖ = ρ →
      R (closedQuotientMap C hηr x.1) =
        centralProject C r hr (straightenedPrescribedCollapse C η x))

include hEnd

/-- One actual norm-sphere-controlled retraction has this exact
endpoint on every angle and every phase-plane point simultaneously. -/
theorem retraction_phaseCirclePoint (a : ℝ) (p : PhasePlane) :
    R (phaseCirclePoint C r ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη hηr (a, p)) =
      centralProject C r hr (rotatingCentralPoint (C 0) a p) := by
  rw [phaseCirclePoint_apply,
    hEnd _ (phaseCircleToricPoint_norm_time C ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη (a, p)),
    phaseCircleToricPoint_prescribed]

/-- The same pointwise endpoint is the previously constructed source
rotation, now in the original-radius central quotient. -/
theorem retraction_phaseCirclePoint_sourceRotation (a : ℝ) (p : PhasePlane) :
    R (phaseCirclePoint C r ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη hηr (a, p)) =
      sourceRotation C r hr a (sourceProjection (C 0) p) := by
  rw [sourceRotation_projection]
  exact retraction_phaseCirclePoint C r hr ε hε hε1 hCε hRC hRF ρ hρ hρε η hρη hηr R hEnd a p

end Wikipedia.HopfProblem.CuspBoundaryTopVanishingCircle
