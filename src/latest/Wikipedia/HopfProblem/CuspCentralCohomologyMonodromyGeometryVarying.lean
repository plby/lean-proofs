import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryPhase
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexVarying

/-!
# Joint circle transport for the actual varying cusp correction

The inverse of the genuine change-of-twist map carries the compensated
circle family to the original varying quotient.  Continuity is joint in
the angle and the source point, with values in the unchanged ambient
quotient tube.  A full positive turn is the literal source shear.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspPositive CuspCollapse CuspHoneycomb
open CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε)

/-- The genuine inverse straightening is continuous simultaneously in
the real base angle and the phase-plane point. -/
theorem varyingComplexPhaseHomeomorph_joint_continuous :
    Continuous (fun p : ℝ × PhasePlane =>
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p.1 p.2 : Space)) := by
  simp only [varyingComplexPhaseHomeomorph_coe]
  apply (changeTwist_continuousOn (frozen C) C hε hε1
    (fun _ _ => continuousOn_const) (fun i j => (hC i j).continuousOn) rfl hRD).comp_continuous
    (complexPhaseHomeomorph_joint_continuous (C 0) ρ hρ ε hε1 hρε
      (smallDrift_positiveTwist (C 0) hRD))
  intro p
  change time (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
    (smallDrift_positiveTwist (C 0) hRD) p.1 p.2 : Space) ∈ Metric.ball 0 ε
  rw [(complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
    (smallDrift_positiveTwist (C 0) hRD) p.1 p.2).2]
  simpa only [Metric.mem_ball, dist_zero_right] using
    rotatedLevel_norm_lt ρ p.1 hρ.le ε hρε

/-- Inverse straightening retains the exact positive-turn endpoint,
as equality in the original toric space. -/
theorem varyingComplexPhaseHomeomorph_add_one_coe (r : ℝ) (p : PhasePlane) :
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD (r + 1) p : Space) =
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
        (phasePlaneShear p) : Space) := by
  rw [varyingComplexPhaseHomeomorph_coe, varyingComplexPhaseHomeomorph_coe,
    complexPhaseHomeomorph_add_one_coe]

/-- The full circle family lies in the original toric tube. -/
def varyingCircleToricFamily (p : ℝ × PhasePlane) : Tube (disc ε) :=
  ⟨varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p.1 p.2, by
    change time (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
      p.1 p.2 : Space) ∈ Metric.ball 0 ε
    rw [(varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p.1 p.2).2]
    simpa only [Metric.mem_ball, dist_zero_right] using
      rotatedLevel_norm_lt ρ p.1 hρ.le ε hρε⟩

theorem varyingCircleToricFamily_continuous :
    Continuous (varyingCircleToricFamily C ρ hρ ε hε hε1 hρε hC hRC hRD) :=
  (varyingComplexPhaseHomeomorph_joint_continuous C ρ hρ ε hε hε1 hρε hC hRC hRD).subtype_mk _

/-- The existing actual slice homeomorphisms, regarded jointly as points
of the original varying quotient rather than separate fibre types. -/
def varyingCircleFamily (p : ℝ × SourceModel (C 0)) : QuotientSpace C ε :=
  varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p.1 p.2

@[simp] theorem varyingCircleFamily_sourceProjection (r : ℝ) (p : PhasePlane) :
    varyingCircleFamily C ρ hρ ε hε hε1 hρε hC hRC hRD (r, sourceProjection (C 0) p) =
      quotientMap C ε (varyingCircleToricFamily C ρ hρ ε hε hε1 hρε hC hRC hRD (r, p)) := by
  unfold varyingCircleFamily
  rw [varyingComplexSourceHomeomorph_projection]
  rfl

/-- Joint continuity descends through the fixed source quotient; no
choice of fibrewise representatives enters the family. -/
theorem varyingCircleFamily_continuous :
    Continuous (varyingCircleFamily C ρ hρ ε hε hε1 hρε hC hRC hRD) := by
  apply (sourceProjection_isQuotientMap (C 0)).continuous_lift_prod_right
  simpa only [Function.comp_def, varyingCircleFamily_sourceProjection] using
    (quotientMap_continuous C ε).comp
      (varyingCircleToricFamily_continuous C ρ hρ ε hε hε1 hρε hC hRC hRD)

/-- The original base coordinate makes a positive circle of radius `ρ`. -/
@[simp] theorem varyingCircleFamily_base (r : ℝ) (q : SourceModel (C 0)) :
    projection C ε (varyingCircleFamily C ρ hρ ε hε hε1 hρε hC hRC hRD (r, q)) =
      rotatedLevel ρ r :=
  (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r q).2

/-- One positive base turn gives exactly the original source shear,
after descending the actual varying-twist family. -/
theorem varyingCircleFamily_add_one (r : ℝ) (q : SourceModel (C 0)) :
    varyingCircleFamily C ρ hρ ε hε hε1 hρε hC hRC hRD (r + 1, q) =
      varyingCircleFamily C ρ hρ ε hε hε1 hρε hC hRC hRD (r, sourceShear (C 0) q) := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [sourceShear_projection, varyingCircleFamily_sourceProjection,
    varyingCircleFamily_sourceProjection]
  apply congrArg (quotientMap C ε)
  apply Subtype.ext
  exact varyingComplexPhaseHomeomorph_add_one_coe C ρ hρ ε hε hε1 hρε hC hRC hRD r p

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
