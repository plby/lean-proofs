import Wikipedia.HopfProblem.CuspControlledRetractionCollapse
import Wikipedia.HopfProblem.CuspControlledRetractionTransport

/-!
# The prescribed collapse for the original varying cusp twist

Precompose the independent frozen honeycomb collapse with the actual
explicit straightening map. This prescribed map is defined before any
controlled deformation is chosen. The proved straightening preserves the
base and fixes the central fibre, so its conjugation transports a controlled
endpoint exactly to this map.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction CuspPositiveRetraction

/-- The explicit change of twist on the literal punctured closed tube. -/
def puncturedStraightening (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (x : PuncturedClosedTube η) : PuncturedClosedTube η :=
  ⟨closedTubeChangeTwist C (frozen C) η x.1, by
    change time (changeTwist C (frozen C) (x.1 : Space)) ≠ 0
    rw [time_changeTwist]
    exact x.2⟩

@[simp] theorem puncturedStraightening_coe
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ) (x : PuncturedClosedTube η) :
    ((puncturedStraightening C η x).1 : Space) = changeTwist C (frozen C) (x.1 : Space) := rfl

theorem puncturedStraightening_base
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ) (x : PuncturedClosedTube η) :
    time ((puncturedStraightening C η x).1 : Space) = time (x.1 : Space) :=
  time_changeTwist C (frozen C) (x.1 : Space)

/-- The prescribed varying-twist collapse, independent of any homotopy. -/
def straightenedPrescribedCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ) :
    PuncturedClosedTube η → CentralFibre :=
  prescribedCollapse (C 0) η ∘ puncturedStraightening C η

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
variable (hε : 0 < ε) (hε1 : ε < 1)
variable (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
variable (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε) (hηε : η < ε)

include hε hε1 hC hRC hηε in
theorem puncturedStraightening_continuous : Continuous (puncturedStraightening C η) := by
  apply Continuous.subtype_mk
  exact (closedTubeChangeTwist_continuous C (frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hηε).comp continuous_subtype_val

include hε hε1 hC hRC hRD hηε in
theorem straightenedPrescribedCollapse_continuous :
    Continuous (straightenedPrescribedCollapse C η) :=
  (prescribedCollapse_continuous (C 0) hε1
    (CuspPositive.smallDrift_positiveTwist (C 0) hRD) hηε).comp
    (puncturedStraightening_continuous C hε hε1 hC hRC hηε)

/-- No additional central motion is introduced by inverse straightening. -/
theorem straightenedHomotopy_prescribed_endpoint
    (H : C(unitInterval × ClosedTube η, ClosedTube η)) (hη : 0 ≤ η) {ρ : ℝ}
    (hEnd : ∀ x : PuncturedClosedTube η, ‖time (x.1 : Space)‖ = ρ →
      H (1, x.1) = centralIntoClosedTube η hη (prescribedCollapse (C 0) η x))
    (x : PuncturedClosedTube η) (hx : ‖time (x.1 : Space)‖ = ρ) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (1, x.1) =
      centralIntoClosedTube η hη (straightenedPrescribedCollapse C η x) := by
  apply straightenedHomotopy_endpoint_of_eq C hε hε1 hC hRC hRD hηε H hη
    x.1 (straightenedPrescribedCollapse C η x)
  exact hEnd (puncturedStraightening C η x)
    ((congrArg norm (puncturedStraightening_base C η x)).trans hx)

end Wikipedia.HopfProblem.CuspControlledRetraction
