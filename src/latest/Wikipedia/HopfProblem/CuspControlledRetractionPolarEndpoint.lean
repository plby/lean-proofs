import Wikipedia.HopfProblem.CuspControlledRetractionPolar
import Wikipedia.HopfProblem.CuspControlledRetractionCollapse

/-!
# The spread endpoint equals the independently prescribed collapse

The prescribed collapse was defined from the actual punctured polar
homeomorphism and normalized honeycomb coordinates, without reference
to a homotopy. The transfer below identifies a controlled positive
homotopy's endpoint with that fixed map on the prescribed norm-time shell.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction CuspPositiveRetraction

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
variable (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
variable (hfix : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
  time (q.1 : Space) = 0 → P (s, q) = q)

/-- The positive endpoint need only be prescribed on the actual punctured
positive shell. The conclusion is an equality in the actual closed tube. -/
theorem polarDeformation_prescribedCollapse_of_puncturedEndpoint (ρ : ℝ) (hη : 0 ≤ η)
    (hEnd : ∀ q : PuncturedPositiveTube η, ‖time (q.1.1 : Space)‖ = ρ →
      P (1, q.1) = positiveCentralInclusion η hη (prescribedPositiveCollapse C₀ η q))
    (x : PuncturedClosedTube η) (hx : ‖time (x.1 : Space)‖ = ρ) :
    polarDeformation P hfix (1, x.1) =
      centralIntoClosedTube η hη (prescribedCollapse C₀ η x) := by
  obtain ⟨⟨φ, q⟩, rfl⟩ := puncturedPolarMap_surjective η x
  have hq : ‖time (q.1.1 : Space)‖ = ρ := by
    simpa only [norm_time_puncturedPolarMap] using hx
  apply Subtype.ext
  change (polarDeformation P hfix (1, closedPolarMap η (φ, q.1)) : Space) =
    (prescribedCollapse C₀ η (puncturedPolarMap η (φ, q)) : Space)
  rw [polarDeformation_closedPolarMap, hEnd q hq, prescribedCollapse_polar]
  rfl

/-- The source's explicit normalized-position endpoint is exactly the
previously defined collapse, for every point of the actual punctured shell. -/
theorem polarDeformation_prescribedCollapse (ρ : ℝ) (hη : 0 ≤ η)
    (hEnd : ∀ q : ClosedPositiveTube η, ‖time (q.1 : Space)‖ = ρ →
      P (1, q) = positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : Space))))
    (x : PuncturedClosedTube η) (hx : ‖time (x.1 : Space)‖ = ρ) :
    polarDeformation P hfix (1, x.1) =
      centralIntoClosedTube η hη (prescribedCollapse C₀ η x) :=
  polarDeformation_prescribedCollapse_of_puncturedEndpoint C₀ P hfix ρ hη
    (fun q hq => hEnd q.1 hq) x hx

theorem polarDeformation_prescribedCollapse_coe (ρ : ℝ) (hη : 0 ≤ η)
    (hEnd : ∀ q : ClosedPositiveTube η, ‖time (q.1 : Space)‖ = ρ →
      P (1, q) = positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : Space))))
    (x : PuncturedClosedTube η) (hx : ‖time (x.1 : Space)‖ = ρ) :
    (polarDeformation P hfix (1, x.1) : Space) = (prescribedCollapse C₀ η x : Space) :=
  congrArg Subtype.val (polarDeformation_prescribedCollapse C₀ P hfix ρ hη hEnd x hx)

/-- The genuine central retraction, not only the homotopy's ambient
endpoint, agrees with the independently prescribed map. -/
theorem polarRetraction_prescribedCollapse
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0)
    (ρ : ℝ) (hη : 0 ≤ η)
    (hEnd : ∀ q : ClosedPositiveTube η, ‖time (q.1 : Space)‖ = ρ →
      P (1, q) = positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : Space))))
    (x : PuncturedClosedTube η) (hx : ‖time (x.1 : Space)‖ = ρ) :
    CuspRetraction.polarRetraction P hfix hone x.1 = prescribedCollapse C₀ η x := by
  apply Subtype.ext
  exact polarDeformation_prescribedCollapse_coe C₀ P hfix ρ hη hEnd x hx

end Wikipedia.HopfProblem.CuspControlledRetraction
