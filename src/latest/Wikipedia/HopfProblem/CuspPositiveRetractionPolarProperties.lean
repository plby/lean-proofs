import Wikipedia.HopfProblem.CuspRetractionPolarHomotopy
import Wikipedia.HopfProblem.CuspRetractionHomeomorph

/-!
# Height and fibre-torus properties of the polar-spread homotopy

Polar spreading preserves a positive-part homotopy's nonincrease of the
norm of the cusp parameter.  Its compact-torus equivariance also gives
equivariance for the actual unit-norm complex fibre multipliers used in
the straightening construction.
-/

noncomputable section

open Set Topology
open scoped Matrix ContinuousMap

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricSpace

variable {η : ℝ}
variable (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
variable (hfix : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
  time (q.1 : Space) = 0 → P (s, q) = q)

include hfix in
/-- Norm-height decrease on the positive part gives norm-height decrease
on the entire actual closed tube. -/
theorem polarSpread_norm_time_le
    (hmono : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
      ‖time ((P (s, q)).1 : Space)‖ ≤ ‖time (q.1 : Space)‖)
    (s : unitInterval) (x : ClosedTube η) :
    ‖time (polarSpread P s x : Space)‖ ≤ ‖time (x : Space)‖ := by
  obtain ⟨⟨u, q⟩, rfl⟩ := closedPolarMap_surjective η x
  rw [polarSpread_closedPolarMap P hfix]
  simpa only [closedPolarMap_coe, norm_time_compactTorusAction] using hmono s q

/-- A unit-norm pair of complex fibre multipliers gives an actual
compact-torus element with third phase equal to one. -/
def compactFibrePhase (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) : CompactTorus :=
  ![⟨(u 0 : ℂ), mem_sphere_zero_iff_norm.mpr (hu 0)⟩,
    ⟨(u 1 : ℂ), mem_sphere_zero_iff_norm.mpr (hu 1)⟩, 1]

@[simp] theorem compactTorusUnits_compactFibrePhase
    (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) :
    compactTorusUnits (compactFibrePhase u hu) = fibreMultiplier u := by
  funext i
  apply Units.ext
  fin_cases i <;> simp [compactFibrePhase, fibreMultiplier]

@[simp] theorem closedCompactAction_compactFibrePhase
    (η : ℝ) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    closedCompactAction η (compactFibrePhase u hu) x = closedFibreAction η u x := by
  apply Subtype.ext
  change torusAction (compactTorusUnits (compactFibrePhase u hu)) x =
    torusAction (fibreMultiplier u) x
  rw [compactTorusUnits_compactFibrePhase]

include hfix in
/-- Compact-torus equivariance specializes to the actual unit-norm fibre
action used by the varying-period straightening homeomorphism. -/
theorem polarSpread_fibre_torus_equivariant (s : unitInterval)
    (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    polarSpread P s (closedFibreAction η u x) =
      closedFibreAction η u (polarSpread P s x) := by
  simpa only [closedCompactAction_compactFibrePhase] using
    polarSpread_compactTorus_equivariant P hfix s (compactFibrePhase u hu) x

end Wikipedia.HopfProblem.CuspRetraction
