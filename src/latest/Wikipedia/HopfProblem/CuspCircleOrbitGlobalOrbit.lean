import Wikipedia.HopfProblem.CuspCircleOrbitLocalCoordinates
import Wikipedia.HopfProblem.ThreefoldCircleActionSemifree
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The original cusp coordinate cover is injective on each local circle orbit

Away from the actual fixed curve, the genuine global circle orbit has no
repeated parameters. Above a fixed point, equivariance puts the connected
local circle orbit in one fibre of the original local homeomorphism. The
orbit is therefore discrete and connected, hence a singleton.

This proves injectivity only on each individual local orbit. It does not
assert that an entire cusp coordinate cover is globally injective.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
namespace Global

open ToricCharts ToricFan
open Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

local notation "E₃" => CoordinateSpace 3
local notation "Circle" => AddCircle (1 : ℝ)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The literal local circle orbit varies continuously in the original circle parameter. -/
theorem coordinateCircleOrbit_continuous (z : Domain) :
    Continuous (fun t : Circle => coordinateAction (DeltaSweep.circleParameter t) z) := by
  apply Continuous.subtype_mk
  have hval : Continuous (fun t : Circle => (DeltaSweep.circleParameter t : ℂ)) :=
    Units.continuous_val.comp DeltaSweep.circleParameter_continuous
  have hinv : Continuous (fun t : Circle => ((DeltaSweep.circleParameter t : ℂ)⁻¹)) := by
    simpa only [Function.comp_def, Units.val_inv_eq_inv_val] using
      Units.continuous_coe_inv.comp DeltaSweep.circleParameter_continuous
  apply continuous_pi
  intro j
  fin_cases j
  · simpa [diagonal_apply] using hinv.mul_const ((z : E₃) 0)
  · simpa [diagonal_apply] using (continuous_const : Continuous (fun _ : Circle => (z : E₃) 1))
  · simpa [diagonal_apply] using hval.mul_const ((z : E₃) 2)

/-- Over the actual fixed curve, the entire original local circle orbit is a singleton. -/
theorem coordinateCircleOrbit_subsingleton_of_fixed (a : Triangle) (z : Domain)
    (hz : globalMap a z ∈ VerticalAction.D₀) :
    (Set.range
      (fun t : Circle => coordinateAction (DeltaSweep.circleParameter t) z)).Subsingleton := by
  let O := Set.range (fun t : Circle => coordinateAction (DeltaSweep.circleParameter t) z)
  have himage : globalMap a '' O ⊆ {globalMap a z} := by
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    change globalMap a (coordinateAction (DeltaSweep.circleParameter t) z) = globalMap a z
    rw [← globalMap_circle_coordinateAction]
    exact (VerticalAction.action_fixed_iff (globalMap a z)).mpr hz
      (DeltaSweep.circleParameter t)
  have hlocal : IsLocalHomeomorphOn (globalMap a) O :=
    (globalMap_isLocalDiffeomorph a).isLocalHomeomorph.isLocalHomeomorphOn
  have hdiscrete : IsDiscrete O :=
    hlocal.isDiscrete_of_image (Set.subsingleton_singleton.anti himage).isDiscrete
  exact (isPreconnected_range (coordinateCircleOrbit_continuous z)).isDiscrete_iff_subsingleton.mp
    hdiscrete

/-- The genuine cusp coordinate cover is injective on every individual local circle orbit. -/
theorem globalMap_injOn_coordinateCircleOrbit (a : Triangle) (z : Domain) :
    Set.InjOn (globalMap a)
      (Set.range (fun t : Circle => coordinateAction (DeltaSweep.circleParameter t) z)) := by
  by_cases hz : globalMap a z ∈ VerticalAction.D₀
  · intro x hx y hy _
    exact coordinateCircleOrbit_subsingleton_of_fixed a z hz hx hy
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
    have hglobal : DeltaSweep.actionMap (s, globalMap a z) =
        DeltaSweep.actionMap (t, globalMap a z) := by
      simpa only [globalMap_circle_coordinateAction] using h
    have hst := CircleActionSemifree.orbitMap_injective (globalMap a z) hz hglobal
    exact congrArg (fun r : Circle => coordinateAction (DeltaSweep.circleParameter r) z) hst

end Global
end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
