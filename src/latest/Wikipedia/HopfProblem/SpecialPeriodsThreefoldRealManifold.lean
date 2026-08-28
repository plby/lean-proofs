import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Wikipedia.HopfProblem.ComplexRealManifold

/-!
# The actual underlying smooth real six-manifold

The glued complex atlas itself is real analytic, hence smooth. Its model
has real dimension six. These are properties of the actual constructed
space; they do not identify it with a sphere.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] chartedSpace space_isManifold space_connected

/-- Restrict scalars in the native glued complex atlas. -/
theorem space_isRealAnalyticManifold :
    IsManifold 𝓘(ℝ, ℂ × ComplexPlane₂) ω Space :=
  complexManifold_isRealManifold Space ω

theorem space_isSmoothRealManifold :
    IsManifold 𝓘(ℝ, ℂ × ComplexPlane₂) ∞ Space := by
  let := space_isRealAnalyticManifold
  infer_instance

theorem real_dimension : Module.finrank ℝ (ℂ × ComplexPlane₂) = 6 := by
  simp [ComplexPlane₂, Module.finrank_prod, Module.finrank_pi_fintype]

theorem space_locallyPathConnected : LocallyPathConnectedSpace Space :=
  ChartedSpace.locallyPathConnectedSpace (ℂ × ComplexPlane₂) Space

theorem space_pathConnected : PathConnectedSpace Space := by
  let := space_locallyPathConnected
  exact pathConnectedSpace_iff_connectedSpace.mpr space_connected

/-- The constructed threefold is a compact connected smooth real
six-manifold in its original atlas. -/
theorem compact_connected_smooth_six_manifold :
    CompactSpace Space ∧ ConnectedSpace Space ∧ PathConnectedSpace Space ∧
      T2Space Space ∧ SecondCountableTopology Space ∧
      IsManifold 𝓘(ℝ, ℂ × ComplexPlane₂) ∞ Space ∧
      Module.finrank ℝ (ℂ × ComplexPlane₂) = 6 :=
  ⟨space_compact, space_connected, space_pathConnected, space_t2Space,
    space_secondCountable, space_isSmoothRealManifold, real_dimension⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
