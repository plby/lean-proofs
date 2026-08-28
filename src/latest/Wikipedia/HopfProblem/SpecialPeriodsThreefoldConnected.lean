import Wikipedia.HopfProblem.SpecialPeriodsThreefold
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreConnected
import Wikipedia.HopfProblem.ThreefoldGluingFibres

/-!
# The actual compact threefold and all its fibres are connected

Connectedness of the four genuine local families transfers through the
full patch identifications to every literal global fibre. The proper
surjective projection over the connected sphere then proves connectedness
of the constructed compact complex threefold, without a topological
description of the total space being assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle FibreTopology

attribute [local instance] triangleCompactifiedChartedSpace chartedSpace

theorem gluingData_localProjection_fibre_isConnected (i : Index)
    (b : specialBaseCover.patch i) :
    IsConnected (gluingData.localProjection i ⁻¹' {b}) :=
  localProjection_fibre_isConnected i b

/-- The literal global fibre is naturally the literal fibre in any
actual local patch containing its base point. -/
def localFibreHomeomorph (i : Index) (b : specialBaseCover.patch i) :
    (localProjection i ⁻¹' {b}) ≃ₜ (projection ⁻¹' {(b : TriangleCompactifiedOrbitSpace)}) :=
  gluingData.fibreHomeomorph i b

@[simp] theorem localFibreHomeomorph_val (i : Index) (b : specialBaseCover.patch i)
    (x : localProjection i ⁻¹' {b}) :
    (localFibreHomeomorph i b x : Space) = inclusion i x := rfl

theorem projection_fibre_isConnected (b : TriangleCompactifiedOrbitSpace) :
    IsConnected (projection ⁻¹' {b}) :=
  gluingData.projection_fibre_isConnected gluingData_localProjection_fibre_isConnected b

theorem projectionSphere_fibre_isConnected (b : RiemannSphere) :
    IsConnected (projectionSphere ⁻¹' {b}) :=
  fibre_isConnected_comp_homeomorph projection triangleSphereUniformization.toHomeomorph b
    (projection_fibre_isConnected (triangleSphereUniformization.symm b))

theorem projection_fibre_connectedSpace (b : TriangleCompactifiedOrbitSpace) :
    ConnectedSpace (projection ⁻¹' {b}) :=
  isConnected_iff_connectedSpace.mp (projection_fibre_isConnected b)

theorem projectionSphere_fibre_connectedSpace (b : RiemannSphere) :
    ConnectedSpace (projectionSphere ⁻¹' {b}) :=
  isConnected_iff_connectedSpace.mp (projectionSphere_fibre_isConnected b)

/-- The actual glued manifold is connected, not merely each local model. -/
theorem space_connected : ConnectedSpace Space :=
  gluingData.connectedSpace gluingData_localProjection_proper
    gluingData_localProjection_fibre_isConnected

/-- The constructed connected compact complex threefold has a proper
surjective holomorphic sphere projection with compact connected fibres.
No identification with the six-sphere is asserted by this theorem. -/
theorem connected_compact_holomorphic_threefold :
    CompactSpace Space ∧ ConnectedSpace Space ∧ T2Space Space ∧
      SecondCountableTopology Space ∧
      IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω Space ∧
      Module.finrank ℂ (ℂ × ComplexPlane₂) = 3 ∧
      IsProperMap projectionSphere ∧ Function.Surjective projectionSphere ∧
      ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω projectionSphere ∧
      ∀ b : RiemannSphere, IsCompact (projectionSphere ⁻¹' {b}) ∧
        IsConnected (projectionSphere ⁻¹' {b}) :=
  ⟨space_compact, space_connected, space_t2Space, space_secondCountable, space_isManifold,
    complex_dimension, projectionSphere_proper, projectionSphere_surjective,
    projectionSphere_holomorphic, fun b =>
      ⟨projectionSphere_fibre_compact b, projectionSphere_fibre_isConnected b⟩⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
