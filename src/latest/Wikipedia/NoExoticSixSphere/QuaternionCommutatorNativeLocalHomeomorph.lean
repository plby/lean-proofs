import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativeCharts

/-!
# A local homeomorphism for the actual native seven-sphere map

The source chart, the proved inverse-function chart, and the actual
target chart are composed and restricted to the finite target patch.
On this open neighborhood the forward map is exactly the original
descended sphere map. The global fiber at the marked value is a singleton.
-/

noncomputable section

namespace NoExoticSixSphere.QuaternionCommutatorNativeLocalHomeomorph

open Wikipedia.HomotopyGroupsOfSpheres
open QuaternionicFibration SphereCenteredCoordinates
open QuaternionCommutatorNativeSphere QuaternionCommutatorNativeCharts

local notation "south" => QuaternionCommutatorAntipodal.antipode

def comparison : OpenPartialHomeomorph (Sphere 7) BaseSphere :=
  (nativeChart.trans QuaternionCommutatorLocalRegularity.localHomeomorph).trans
    (chart south).symm

def finitePatch : Set (Sphere 7) := sphereMap ⁻¹' (chart south).source

theorem isOpen_finitePatch : IsOpen finitePatch :=
  (chart south).open_source.preimage sphereMap.continuous

def localModel : OpenPartialHomeomorph (Sphere 7) BaseSphere :=
  comparison.restrOpen finitePatch isOpen_finitePatch

theorem sourcePoint_mem_comparison : sourcePoint ∈ comparison.source := by
  refine ⟨⟨sourcePoint_mem_nativeChart, ?_⟩, ?_⟩
  · change nativeChart sourcePoint ∈ QuaternionCommutatorLocalRegularity.localHomeomorph.source
    rw [nativeChart_sourcePoint]
    exact QuaternionCommutatorLocalRegularity.zero_mem_localHomeomorph_source
  · exact Set.mem_univ _

theorem sourcePoint_mem_localModel : sourcePoint ∈ localModel.source := by
  refine ⟨sourcePoint_mem_comparison, ?_⟩
  change sphereMap sourcePoint ∈ (chart south).source
  rw [sourcePoint_map]
  exact self_mem_chart_source south

theorem localModel_eq_sphereMap : Set.EqOn localModel sphereMap localModel.source := by
  intro x hx
  have hn : x ∈ nativeChart.source := hx.1.1.1
  change (chart south).symm
    (QuaternionCommutatorLocalRegularity.coordinateMap (nativeChart x)) = sphereMap x
  rw [QuaternionCommutatorLocalRegularity.coordinateMap_eq_chart,
    projectionMap_nativeChart x hn]
  exact (chart south).left_inv hx.2

theorem localModel_sourcePoint : localModel sourcePoint = south :=
  (localModel_eq_sphereMap sourcePoint_mem_localModel).trans sourcePoint_map

theorem south_mem_localModel_target : south ∈ localModel.target := by
  have h := localModel.map_source sourcePoint_mem_localModel
  rwa [localModel_sourcePoint] at h

theorem sphereMap_fiber_iff (x : Sphere 7) : sphereMap x = south ↔ x = sourcePoint := by
  constructor
  · intro hx
    obtain ⟨y, hy, hu⟩ := sphereMap_unique_antipodal_fiber
    exact (hu x hx).trans (hu sourcePoint sourcePoint_map).symm
  · rintro rfl
    exact sourcePoint_map

end NoExoticSixSphere.QuaternionCommutatorNativeLocalHomeomorph
