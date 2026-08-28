import Wikipedia.HopfProblem.CuspComplementCap
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicProjection
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The genuine frontier of the original compact cusp cap

The original sphere projection is open, including at its central
fibres. The actual cusp chart therefore makes the original cusp
parameter open. Pulling back the interior of a closed complex disk
computes the interior of the actual cap, so its frontier is precisely
the original parameter-norm level in the original threefold.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.CuspComplement.OuterBoundary

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.space_t2Space

/-- The unchanged cusp parameter is open for the original quotient topology. -/
theorem parameter_isOpenMap : IsOpenMap CuspGeometry.parameter := by
  intro U hU
  have hg : IsOpen (Threefold.projectionSphere '' (CuspGeometry.inclusion '' U)) :=
    Threefold.projectionSphere_isOpenMap _ (CuspGeometry.inclusion_openEmbedding.isOpenMap U hU)
  have hs : Threefold.projectionSphere '' (CuspGeometry.inclusion '' U) ⊆
      CuspGeometry.sphereChart.source := by
    rintro _ ⟨_, ⟨q, _, rfl⟩, rfl⟩
    exact CuspGeometry.projectionSphere_inclusion_mem_sphereChart_source q
  have ho : IsOpen (CuspGeometry.sphereChart ''
      (Threefold.projectionSphere '' (CuspGeometry.inclusion '' U))) :=
    CuspGeometry.sphereChart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hg hs
  have he : CuspGeometry.sphereChart ''
      (Threefold.projectionSphere '' (CuspGeometry.inclusion '' U)) =
      CuspGeometry.parameter '' U := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext q
    exact CuspGeometry.sphereChart_projectionSphere_inclusion q
  exact he ▸ ho

/-- The literal local closed cap has exactly the strict parameter sublevel as its interior. -/
theorem interior_localCap : interior localCap = (localOpenCap : Set CuspGeometry.LocalSpace) := by
  have hs : localCap = CuspGeometry.parameter ⁻¹' closedBall (0 : ℂ) capRadius := by
    ext q
    simp only [localCap, mem_ofPred_eq, mem_preimage, mem_closedBall, dist_zero_right]
  rw [hs, ← parameter_isOpenMap.preimage_interior_eq_interior_preimage
    CuspGeometry.parameter_continuous, interior_closedBall (0 : ℂ) (ne_of_gt capRadius_pos)]
  ext q
  simp only [mem_preimage, mem_ball, dist_zero_right]
  rfl

theorem inclusion_preimage_cap : CuspGeometry.inclusion ⁻¹' cap = localCap := by
  ext q
  constructor
  · rintro ⟨p, hp, he⟩
    exact CuspGeometry.inclusion_injective he ▸ hp
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- The ambient threefold interior is computed through its actual open cusp inclusion. -/
theorem inclusion_mem_interior_cap_iff (q : CuspGeometry.LocalSpace) :
    CuspGeometry.inclusion q ∈ interior cap ↔ ‖CuspGeometry.parameter q‖ < capRadius := by
  change q ∈ CuspGeometry.inclusion ⁻¹' interior cap ↔ _
  rw [CuspGeometry.inclusion_openEmbedding.isOpenMap.preimage_interior_eq_interior_preimage
    CuspGeometry.inclusion_continuous, inclusion_preimage_cap, interior_localCap]
  rfl

theorem inclusion_mem_cap_iff (q : CuspGeometry.LocalSpace) :
    CuspGeometry.inclusion q ∈ cap ↔ ‖CuspGeometry.parameter q‖ ≤ capRadius := by
  change q ∈ CuspGeometry.inclusion ⁻¹' cap ↔ _
  rw [inclusion_preimage_cap]
  rfl

/-- The exact outer level criterion is for the original ambient topological frontier. -/
theorem inclusion_mem_frontier_cap_iff (q : CuspGeometry.LocalSpace) :
    CuspGeometry.inclusion q ∈ frontier cap ↔ ‖CuspGeometry.parameter q‖ = capRadius := by
  rw [cap_isCompact.isClosed.frontier_eq]
  change (CuspGeometry.inclusion q ∈ cap ∧ CuspGeometry.inclusion q ∉ interior cap) ↔ _
  rw [inclusion_mem_cap_iff, inclusion_mem_interior_cap_iff]
  exact ⟨fun h => le_antisymm h.1 (not_lt.mp h.2), fun h => ⟨h.le, not_lt.mpr h.ge⟩⟩

/-- The named outer mark is the genuine frontier of the actual compact cusp cap. -/
theorem frontier_cap : frontier cap = outerBoundary := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, _, rfl⟩ := cap_isCompact.isClosed.frontier_subset hx
    exact ⟨q, (inclusion_mem_frontier_cap_iff q).mp hx, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact (inclusion_mem_frontier_cap_iff q).mpr hq

theorem interior_cap : interior cap = (openCap : Set Threefold.Space) := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨q, _, rfl⟩ := interior_subset hx
    exact ⟨q, (inclusion_mem_interior_cap_iff q).mp hx, rfl⟩
  · exact openCap_subset_interior_cap

theorem outerBoundary_isClosed : IsClosed outerBoundary := by
  rw [← frontier_cap]
  exact isClosed_frontier

theorem outerBoundary_isCompact : IsCompact outerBoundary :=
  cap_isCompact.of_isClosed_subset outerBoundary_isClosed outerBoundary_subset_cap

end Wikipedia.HopfProblem.CuspComplement.OuterBoundary
