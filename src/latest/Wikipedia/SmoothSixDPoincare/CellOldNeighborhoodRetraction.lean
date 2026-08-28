import Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
import Wikipedia.SmoothSixDPoincare.OuterDiskDeformation
import Wikipedia.SmoothSixDPoincare.ClosedPieceMaps
import Mathlib.Topology.LocalAtTarget

/-!
# Retraction of the actual old-space neighborhood

The old space and the original outer disk form a closed embedded cover of
the open old-space neighborhood. Radial normalization agrees with the
identity on their exact boundary intersection, so the maps glue to a
continuous retraction onto the original old space.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

open MorseHandle

variable {N X : Type*} [NormedAddCommGroup N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

def oldInclusion : C(D.old, D.oldNeighborhood) :=
  ⟨Set.inclusion D.old_subset_neighborhood, continuous_inclusion _⟩

def outerParameterHomeomorph : OuterDisk.Space N ≃ₜ (D.cell ⁻¹' D.oldNeighborhood) :=
  Homeomorph.setCongr (by ext z; exact (D.cell_mem_oldNeighborhood_iff z).symm)

def outerInclusion : C(OuterDisk.Space N, D.oldNeighborhood) :=
  ⟨fun z => ⟨D.cell z.val, (D.cell_mem_oldNeighborhood_iff z.val).mpr z.property⟩,
    (D.cell.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem oldInclusion_closed : IsClosedEmbedding D.oldInclusion :=
  ClosedCover.isClosedEmbedding_codRestrict D.old_closed.isClosedEmbedding_subtypeVal
    (fun x => D.old_subset_neighborhood x.property)

theorem outerInclusion_closed : IsClosedEmbedding D.outerInclusion :=
  (D.oldNeighborhood.restrictPreimage_isClosedEmbedding D.cell_closed).comp
    D.outerParameterHomeomorph.isClosedEmbedding

theorem oldNeighborhood_cover : range D.oldInclusion ∪ range D.outerInclusion = univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨x, hx⟩
  have hcover : x ∈ D.old ∪ range D.cell := by rw [D.cover]; trivial
  rcases hcover with hA | ⟨z, rfl⟩
  · exact Or.inl ⟨⟨x, hA⟩, rfl⟩
  · exact Or.inr ⟨⟨z, (D.cell_mem_oldNeighborhood_iff z).mp hx⟩, rfl⟩

theorem sphere_attaches (u : sphere (0 : N) 1) : D.cell (OuterDisk.sphereDisk u) ∈ D.old :=
  (D.boundary _).mpr (mem_sphere_zero_iff_norm.mp u.property)

/-- The unmodified boundary map of the original cell. -/
def attachingSphere : C(sphere (0 : N) 1, D.old) :=
  ⟨fun u => ⟨D.cell (OuterDisk.sphereDisk u), D.sphere_attaches u⟩,
    (D.cell.continuous.comp OuterDisk.sphereDisk.continuous).subtype_mk _⟩

variable [NormedSpace ℝ N]

theorem retractionMaps_agree (a : D.old) (z : OuterDisk.Space N)
    (haz : D.oldInclusion a = D.outerInclusion z) :
    a = D.attachingSphere (OuterDisk.toSphere z) := by
  have heq : (a : X) = D.cell z.val := congrArg Subtype.val haz
  have hnorm : ‖(z.val : N)‖ = 1 := (D.boundary z.val).mp (heq ▸ a.property)
  have hs : OuterDisk.sphereDisk (OuterDisk.toSphere z) = z.val :=
    congrArg Subtype.val (OuterDisk.fromSphere_toSphere_boundary z hnorm)
  apply Subtype.ext
  change (a : X) = D.cell (OuterDisk.sphereDisk (OuterDisk.toSphere z))
  rw [hs]
  exact heq

def oldRetraction : C(D.oldNeighborhood, D.old) :=
  ClosedCover.mapOfClosedPieces D.oldInclusion D.outerInclusion
    D.oldInclusion_closed D.outerInclusion_closed D.oldNeighborhood_cover
    (ContinuousMap.id D.old) (D.attachingSphere.comp OuterDisk.toSphere) D.retractionMaps_agree

theorem oldRetraction_old (a : D.old) : D.oldRetraction (D.oldInclusion a) = a :=
  ClosedCover.mapOfClosedPieces_left D.oldInclusion D.outerInclusion
    D.oldInclusion_closed D.outerInclusion_closed D.oldNeighborhood_cover
    (ContinuousMap.id D.old) (D.attachingSphere.comp OuterDisk.toSphere) D.retractionMaps_agree a

theorem oldRetraction_outer (z : OuterDisk.Space N) :
    D.oldRetraction (D.outerInclusion z) = D.attachingSphere (OuterDisk.toSphere z) :=
  ClosedCover.mapOfClosedPieces_right D.oldInclusion D.outerInclusion
    D.oldInclusion_closed D.outerInclusion_closed D.oldNeighborhood_cover
    (ContinuousMap.id D.old) (D.attachingSphere.comp OuterDisk.toSphere) D.retractionMaps_agree z

end Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
