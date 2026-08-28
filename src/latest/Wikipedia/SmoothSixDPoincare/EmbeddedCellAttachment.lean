import Wikipedia.SmoothSixDPoincare.MorseHandleModel
import Wikipedia.SmoothSixDPoincare.SurgeryComplementPieces

/-!
# An open cover of an actual embedded cell attachment

The old space is closed, the attached disk is embedded, and their exact
intersection is the disk boundary. Remove the closed half-radius disk to
obtain a neighborhood of the old space; the complement of the old space is
the open disk. Their intersection has the original annular coordinates.
-/

noncomputable section

open Set Metric Function Topology

namespace Wikipedia.SmoothSixDPoincare

open MorseHandle

/-- A genuine embedded disk attached to a closed old space along exactly its boundary. -/
structure EmbeddedCellAttachment (N X : Type*) [NormedAddCommGroup N] [TopologicalSpace X] where
  old : Set X
  old_closed : IsClosed old
  cell : C(UnitDisk N, X)
  cell_closed : IsClosedEmbedding cell
  cover : old ∪ range cell = univ
  boundary : ∀ z, cell z ∈ old ↔ ‖(z : N)‖ = 1

namespace EmbeddedCellAttachment

variable {N X : Type*} [NormedAddCommGroup N] [TopologicalSpace X]

/-- Construct the presentation on the actual ambient union; the old subspace is not replaced. -/
def ofUnion (A : Set X) (e : C(UnitDisk N, X)) (hA : IsClosed A)
    (he : IsClosedEmbedding e) (hface : ∀ z, e z ∈ A ↔ ‖(z : N)‖ = 1) :
    EmbeddedCellAttachment N ↥(A ∪ range e) where
  old := {x | x.val ∈ A}
  old_closed := hA.preimage continuous_subtype_val
  cell := ⟨fun z => ⟨e z, Or.inr (mem_range_self z)⟩, e.continuous.subtype_mk _⟩
  cell_closed := ClosedCover.isClosedEmbedding_codRestrict he
    (fun z => Or.inr (mem_range_self z))
  cover := by
    apply Set.eq_univ_of_forall
    rintro ⟨x, hx | ⟨z, rfl⟩⟩
    · exact Or.inl hx
    · exact Or.inr ⟨z, rfl⟩
  boundary := hface

variable (D : EmbeddedCellAttachment N X)

def oldNeighborhood : Set X := (D.cell '' {z : UnitDisk N | ‖(z : N)‖ ≤ 1 / 2})ᶜ
def diskPatch : Set X := D.oldᶜ

theorem isOpen_oldNeighborhood : IsOpen D.oldNeighborhood :=
  (D.cell_closed.isClosedMap _
    (isClosed_le continuous_subtype_val.norm continuous_const)).isOpen_compl

theorem isOpen_diskPatch : IsOpen D.diskPatch := D.old_closed.isOpen_compl

theorem cell_mem_oldNeighborhood_iff (z : UnitDisk N) :
    D.cell z ∈ D.oldNeighborhood ↔ 1 / 2 < ‖(z : N)‖ := by
  constructor
  · intro hz
    by_contra! hnorm
    exact hz ⟨z, hnorm, rfl⟩
  · rintro hnorm ⟨w, hw, heq⟩
    have hwz : w = z := D.cell_closed.injective heq
    subst w
    exact (not_le_of_gt hnorm) hw

theorem cell_mem_diskPatch_iff (z : UnitDisk N) :
    D.cell z ∈ D.diskPatch ↔ ‖(z : N)‖ < 1 := by
  change D.cell z ∉ D.old ↔ ‖(z : N)‖ < 1
  rw [D.boundary]
  have hz : ‖(z : N)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
  constructor
  · intro h
    exact lt_of_le_of_ne hz h
  · exact ne_of_lt

theorem old_subset_neighborhood : D.old ⊆ D.oldNeighborhood := by
  rintro x hx ⟨z, hz, rfl⟩
  have heq := (D.boundary z).mp hx
  change ‖(z : N)‖ ≤ 1 / 2 at hz
  linarith

theorem open_cover : D.oldNeighborhood ∪ D.diskPatch = univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ D.old
  · exact Or.inl (D.old_subset_neighborhood hx)
  · exact Or.inr hx

theorem diskPatch_subset_range : D.diskPatch ⊆ range D.cell := by
  intro x hx
  have hcover : x ∈ D.old ∪ range D.cell := by rw [D.cover]; trivial
  exact hcover.resolve_left hx

theorem overlap_subset_range : D.oldNeighborhood ∩ D.diskPatch ⊆ range D.cell :=
  inter_subset_right.trans D.diskPatch_subset_range

/-- The disk patch has the original open-disk coordinates. -/
def diskHomeomorph : {z : UnitDisk N // ‖(z : N)‖ < 1} ≃ₜ D.diskPatch :=
  (Homeomorph.setCongr (by
    ext z
    exact (D.cell_mem_diskPatch_iff z).symm)).trans
      (D.cell_closed.isEmbedding.homeomorphOfSubsetRange D.diskPatch_subset_range)

theorem diskHomeomorph_apply (z : {z : UnitDisk N // ‖(z : N)‖ < 1}) :
    (D.diskHomeomorph z : X) = D.cell z.val := rfl

/-- The overlap has precisely the original annular coordinates, with no quotient changes. -/
def overlapHomeomorph :
    {z : UnitDisk N // 1 / 2 < ‖(z : N)‖ ∧ ‖(z : N)‖ < 1} ≃ₜ
      ↥(D.oldNeighborhood ∩ D.diskPatch) :=
  (Homeomorph.setCongr (by
    ext z
    exact (and_congr (D.cell_mem_oldNeighborhood_iff z) (D.cell_mem_diskPatch_iff z)).symm)).trans
      (D.cell_closed.isEmbedding.homeomorphOfSubsetRange D.overlap_subset_range)

theorem overlapHomeomorph_apply
    (z : {z : UnitDisk N // 1 / 2 < ‖(z : N)‖ ∧ ‖(z : N)‖ < 1}) :
    (D.overlapHomeomorph z : X) = D.cell z.val := rfl

end EmbeddedCellAttachment
end Wikipedia.SmoothSixDPoincare
