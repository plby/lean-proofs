import ErdosProblems.Erdos577.AlmostComplete

/-! Two disjoint quadrilaterals using three vertices of a complete seven-set extend to a factor. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem partition_of_two_quads_and_core {core outside used a b : Finset V} {x : V}
    (hcore : G.IsNClique 7 core) (hd : Disjoint core outside) (hx : x ∉ core ∪ outside)
    (hu : used ⊆ core) (hucard : used.card = 3)
    (ha : QuadOn G a) (hb : QuadOn G b) (hab : Disjoint a b)
    (hcover : a ∪ b = insert x (used ∪ outside)) :
    Nonempty (BlockPartition G (insert x (core ∪ outside))) := by
  have hr : QuadOn G (core \ used) := QuadOn.of_clique
    (by rw [card_sdiff_of_subset hu, hcore.card_eq, hucard])
    (hcore.isClique.subset (coe_subset.mpr sdiff_subset))
  have hdr : Disjoint (a ∪ b) (core \ used) := by
    rw [hcover]
    apply disjoint_left.mpr
    intro v hv hvr
    obtain ⟨hvcore, hvnot⟩ := mem_sdiff.mp hvr
    rcases mem_insert.mp hv with hv | hv
    · exact hx (mem_union_left _ (hv ▸ hvcore))
    · rcases mem_union.mp hv with hv | hv
      · exact hvnot hv
      · exact disjoint_left.mp hd hvcore hv
  have he : (a ∪ b) ∪ (core \ used) = insert x (core ∪ outside) := by
    rw [hcover, insert_union, union_right_comm used outside, union_sdiff_of_subset hu]
  exact ⟨he ▸ ((BlockPartition.single ha).union (BlockPartition.single hb) hab).union
    (BlockPartition.single hr) hdr⟩

end Erdos577
