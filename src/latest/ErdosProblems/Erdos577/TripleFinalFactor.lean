import ErdosProblems.Erdos577.TripleFinalSelection

/-! The two final cases give actual four-cycle factors retaining every unselected block. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G}

theorem Configuration.final_factor (h : Configuration c p q) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) {a s : Finset V} (ha : a ∈ c.blocks)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (hs : s ∈ c.blocks)
    (hja : j.support ≠ a) (hsa : s ≠ a) (hsj : s ≠ j.support)
    {u z : V} (hu : u ∈ a) (hz : z = p.leaf ∨ z = u)
    (hrepA : QuadOn G (insert p.leaf (a.erase u)))
    (hrepJ : QuadOn G (insert z (j.support.erase (j 3))))
    (hcommon : CommonReplacement G p.center (p.vertices 3) (j 3) s) : HasPacking G k := by
  have hTsub : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hFJ := h.paw_disjoint_block hj
  have hFS := h.paw_disjoint_block hs
  have hFA := h.paw_disjoint_block ha
  have hTJ := hFJ.mono_left hTsub
  have hTS := hFS.mono_left hTsub
  have hTA := hFA.mono_left hTsub
  have hSJ := c.property.blocks_disjoint hs hj hsj
  have hSA := c.property.blocks_disjoint hs ha hsa
  have hJA := c.property.blocks_disjoint hj ha hja
  have hdisJ : Disjoint (p.triangle ∪ s) j.support := disjoint_union_left.mpr ⟨hTJ, hSJ⟩
  have hdisA : Disjoint ((p.triangle ∪ s) ∪ j.support) a :=
    disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hTA, hSA⟩, hJA⟩
  have hy : j 3 ∉ p.triangle ∪ s := fun hh ↦
    disjoint_left.mp hdisJ hh ((j.mem_support _).mpr ⟨3, rfl⟩)
  have hf := LocalFactor.of_three_path_common p.center (p.vertices 2) (p.vertices 3) (j 3)
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 3)) p.edge12 p.edge23 hTS hy hcommon
  change LocalFactor G (insert (j 3) (p.triangle ∪ s)) at hf
  obtain ⟨base⟩ := hf.partition
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hxA : p.leaf ∉ a := fun hh ↦ disjoint_left.mp hFA hxF hh
  have hxout : p.leaf ∉ (p.triangle ∪ s) ∪ j.support := by
    rintro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact p.leaf_not_mem_triangle hh
      · exact disjoint_left.mp hFS hxF hh
    · exact disjoint_left.mp hFJ hxF hh
  have hzout : z ∉ (p.triangle ∪ s) ∪ j.support := by
    rcases hz with rfl | rfl
    · exact hxout
    · exact fun hh ↦ disjoint_left.mp hdisA hh hu
  let joined : BlockPartition G (insert z ((p.triangle ∪ s) ∪ j.support)) :=
    BlockPartition.replacementUnion hdisJ hzout
    ((j.mem_support _).mpr ⟨3, rfl⟩) base (BlockPartition.single hrepJ)
  have hsel : ({a, j.support, s} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset ha (insert_subset hj (singleton_subset_iff.mpr hs))
  have hselected : c.remainder ∪ ({a, j.support, s} : Finset (Finset V)).biUnion id =
      insert p.leaf p.triangle ∪ (a ∪ (j.support ∪ s)) := by
    rw [← h.paw, p.support_eq]
    simp only [biUnion_insert, singleton_biUnion, id_eq]
  rcases hz with rfl | rfl
  · have hd : Disjoint (insert p.leaf ((p.triangle ∪ s) ∪ j.support)) a :=
      disjoint_insert_left.mpr ⟨hxA, hdisA⟩
    let parts : BlockPartition G (insert p.leaf ((p.triangle ∪ s) ∪ j.support) ∪ a) :=
      joined.union (BlockPartition.single (c.property.blocks_quad a ha)) hd
    have he : insert p.leaf ((p.triangle ∪ s) ∪ j.support) ∪ a =
        c.remainder ∪ ({a, j.support, s} : Finset (Finset V)).biUnion id := by
      rw [hselected]
      simp only [insert_union]
      congr 1
      ac_rfl
    exact c.complementPartition.hasPacking_of_selected_factor hcard {a, j.support, s} hsel
      (he ▸ parts)
  · have hx : p.leaf ∉ ((p.triangle ∪ s) ∪ j.support) ∪ a := by
      simpa only [mem_union, not_or] using And.intro hxout hxA
    let parts : BlockPartition G (insert p.leaf (((p.triangle ∪ s) ∪ j.support) ∪ a)) :=
      BlockPartition.replacementUnion hdisA hx hu joined (BlockPartition.single hrepA)
    have he : insert p.leaf (((p.triangle ∪ s) ∪ j.support) ∪ a) =
        c.remainder ∪ ({a, j.support, s} : Finset (Finset V)).biUnion id := by
      rw [hselected]
      simp only [insert_union]
      congr 1
      ac_rfl
    exact c.complementPartition.hasPacking_of_selected_factor hcard {a, j.support, s} hsel
      (he ▸ parts)

end Erdos577.UniversalTriple
