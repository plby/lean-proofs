import ErdosProblems.Erdos577.TwoCorePathPartition
import ErdosProblems.Erdos577.PathCommonAlternatives

/-! The two path-classification alternatives give explicit factors of the selected vertices. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem triangle_common_false {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {j : Finset V} (hj : j ∈ c.blocks)
    (hcommon : CommonReplacement G p.center (p.vertices 2) p.leaf j) : False := by
  have hd : Disjoint p.support j := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)
  have htrieq : ({p.center, p.vertices 3, p.vertices 2} : Finset V) = p.triangle := by
    ext v
    simp only [Paw.triangle, Paw.center, mem_insert, mem_singleton]
    tauto
  have htri : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hx : p.leaf ∉ ({p.center, p.vertices 3, p.vertices 2} : Finset V) ∪ j := by
    rw [htrieq]
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact p.leaf_not_mem_triangle hh
    · exact (c.presentPaw p hp).terminal_not_mem_block hj hh
  have hdis : Disjoint ({p.center, p.vertices 3, p.vertices 2} : Finset V) j := by
    rw [htrieq]
    exact hd.mono_left htri
  have hf := LocalFactor.of_common_path p.center (p.vertices 3) (p.vertices 2) p.leaf
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2)) p.edge13 p.edge23.symm
    hdis hx hcommon
  rw [htrieq, ← insert_union, ← p.support_eq, hp] at hf
  exact c.no_local_factor hcard hn hj hf

theorem first_common_false {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s j : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (hj : j ∈ c.blocks) (hjb : j ≠ b) (hjs : j ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b)
    (hr : QuadOn G ((p.triangle ∪ b) \ {z₁, z₂, p.center}))
    (hcross : QuadOn G {z₁, q 1, q 2, z₂}) (h0 : G.Adj p.leaf (q 0))
    (hcommon : CommonReplacement G p.leaf (q 3) p.center j) : False := by
  have hF (i : Fin 4) : p.vertices i ∈ p.support :=
    (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hFB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFJ : Disjoint p.support j := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)
  have hBQ : Disjoint b q.support := by
    rw [hq]
    exact c.property.blocks_disjoint hb hs hbs
  have hBJ : Disjoint b j := c.property.blocks_disjoint hb hj hjb.symm
  have hQJ : Disjoint q.support j := by
    rw [hq]
    exact c.property.blocks_disjoint hs hj hjs.symm
  obtain ⟨w, hw, hxw, h3w, hJrep⟩ := hcommon
  have hwQ : w ∉ q.support := fun hh ↦ disjoint_left.mp hQJ hh hw
  have hwB : w ∉ b := fun hh ↦ disjoint_left.mp hBJ hh hw
  have hxQ : p.leaf ∉ q.support := fun hh ↦ disjoint_left.mp hFQ (hF 0) hh
  have hxB : p.leaf ∉ b := fun hh ↦ disjoint_left.mp hFB (hF 0) hh
  have hxrQ : Disjoint ({w, p.leaf} : Finset V) q.support :=
    disjoint_insert_left.mpr ⟨hwQ, disjoint_singleton_left.mpr hxQ⟩
  have hzs : ({z₁, z₂} : Finset V) ⊆ b := insert_subset hz₁ (singleton_subset_iff.mpr hz₂)
  have hxrB : Disjoint ({w, p.leaf} : Finset V) b :=
    disjoint_insert_left.mpr ⟨hwB, disjoint_singleton_left.mpr hxB⟩
  have ha := QuadOn.of_vertices (G := G) (a := w) (b := p.leaf) (c := q 0) (d := q 3)
    (fun he ↦ hwQ (he.symm ▸ (q.mem_support _).mpr ⟨0, rfl⟩))
    (fun he ↦ hxQ (he.symm ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    hxw.symm h0 (q.adjacent 3).symm h3w
  obtain ⟨coreParts⟩ := crossing_partition q w p.leaf z₁ z₂ hxrQ
    (hBQ.mono_left hzs) (hxrB.mono_right hzs) ha hcross
  have hS : ({z₁, z₂, p.leaf} : Finset V) ∪ q.support ⊆
      (p.support ∪ b) ∪ q.support := by
    apply union_subset_union _ subset_rfl
    exact insert_subset (mem_union_right _ hz₁) (insert_subset (mem_union_right _ hz₂)
      (singleton_subset_iff.mpr (mem_union_left _ (hF 0))))
  have hSJ : Disjoint (({z₁, z₂, p.leaf} : Finset V) ∪ q.support) j :=
    (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hFJ, hBJ⟩, hQJ⟩).mono_left hS
  have hrout : p.center ∉ (({z₁, z₂, p.leaf} : Finset V) ∪ q.support) ∪ j := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · simp only [mem_insert, mem_singleton] at hh
        rcases hh with hh | hh | hh
        · exact disjoint_left.mp hFB (show p.center ∈ p.support from hF 1) (hh.symm ▸ hz₁)
        · exact disjoint_left.mp hFB (show p.center ∈ p.support from hF 1) (hh.symm ▸ hz₂)
        · exact p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 0) hh
      · exact disjoint_left.mp hFQ (hF 1) hh
    · exact disjoint_left.mp hFJ (hF 1) hh
  let replaced := BlockPartition.replacementUnion hSJ hrout hw coreParts
    (BlockPartition.single hJrep)
  have hepartial : insert p.center ((({z₁, z₂, p.leaf} : Finset V) ∪ q.support) ∪ j) =
      insert p.leaf ({z₁, z₂, p.center} ∪ (q.support ∪ j)) := by
    ext v
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  have htri : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hcore : Disjoint (p.triangle ∪ b) (q.support ∪ j) :=
    disjoint_union_left.mpr ⟨(disjoint_union_right.mpr ⟨hFQ, hFJ⟩).mono_left htri,
      disjoint_union_right.mpr ⟨hBQ, hBJ⟩⟩
  have hxout : p.leaf ∉ (p.triangle ∪ b) ∪ (q.support ∪ j) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact (mem_union.mp hh).elim p.leaf_not_mem_triangle hxB
    · rcases mem_union.mp hh with hh | hh
      · exact hxQ hh
      · exact disjoint_left.mp hFJ (hF 0) hh
  have hu : ({z₁, z₂, p.center} : Finset V) ⊆ p.triangle ∪ b :=
    insert_subset (mem_union_right _ hz₁) (insert_subset (mem_union_right _ hz₂)
      (singleton_subset_iff.mpr (mem_union_left _ p.center_mem_triangle)))
  obtain ⟨all⟩ := partition_with_core_complement hcore hxout hu hr ⟨hepartial ▸ replaced⟩
  have hsel : ({b, s, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hb (insert_subset hs (singleton_subset_iff.mpr hj))
  have he : insert p.leaf ((p.triangle ∪ b) ∪ (q.support ∪ j)) =
      c.remainder ∪ ({b, s, j} : Finset (Finset V)).biUnion id := by
    rw [← insert_union, ← insert_union, ← p.support_eq, hp]
    simp only [biUnion_insert, singleton_biUnion, id_eq, hq, union_assoc]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {b, s, j} hsel (he ▸ all))

end Erdos577.TwoCore
