import ErdosProblems.Erdos577.TwoCoreMatchingGain
import ErdosProblems.Erdos577.FullRowDistinguishedFactor

/-! Complete an actual partial factor with the supplied complementary core quadrilateral. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem partition_with_core_complement {core outside used : Finset V} {x : V}
    (hd : Disjoint core outside) (hx : x ∉ core ∪ outside) (hu : used ⊆ core)
    (hr : QuadOn G (core \ used))
    (hf : Nonempty (BlockPartition G (insert x (used ∪ outside)))) :
    Nonempty (BlockPartition G (insert x (core ∪ outside))) := by
  obtain ⟨parts⟩ := hf
  have hdr : Disjoint (insert x (used ∪ outside)) (core \ used) := by
    apply disjoint_left.mpr
    intro v hv hvr
    obtain ⟨hvcore, hvnot⟩ := mem_sdiff.mp hvr
    rcases mem_insert.mp hv with hv | hv
    · exact hx (mem_union_left _ (hv ▸ hvcore))
    · rcases mem_union.mp hv with hv | hv
      · exact hvnot hv
      · exact disjoint_left.mp hd hvcore hv
  have he : insert x (used ∪ outside) ∪ (core \ used) =
      insert x (core ∪ outside) := by
    rw [insert_union, union_right_comm used outside, union_sdiff_of_subset hu]
  exact ⟨he ▸ parts.union (BlockPartition.single hr) hdr⟩

theorem crossing_partition (q : Quadrilateral G) (x r z₁ z₂ : V)
    (hxr : Disjoint {x, r} q.support) (hz : Disjoint {z₁, z₂} q.support)
    (hdis : Disjoint ({x, r} : Finset V) {z₁, z₂})
    (ha : QuadOn G {x, r, q 0, q 3}) (hb : QuadOn G {z₁, q 1, q 2, z₂}) :
    Nonempty (BlockPartition G (insert x ({z₁, z₂, r} ∪ q.support))) := by
  have hlow : ({q 0, q 3} : Finset V) ⊆ q.support := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact (q.mem_support _).mpr ⟨0, rfl⟩
    · exact (mem_singleton.mp hv) ▸ (q.mem_support _).mpr ⟨3, rfl⟩
  have hmid : ({q 1, q 2} : Finset V) ⊆ q.support := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact (q.mem_support _).mpr ⟨1, rfl⟩
    · exact (mem_singleton.mp hv) ▸ (q.mem_support _).mpr ⟨2, rfl⟩
  have hsplit : Disjoint ({q 0, q 3} : Finset V) {q 1, q 2} := by
    simp only [disjoint_insert_left, disjoint_singleton_left, mem_insert, mem_singleton,
      not_or]
    exact ⟨⟨q.injective.ne (by decide : (0 : Fin 4) ≠ 1),
      q.injective.ne (by decide : (0 : Fin 4) ≠ 2)⟩,
      q.injective.ne (by decide : (3 : Fin 4) ≠ 1),
      q.injective.ne (by decide : (3 : Fin 4) ≠ 2)⟩
  have heA : ({x, r, q 0, q 3} : Finset V) = {x, r} ∪ {q 0, q 3} := by
    ext v
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  have heB : ({z₁, q 1, q 2, z₂} : Finset V) = {z₁, z₂} ∪ {q 1, q 2} := by
    ext v
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  have hab : Disjoint ({x, r, q 0, q 3} : Finset V) {z₁, q 1, q 2, z₂} := by
    rw [heA, heB]
    exact disjoint_union_left.mpr
      ⟨disjoint_union_right.mpr ⟨hdis, hxr.mono_right hmid⟩,
        disjoint_union_right.mpr ⟨hz.symm.mono_left hlow, hsplit⟩⟩
  have he : ({x, r, q 0, q 3} : Finset V) ∪ {z₁, q 1, q 2, z₂} =
      insert x ({z₁, z₂, r} ∪ q.support) := by
    rw [q.support_four]
    ext v
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  exact ⟨he ▸ (BlockPartition.single ha).union (BlockPartition.single hb) hab⟩

variable [Fintype V]

theorem hasPacking_of_core_partial {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b)
    (hr : QuadOn G ((p.triangle ∪ b) \ {z₁, z₂, p.center}))
    (hf : Nonempty (BlockPartition G (insert p.leaf ({z₁, z₂, p.center} ∪ q.support)))) :
    HasPacking G k := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hpB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hBQ : Disjoint b q.support := by
    rw [hq]
    exact c.property.blocks_disjoint hb hs hbs
  have htri : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hcore : Disjoint (p.triangle ∪ b) q.support :=
    disjoint_union_left.mpr ⟨hd.mono_left htri, hBQ⟩
  have hxmem : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hx : p.leaf ∉ (p.triangle ∪ b) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact p.leaf_not_mem_triangle hh
      · exact disjoint_left.mp hpB hxmem hh
    · exact disjoint_left.mp hd hxmem hh
  have hu : ({z₁, z₂, p.center} : Finset V) ⊆ p.triangle ∪ b := by
    apply insert_subset (mem_union_right _ hz₁)
    apply insert_subset (mem_union_right _ hz₂)
    exact singleton_subset_iff.mpr (mem_union_left _ p.center_mem_triangle)
  obtain ⟨parts⟩ := partition_with_core_complement hcore hx hu hr hf
  have hsel : ({b, s} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hb (singleton_subset_iff.mpr hs)
  have he : insert p.leaf ((p.triangle ∪ b) ∪ q.support) =
      c.remainder ∪ ({b, s} : Finset (Finset V)).biUnion id := by
    rw [← insert_union, ← insert_union, ← p.support_eq, hp]
    simp only [biUnion_insert, singleton_biUnion, id_eq, hq, union_assoc]
  exact c.complementPartition.hasPacking_of_selected_factor hcard {b, s} hsel (he ▸ parts)

end Erdos577.TwoCore
