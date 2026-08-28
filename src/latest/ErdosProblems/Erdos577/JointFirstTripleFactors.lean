import ErdosProblems.Erdos577.JointFirstCompletion
import ErdosProblems.Erdos577.JointFirstCenterPaw

/-! Each possible three-arm factor completes to a spanning quadrilateral packing. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem leaf_pair_no_factor {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {a j : Finset V} (ha : a ∈ c.blocks) (hj : j ∈ c.blocks) (haj : a ≠ j)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a)
    (hr : QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2})) :
    ¬LocalFactor G (insert p.leaf ({p.center, z1, z2} ∪ j)) := by
  intro hf
  have hu : ({p.center, z1, z2} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset (mem_union_left _ p.center_mem_triangle)
      (insert_subset (mem_union_right _ h1) (singleton_subset_iff.mpr (mem_union_right _ h2)))
  exact hn (JointCore.hasPacking_of_partial_core hcard p hp ha hj haj hu hr hf.partition)

variable [DecidableRel G.Adj]

theorem center_pair_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a j : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hj : j ∈ c.blocks)
    (has : a ≠ s) (hjs : j ≠ s) (haj : a ≠ j)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a)
    (hr : QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2})) :
    ¬LocalFactor G (insert (q 1) ({p.center, z1, z2} ∪ j)) := by
  intro hf
  obtain ⟨d, _, ht, hT, _, _, _, hkeep⟩ :=
    exists_center_terminal hc hcard hn p hp hs q hq hcase
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  let p' := centerPaw p q hd hcase.2.1
  have hp' : p'.support = d.remainder := by
    change (centerPaw p q hd hcase.2.1).support = insert d.terminal d.triangle
    rw [centerPaw_support, ht, hT]
  have htriangle : p'.triangle = p.triangle := centerPaw_triangle p q hd hcase.2.1
  have hleaf : p'.leaf = q 1 := centerPaw_leaf p q hd hcase.2.1
  have hu : ({p.center, z1, z2} : Finset V) ⊆ p'.triangle ∪ a := by
    rw [htriangle]
    exact insert_subset (mem_union_left _ p.center_mem_triangle)
      (insert_subset (mem_union_right _ h1) (singleton_subset_iff.mpr (mem_union_right _ h2)))
  have hr' : QuadOn G ((p'.triangle ∪ a) \ {p.center, z1, z2}) := by
    rwa [htriangle]
  have hf' : LocalFactor G (insert p'.leaf ({p.center, z1, z2} ∪ j)) := by rwa [hleaf]
  exact hn (JointCore.hasPacking_of_partial_core hcard p' hp'
    (hkeep a ha has) (hkeep j hj hjs) haj hu hr' hf'.partition)

theorem two_leaves_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a j : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hj : j ∈ c.blocks)
    (has : a ≠ s) (hjs : j ≠ s) (haj : a ≠ j)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    {z : V} (hz : z ∈ a)
    (hr : QuadOn G ((p.triangle ∪ a) \ {z, p.center, p.vertices 2})) :
    ¬LocalFactor G (insert p.leaf ({q 1, z, p.center} ∪ j)) := by
  intro hf
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hFJ : Disjoint p.support j := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)
  have hAQ : Disjoint a q.support := by rw [hq]; exact c.property.blocks_disjoint ha hs has
  have hJQ : Disjoint j q.support := by rw [hq]; exact c.property.blocks_disjoint hj hs hjs
  have hxF : p.leaf ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩
  have hrF : p.center ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
  have hbF : p.vertices 2 ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩
  have hzQ : z ∉ q.support := fun hh ↦ disjoint_left.mp hAQ hz hh
  have hd : Disjoint (insert p.leaf ({z, p.center} ∪ j)) q.support := by
    refine disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hFQ hxF hh, ?_⟩
    refine disjoint_union_left.mpr ⟨?_, hJQ⟩
    exact disjoint_insert_left.mpr ⟨hzQ,
      disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hFQ hrF hh)⟩
  have hbx : p.vertices 2 ≠ p.leaf := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hbr : p.vertices 2 ≠ p.center := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)
  have hbz : p.vertices 2 ≠ z := fun he ↦ disjoint_left.mp hFA hbF (he.symm ▸ hz)
  have hbout : p.vertices 2 ∉ (insert p.leaf ({z, p.center} ∪ j)) ∪ q.support := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hbx, ⟨hbz, hbr⟩, fun hh ↦ disjoint_left.mp hFJ hbF hh⟩,
      fun hh ↦ disjoint_left.mp hFQ hbF hh⟩
  have hpart : Nonempty (BlockPartition G (insert (q 1) (insert p.leaf ({z, p.center} ∪ j)))) := by
    have he : insert p.leaf ({q 1, z, p.center} ∪ j) =
        insert (q 1) (insert p.leaf ({z, p.center} ∪ j)) := by
      rw [insert_union, insert_comm p.leaf (q 1)]
    exact he ▸ hf.partition
  obtain ⟨part⟩ := hpart
  have hrep := first_noncentral_replacement hc hcard hn p hp hs q hq hcase
  rw [← hq] at hrep
  let parts := part.replacementUnion hd hbout ((q.mem_support _).mpr ⟨1, rfl⟩)
    (BlockPartition.single hrep)
  have he : insert (p.vertices 2) ((insert p.leaf ({z, p.center} ∪ j)) ∪ q.support) =
      insert p.leaf ({z, p.center, p.vertices 2} ∪ ({s, j} : Finset (Finset V)).biUnion id) := by
    rw [← hq]
    simp only [biUnion_insert, singleton_biUnion, id_eq, insert_union, singleton_union]
    rw [union_comm j q.support, insert_comm (p.vertices 2) p.leaf,
      insert_comm (p.vertices 2) z, insert_comm (p.vertices 2) p.center]
  have hf' : Nonempty (BlockPartition G
      (insert p.leaf ({z, p.center, p.vertices 2} ∪ ({s, j} : Finset (Finset V)).biUnion id))) :=
    ⟨he ▸ parts⟩
  have hbs : ({s, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hs (singleton_subset_iff.mpr hj)
  have hna : a ∉ ({s, j} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro has haj
  have hu : ({z, p.center, p.vertices 2} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset (mem_union_right _ hz) (insert_subset (mem_union_left _ p.center_mem_triangle)
      (singleton_subset_iff.mpr (mem_union_left _ (by simp [Paw.triangle]))))
  exact hn (hasPacking_of_selected_core hcard p hp ha {s, j} hbs hna hu hr hf')

end Erdos577.JointFirst
