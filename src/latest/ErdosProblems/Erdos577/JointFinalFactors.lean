import ErdosProblems.Erdos577.JointFinalGeometry

/-! All three actual factor completions behind the final local insertion prohibitions. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.old_triple_no_factor {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hja : j ≠ a) :
    ¬LocalFactor G (insert p.leaf ({p.center, d 2, d 3} ∪ j)) :=
  JointFirst.leaf_pair_no_factor hcard hn p h.config.1 h.config.2.2.1 hj hja.symm
    (h.mem 2) (h.mem 3) h.primary

theorem Core.exposed_triple_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a) :
    ¬LocalFactor G (insert (q 3) ({p.center, d 2, d 3} ∪ j)) := by
  intro hf
  obtain ⟨hp, hs, ha, has, hcase, _, _⟩ := h.config
  have hFQ := h.paw_disjoint hs
  obtain ⟨e, _, _, _, hp', _, _, _, hkeep⟩ :=
    JointClaims.exists_exposed_chain hc hcard hn p hp hs q rfl hFQ (Or.inr hcase)
  let p' := JointClaims.exposedPaw p q hFQ (Or.inr hcase)
  have htri : p'.triangle = p.triangle :=
    JointClaims.exposedPaw_triangle p q hFQ (Or.inr hcase)
  have hu : ({p.center, d 2, d 3} : Finset V) ⊆ p'.triangle ∪ a := by
    rw [htri]
    exact insert_subset (mem_union_left _ p.center_mem_triangle)
      (insert_subset (mem_union_right _ (h.mem 2))
        (singleton_subset_iff.mpr (mem_union_right _ (h.mem 3))))
  have hr : QuadOn G ((p'.triangle ∪ a) \ {p.center, d 2, d 3}) := by rw [htri]; exact h.primary
  exact hn (JointCore.hasPacking_of_partial_core hcard p' hp' (hkeep a ha has)
    (hkeep j hj hjq) hja.symm hu hr hf.partition)

theorem Core.mixed_triple_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    {z : V} (hz : z ∈ a)
    (hcore : QuadOn G ((p.triangle ∪ a) \ {z, p.center, p.vertices 2})) :
    ¬LocalFactor G (insert (q 3) (insert p.leaf ({z, p.center} ∪ j))) := by
  intro hf
  obtain ⟨hp, hs, ha, has, hcase, _, _⟩ := h.config
  have hFQ := h.paw_disjoint hs
  have hFA := h.paw_disjoint ha
  have hFJ := h.paw_disjoint hj
  have hAQ := c.property.blocks_disjoint ha hs has
  have hJQ := c.property.blocks_disjoint hj hs hjq
  have hm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hzQ : z ∉ q.support := fun hh ↦ disjoint_left.mp hAQ hz hh
  have hdis : Disjoint (insert p.leaf ({z, p.center} ∪ j)) q.support := by
    refine disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hFQ (hm 0) hh, ?_⟩
    refine disjoint_union_left.mpr ⟨?_, hJQ⟩
    exact disjoint_insert_left.mpr ⟨hzQ,
      disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hFQ (hm 1) hh)⟩
  have hbx : p.vertices 2 ≠ p.leaf := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hbr : p.vertices 2 ≠ p.center := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)
  have hbz : p.vertices 2 ≠ z := fun he ↦ disjoint_left.mp hFA (hm 2) (he.symm ▸ hz)
  have hbout : p.vertices 2 ∉ (insert p.leaf ({z, p.center} ∪ j)) ∪ q.support := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hbx, ⟨hbz, hbr⟩, fun hh ↦ disjoint_left.mp hFJ (hm 2) hh⟩,
      fun hh ↦ disjoint_left.mp hFQ (hm 2) hh⟩
  have hq3 : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hrep := JointClaims.case_two_universal hc p hp hs q rfl hcase (q 3) hq3
  obtain ⟨part⟩ := hf.partition
  let parts := part.replacementUnion hdis hbout hq3 (BlockPartition.single hrep)
  have he : insert (p.vertices 2) ((insert p.leaf ({z, p.center} ∪ j)) ∪ q.support) =
      insert p.leaf ({z, p.center, p.vertices 2} ∪
        ({q.support, j} : Finset (Finset V)).biUnion id) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, insert_union, singleton_union]
    rw [union_comm j q.support, insert_comm (p.vertices 2) p.leaf,
      insert_comm (p.vertices 2) z, insert_comm (p.vertices 2) p.center]
  have hsel : ({q.support, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hs (singleton_subset_iff.mpr hj)
  have hna : a ∉ ({q.support, j} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro has hja.symm
  have hu : ({z, p.center, p.vertices 2} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset (mem_union_right _ hz) (insert_subset (mem_union_left _ p.center_mem_triangle)
      (singleton_subset_iff.mpr (mem_union_left _ (by simp [Paw.triangle]))))
  exact hn (JointFirst.hasPacking_of_selected_core hcard p hp ha {q.support, j}
    hsel hna hu hcore ⟨he ▸ parts⟩)

end Erdos577.JointFinal
