import ErdosProblems.Erdos577.JointLossLowPattern

/-! A factor on the four arms and an outside block completes to a factor of the selected core. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.arms_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a) :
    ¬LocalFactor G (arms p q d ∪ j) := by
  intro hf
  have he0 : arms p q d ∪ j = insert (q 3) (insert p.leaf ({d 2, d 3} ∪ j)) := by
    ext u
    simp only [arms, mem_union, mem_insert, mem_singleton]
    tauto
  rw [he0] at hf
  obtain ⟨hp, hs, ha, has, hcase, _, _⟩ := h.config
  have hFQ := h.paw_disjoint hs
  have hFA := h.paw_disjoint ha
  have hFJ := h.paw_disjoint hj
  have hAQ := c.property.blocks_disjoint ha hs has
  have hJQ := c.property.blocks_disjoint hj hs hjq
  have hm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hzQ (i : Fin 4) : d i ∉ q.support := fun hh ↦ disjoint_left.mp hAQ (h.mem i) hh
  have hdis : Disjoint (insert p.leaf ({d 2, d 3} ∪ j)) q.support := by
    refine disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hFQ (hm 0) hh, ?_⟩
    exact disjoint_union_left.mpr ⟨disjoint_insert_left.mpr
      ⟨hzQ 2, disjoint_singleton_left.mpr (hzQ 3)⟩, hJQ⟩
  have hbx : p.vertices 2 ≠ p.leaf := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hbz (i : Fin 4) : p.vertices 2 ≠ d i := fun he ↦
    disjoint_left.mp hFA (hm 2) (he.symm ▸ h.mem i)
  have hbout : p.vertices 2 ∉ (insert p.leaf ({d 2, d 3} ∪ j)) ∪ q.support := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hbx, ⟨hbz 2, hbz 3⟩, fun hh ↦ disjoint_left.mp hFJ (hm 2) hh⟩,
      fun hh ↦ disjoint_left.mp hFQ (hm 2) hh⟩
  have hq3 : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hrep := JointClaims.case_two_universal hc p hp hs q rfl hcase (q 3) hq3
  obtain ⟨part⟩ := hf.partition
  let parts := part.replacementUnion hdis hbout hq3 (BlockPartition.single hrep)
  have he : insert (p.vertices 2) ((insert p.leaf ({d 2, d 3} ∪ j)) ∪ q.support) =
      insert p.leaf ({d 2, d 3, p.vertices 2} ∪
        ({q.support, j} : Finset (Finset V)).biUnion id) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, insert_union, singleton_union]
    rw [union_comm j q.support, insert_comm (p.vertices 2) p.leaf,
      insert_comm (p.vertices 2) (d 2), insert_comm (p.vertices 2) (d 3)]
  have hsel : ({q.support, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hs (singleton_subset_iff.mpr hj)
  have hna : a ∉ ({q.support, j} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro has hja.symm
  have hu : ({d 2, d 3, p.vertices 2} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset (mem_union_right _ (h.mem 2)) (insert_subset (mem_union_right _ (h.mem 3))
      (singleton_subset_iff.mpr (mem_union_left _ (by simp [Paw.triangle]))))
  exact hn (JointFirst.hasPacking_of_selected_core hcard p hp ha {q.support, j}
    hsel hna hu h.tertiary ⟨he ▸ parts⟩)

end Erdos577.JointFinal
