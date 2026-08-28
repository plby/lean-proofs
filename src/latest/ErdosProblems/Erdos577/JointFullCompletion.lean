import ErdosProblems.Erdos577.JointFullDenseBound

/-! Complete any partition on the four arms and selected outside blocks with the original core. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.arms_no_partition {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a : Finset V} (h : Core c p q d a)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (hnq : q.support ∉ bs) (hna : a ∉ bs) :
    ¬Nonempty (BlockPartition G (arms p q d ∪ bs.biUnion id)) := by
  intro hf
  have he0 : arms p q d ∪ bs.biUnion id =
      insert (q 3) (insert p.leaf ({d 2, d 3} ∪ bs.biUnion id)) := by
    simp only [arms, insert_union, singleton_union]
    rw [insert_comm p.leaf (q 3)]
  rw [he0] at hf
  obtain ⟨hp, hq, ha, haq, hcase, _, _⟩ := h.config
  have hFO : Disjoint p.support (bs.biUnion id) := by
    rw [disjoint_biUnion_right]
    exact fun b hb ↦ h.paw_disjoint (hbs hb)
  have hOQ : Disjoint (bs.biUnion id) q.support := by
    rw [disjoint_biUnion_left]
    intro b hb
    exact c.property.blocks_disjoint (hbs hb) hq (by
      intro he
      change b = q.support at he
      exact hnq (he ▸ hb))
  have hm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hzQ (i : Fin 4) : d i ∉ q.support := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint ha hq haq) (h.mem i) hh
  have hdis : Disjoint (insert p.leaf ({d 2, d 3} ∪ bs.biUnion id)) q.support := by
    refine disjoint_insert_left.mpr
      ⟨fun hh ↦ disjoint_left.mp (h.paw_disjoint hq) (hm 0) hh, ?_⟩
    exact disjoint_union_left.mpr ⟨disjoint_insert_left.mpr
      ⟨hzQ 2, disjoint_singleton_left.mpr (hzQ 3)⟩, hOQ⟩
  have hbz (i : Fin 4) : p.vertices 2 ≠ d i := fun he ↦
    disjoint_left.mp (h.paw_disjoint ha) (hm 2) (he.symm ▸ h.mem i)
  have hbout : p.vertices 2 ∉
      (insert p.leaf ({d 2, d 3} ∪ bs.biUnion id)) ∪ q.support := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0), ⟨hbz 2, hbz 3⟩,
      fun hh ↦ disjoint_left.mp hFO (hm 2) hh⟩,
      fun hh ↦ disjoint_left.mp (h.paw_disjoint hq) (hm 2) hh⟩
  have hq3 : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hrep := JointClaims.case_two_universal hc p hp hq q rfl hcase (q 3) hq3
  obtain ⟨part⟩ := hf
  let parts := part.replacementUnion hdis hbout hq3 (BlockPartition.single hrep)
  have he : insert (p.vertices 2)
      ((insert p.leaf ({d 2, d 3} ∪ bs.biUnion id)) ∪ q.support) =
      insert p.leaf ({d 2, d 3, p.vertices 2} ∪ (insert q.support bs).biUnion id) := by
    simp only [biUnion_insert, id_eq, insert_union, singleton_union]
    rw [union_comm (bs.biUnion id) q.support, insert_comm (p.vertices 2) p.leaf,
      insert_comm (p.vertices 2) (d 2), insert_comm (p.vertices 2) (d 3)]
  have hna' : a ∉ insert q.support bs := by
    simpa only [mem_insert, not_or] using And.intro haq hna
  have hu : ({d 2, d 3, p.vertices 2} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset (mem_union_right _ (h.mem 2)) (insert_subset (mem_union_right _ (h.mem 3))
      (singleton_subset_iff.mpr (mem_union_left _ (by simp [Paw.triangle]))))
  exact hn (JointFirst.hasPacking_of_selected_core hcard p hp ha (insert q.support bs)
    (insert_subset hq hbs) hna' hu h.tertiary ⟨he ▸ parts⟩)

end Erdos577.JointFinal
