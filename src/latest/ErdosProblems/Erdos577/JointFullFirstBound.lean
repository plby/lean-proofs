import ErdosProblems.Erdos577.JointFullFirstPartition

/-! The exposed low vertex has at most one contact in the original first block. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.full_last_first_degree {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hpattern : FullPattern v p.leaf (q 3) z w) : degreeIn G (v 3) q.support ≤ 1 := by
  obtain ⟨hp, hq, ha, haq, hcase, _, _⟩ := h.config
  have ht : v 3 ∈ j := hv ▸ (v.mem_support _).mpr ⟨3, rfl⟩
  have hqa := c.property.blocks_disjoint hq ha haq.symm
  have hqj := c.property.blocks_disjoint hq hj hjq.symm
  have haj := c.property.blocks_disjoint ha hj hja.symm
  have hz : z ∈ a := by
    rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.mem 2
    · exact h.mem 3
  have hzout : z ∉ j := fun hh ↦ disjoint_left.mp haj hz hh
  have hfull : ∀ u ∈ j, G.Adj z u := by
    intro u hu
    rw [← hv] at hu
    obtain ⟨i, rfl⟩ := (v.mem_support u).mp hu
    exact hpattern.2.2.1 i
  have hjrep := (c.property.blocks_quad j hj).replace_of_complete hzout hfull ht
  by_contra! hlarge
  have hcommon := FullRow.common_insertion hc p hp hq q rfl
    (JointClaims.first_rows p q (Or.inr hcase)).1 hcase.1 (v 3)
    (fun hh ↦ disjoint_left.mp hqj hh ht) (by omega)
  obtain ⟨parts⟩ := first_common_partition p q a j (h.paw_disjoint hq)
    (h.paw_disjoint ha) (h.paw_disjoint hj) hqa hqj haj (v 3) z ht hz
    hcommon hjrep (h.third_replacement z hz)
  have hsel : ({q.support, a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hq (insert_subset ha (singleton_subset_iff.mpr hj))
  have he : p.support ∪ q.support ∪ a ∪ j =
      c.remainder ∪ ({q.support, a, j} : Finset (Finset V)).biUnion id := by
    rw [← hp]
    simp only [biUnion_insert, singleton_biUnion, id_eq]
    ac_rfl
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {q.support, a, j}
    hsel (he ▸ parts))

end Erdos577.JointFinal
