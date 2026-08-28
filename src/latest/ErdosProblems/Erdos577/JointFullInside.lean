import ErdosProblems.Erdos577.JointFullFirstBound

/-! The exact three contributions to the six-row inside budget: thirty-five, seven, and four. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.full_paw_inside {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpattern : FullPattern v p.leaf (q 3) z w) :
    contacts G p.support (p.support ∪ q.support ∪ a ∪ j) ≤ 35 := by
  obtain ⟨hp, hq, ha, haq, hcase, _, _⟩ := h.config
  have hnquad : ¬QuadOn G p.support := by rw [hp]; exact c.no_quad_remainder hcard hn
  have hFF : contacts G p.support p.support = 8 := by
    rw [contacts_self_eq_twice_edgeCount G, p.edgeCount_of_no_quad hnquad]
  have hxQ := degreeIn_le_card G p.leaf q.support
  rw [q.card_support] at hxQ
  have hTQ := JointClaims.triangle_contacts_le_four hc hcard hn p hp hq
    (JointClaims.leaf_lower p q (Or.inr hcase))
  have hFQ : contacts G p.support q.support ≤ 8 := by
    rw [p.contacts_support]
    omega
  have hTA := (h.loss_scores hloss).2.2.1
  have hFA : contacts G p.support a ≤ 10 := by
    rw [p.contacts_support, h.leaf_zero, zero_add]
    exact hTA
  have hFJ : contacts G p.support j ≤ 9 := by
    by_cases hheavy : 9 ≤ contacts G p.support j
    · rcases hc.claim_two_two hcard hdeg hn p hp hj v hv (by rwa [hv]) with hzero | ⟨v', hv', hpat⟩
      · have hxone := hpattern.local_data.1
        omega
      · have heq : contacts G p.support v'.support = 9 := by
          rw [hpat.2.contacts_eq p v' ![1, 15, 9, 3]]
          decide +kernel
        rw [hv', hv] at heq
        exact heq.le
    · omega
  have hFQA : Disjoint (p.support ∪ q.support) a :=
    disjoint_union_left.mpr ⟨h.paw_disjoint ha, c.property.blocks_disjoint hq ha haq.symm⟩
  have hFQAJ : Disjoint (p.support ∪ q.support ∪ a) j :=
    disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨h.paw_disjoint hj, c.property.blocks_disjoint hq hj hjq.symm⟩,
      c.property.blocks_disjoint ha hj hja.symm⟩
  rw [contacts_union_right G _ hFQAJ, contacts_union_right G _ hFQA,
    contacts_union_right G _ (h.paw_disjoint hq)]
  omega

theorem Core.full_exposed_inside {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpattern : FullPattern v p.leaf (q 3) z w) :
    degreeIn G (q 3) (p.support ∪ q.support ∪ a ∪ j) ≤ 7 := by
  obtain ⟨hp, hq, ha, haq, hcase, _, _⟩ := h.config
  have hYQ := degreeIn_le_card G (q 3) (q.support.erase (q 3))
  have hm : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  rw [degreeIn_erase_self G (q 3) hm, card_erase_of_mem hm, q.card_support] at hYQ
  have hYT := JointClaims.triangle_column_le_one hc hcard hn p hp hq
    (JointClaims.leaf_lower p q (Or.inr hcase)) (q 3) hm
  have hYF : degreeIn G (q 3) p.support ≤ 2 := by
    rw [p.support_eq, degreeIn_insert G (q 3) p.leaf p.leaf_not_mem_triangle]
    split_ifs <;> omega
  have hYJ : degreeIn G (q 3) j = 2 := hv ▸ hpattern.local_data.2.1
  have hYA := h.last_zero
  have hFQA : Disjoint (p.support ∪ q.support) a :=
    disjoint_union_left.mpr ⟨h.paw_disjoint ha, c.property.blocks_disjoint hq ha haq.symm⟩
  have hFQAJ : Disjoint (p.support ∪ q.support ∪ a) j :=
    disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨h.paw_disjoint hj, c.property.blocks_disjoint hq hj hjq.symm⟩,
      c.property.blocks_disjoint ha hj hja.symm⟩
  rw [degreeIn_union G _ hFQAJ, degreeIn_union G _ hFQA,
    degreeIn_union G _ (h.paw_disjoint hq)]
  omega

theorem Core.full_last_inside {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hpattern : FullPattern v p.leaf (q 3) z w) :
    degreeIn G (v 3) (p.support ∪ q.support ∪ a ∪ j) ≤ 4 := by
  obtain ⟨_, hq, ha, haq, _, _, _⟩ := h.config
  have htK := (h.full_last_core_unique hc hcard hn hj hjq hja v hv z w hpair hpattern).1
  have htQ := h.full_last_first_degree hc hcard hn hj hjq hja v hv z w hpair hpattern
  have htJ : degreeIn G (v 3) j = 2 := hv ▸ hpattern.local_data.2.2.2.2.2
  have htx : ¬G.Adj (v 3) p.leaf := fun hh ↦
    (by decide : (3 : Fin 4) ≠ 0) ((hpattern.1 3).mp hh.symm)
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hxout : p.leaf ∉ ((p.triangle ∪ a) ∪ q.support) ∪ j := by
    simp only [mem_union, not_or]
    exact ⟨⟨⟨p.leaf_not_mem_triangle,
      fun hh ↦ disjoint_left.mp (h.paw_disjoint ha) hxF hh⟩,
      fun hh ↦ disjoint_left.mp (h.paw_disjoint hq) hxF hh⟩,
      fun hh ↦ disjoint_left.mp (h.paw_disjoint hj) hxF hh⟩
  have hKQ := h.core_disjoint hq haq
  have hKQJ : Disjoint ((p.triangle ∪ a) ∪ q.support) j :=
    disjoint_union_left.mpr ⟨h.core_disjoint hj hja.symm,
      c.property.blocks_disjoint hq hj hjq.symm⟩
  have he : p.support ∪ q.support ∪ a ∪ j =
      insert p.leaf (((p.triangle ∪ a) ∪ q.support) ∪ j) := by
    rw [p.support_eq, insert_union, insert_union, insert_union]
    congr 1
    ac_rfl
  rw [he, degreeIn_insert G _ _ hxout, if_neg htx, zero_add,
    degreeIn_union G _ hKQJ, degreeIn_union G _ hKQ]
  omega

end Erdos577.JointFinal
