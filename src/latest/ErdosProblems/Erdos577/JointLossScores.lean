import ErdosProblems.Erdos577.JointFinalEqual

/-! Exact edge counts and the two possible source patterns when the primary block loses an edge. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma primary_support_eq (p : Paw G) (d : Quadrilateral G)
    (hd : Disjoint p.support d.support) :
    (p.triangle ∪ d.support) \ {p.center, d 2, d 3} =
      {p.vertices 2, p.vertices 3, d 0, d 1} := by
  have ht : ({p.center, d 2, d 3} : Finset V) = {d 2, d 3, p.center} := by
    ext v
    simp only [mem_insert, mem_singleton]
    tauto
  have hs : d.support \ {d 2, d 3} = {d 0, d 1} := by
    ext v
    constructor
    · intro hv
      obtain ⟨hv, hn⟩ := mem_sdiff.mp hv
      obtain ⟨i, rfl⟩ := (d.mem_support v).mp hv
      fin_cases i
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_singleton_self _)
      · exact False.elim (hn (mem_insert_self _ _))
      · exact False.elim (hn (mem_insert_of_mem (mem_singleton_self _)))
    · intro hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact mem_sdiff.mpr ⟨(d.mem_support _).mpr ⟨0, rfl⟩, by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨d.injective.ne (by decide), d.injective.ne (by decide)⟩⟩
      · exact mem_sdiff.mpr ⟨(d.mem_support _).mpr ⟨1, rfl⟩, by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨d.injective.ne (by decide), d.injective.ne (by decide)⟩⟩
  rw [ht, TwoCore.core_complement_eq p d.support hd (d 2) (d 3)
    ((d.mem_support _).mpr ⟨2, rfl⟩) ((d.mem_support _).mpr ⟨3, rfl⟩), hs]

omit [DecidableRel G.Adj] in
lemma primary_clique_of_rows (p : Paw G) (d : Quadrilateral G)
    (hd : Disjoint p.support d.support)
    (hb0 : G.Adj (p.vertices 2) (d 0)) (hb1 : G.Adj (p.vertices 2) (d 1))
    (hc0 : G.Adj (p.vertices 3) (d 0)) (hc1 : G.Adj (p.vertices 3) (d 1)) :
    G.IsNClique 4 ((p.triangle ∪ d.support) \ {p.center, d 2, d 3}) := by
  rw [primary_support_eq p d hd]
  have ht : G.IsNClique 3 {p.vertices 3, d 0, d 1} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hc0, hc1, d.adjacent 0⟩
  apply ht.insert
  intro v hv
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact p.edge23
  · exact hb0
  · exact hb1

omit [DecidableRel G.Adj] in
lemma other_tag_primary_clique (tag : Fin 8) (p : Paw G) (d : Quadrilateral G)
    (hd : Disjoint p.support d.support) (h : JointCore.RefinedSourcePattern tag p d)
    (htag : tag = 5 ∨ tag = 6 ∨ tag = 7) :
    G.IsNClique 4 ((p.triangle ∪ d.support) \ {p.center, d 2, d 3}) := by
  have hbits : (JointCore.lowerRows tag 2).testBit 0 = true ∧
      (JointCore.lowerRows tag 3).testBit 0 = true ∧
      (JointCore.lowerRows tag 3).testBit 1 = true := by
    rcases htag with rfl | rfl | rfl <;> decide
  have hb1 : G.Adj (p.vertices 2) (d 1) := by
    rcases htag with rfl | rfl | rfl
    · exact (h.2.2.2.2 rfl).1
    · exact (h.1.2.2 2 1 (by decide)).1 (by decide)
    · exact (h.1.2.2 2 1 (by decide)).1 (by decide)
  exact primary_clique_of_rows p d hd ((h.1.2.2 2 0 (by decide)).1 hbits.1) hb1
    ((h.1.2.2 3 0 (by decide)).1 hbits.2.1) ((h.1.2.2 3 1 (by decide)).1 hbits.2.2)

variable [Fintype V]

theorem Core.loss_scores {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    {a : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a) :
    edgeCount G a = 6 ∧ edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) = 5 ∧
      contacts G p.triangle a ≤ 10 ∧ G.IsNClique 4 a := by
  have hlo := h.primary_edges
  have hup := (c.property.blocks_quad a h.config.2.2.1).edgeCount_le_six
  have ha : edgeCount G a = 6 := by omega
  have hD : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) = 5 := by omega
  refine ⟨ha, hD, ?_, clique_of_four_six (c.property.blocks_quad a h.config.2.2.1).card ha⟩
  by_contra hn
  have hcl := h.high (by omega)
  have he := edgeCount_clique hcl.isClique
  rw [hcl.card_eq, hD] at he
  exact (by decide : ¬(5 : ℕ) = Nat.choose 4 2) he

theorem Core.loss_tags {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    {a : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a) :
    ∃ tag : Fin 8, (tag = 1 ∨ tag = 4) ∧ JointCore.RefinedSourcePattern tag p d := by
  obtain ⟨ha, hD, hlow, _⟩ := h.loss_scores hloss
  obtain ⟨tag, hpat⟩ := h.low hlow
  refine ⟨tag, ?_, hpat⟩
  have hnot0 : tag ≠ 0 := by
    intro ht
    subst tag
    have hd1 := hpat.1.1.mpr (by decide)
    have hd2 : ¬G.Adj (d 1) (d 3) := fun hh ↦ by
      have he := hpat.1.2.1.mp hh
      exact (by decide : ¬(JointCore.diagonal 0).val.testBit 1 = true) he
    have he := d.edgeCount_eq
    rw [h.labels, ha, if_pos hd1, if_neg hd2] at he
    omega
  have hnotother : ¬(tag = 5 ∨ tag = 6 ∨ tag = 7) := by
    intro ht
    have hd : Disjoint p.support d.support := by
      rw [h.labels]
      exact h.paw_disjoint h.config.2.2.1
    have hcl := other_tag_primary_clique tag p d hd hpat ht
    rw [h.labels] at hcl
    have he := edgeCount_clique hcl.isClique
    rw [hcl.card_eq, hD] at he
    exact (by decide : ¬(5 : ℕ) = Nat.choose 4 2) he
  have h2 := hpat.2.1
  have h3 := hpat.2.2.1
  fin_cases tag <;> simp_all

end Erdos577.JointFinal
