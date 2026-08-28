import ErdosProblems.Erdos577.TripleRemainingCase

/-! The five distinct C rows have inside budget27 and force an eleven-contact outside block. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w u v : V}

lemma CCase.exposed_outside_paw (s : CCase p a w u v) (h : HighCore c p q a w) :
    q 3 ∉ (s.paw h).support := by
  rw [Paw.support_eq, s.paw_triangle]
  change q 3 ∉ insert p.leaf ({p.center, u, v} : Finset V)
  intro hh
  rcases mem_insert.mp hh with hh | hh
  · exact h.leaf_exposed_ne hh.symm
  · exact h.exposed_outside_core (s.core_subset hh)

lemma CCase.five_card (s : CCase p a w u v) (h : HighCore c p q a w) :
    (insert (q 3) (s.paw h).support).card = 5 := by
  rw [card_insert_of_notMem (s.exposed_outside_paw h), (s.paw h).card_support]

lemma CCase.triangle_first_contacts (s : CCase p a w u v) (h : HighCore c p q a w)
    (hno : ¬G.Adj p.center (q 3)) : contacts G {p.center, u, v} q.support = 1 := by
  have hzero (i : Fin 4) (hi : i ≠ 3) : degreeIn G (q i) {p.center, u, v} = 0 := by
    apply (degreeIn_eq_zero_iff _ _).mpr
    intro z hz hadj
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hi (h.center_row i hadj.symm)
    · exact (degreeIn_eq_zero_iff _ _).mp (h.first_zero i hi) _ s.first_mem hadj
    · exact (degreeIn_eq_zero_iff _ _).mp (h.first_zero i hi) _ s.second_mem hadj
  have hrout : p.center ∉ ({u, v} : Finset V) := by
    have he := SimpleGraph.is3Clique_triple_iff.mp s.triangle
    simpa only [mem_insert, mem_singleton, not_or] using And.intro he.1.ne he.2.1.ne
  have hY : degreeIn G (q 3) {p.center, u, v} = 1 := by
    rw [degreeIn_insert G _ _ hrout, if_neg (fun he ↦ hno he.symm),
      zero_add, s.exposed_pair_degree h]
  rw [contacts_comm, Quadrilateral.support, contacts_image_left G univ q q.injective,
    Fin.sum_univ_four, hzero 0 (by decide), hzero 1 (by decide), hzero 2 (by decide), hY]

lemma HighCore.exposed_inside_of_nonadj (h : HighCore c p q a w)
    (hno : ¬G.Adj p.center (q 3)) : degreeIn G (q 3) (p.support ∪ q.support ∪ a) = 4 := by
  have hQ : degreeIn G (q 3) q.support = 3 := by
    rw [degreeIn_clique G h.complete.isClique ((q.mem_support _).mpr ⟨3, rfl⟩), q.card_support]
  have hd : Disjoint (p.support ∪ q.support) a := disjoint_union_left.mpr
    ⟨h.toConfiguration.paw_disjoint_block h.core_block,
      c.property.blocks_disjoint h.block h.core_block h.core_ne.symm⟩
  rw [degreeIn_union G _ hd, degreeIn_union G _ h.toConfiguration.disjoint,
    h.toConfiguration.exposed_paw_degree, if_neg hno, hQ, h.exposed_degree]

lemma CCase.triangle_inside (s : CCase p a w u v) (h : HighCore c p q a w)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (hno : ¬G.Adj p.center (q 3)) :
    contacts G {p.center, u, v} (p.support ∪ q.support ∪ a) ≤ 19 := by
  have hX : degreeIn G p.leaf {p.center, u, v} ≤ 1 := by
    have hsub : ({p.center, u, v} : Finset V).filter (G.Adj p.leaf) ⊆ {p.center} := by
      intro z hz
      obtain ⟨hz, hadj⟩ := mem_filter.mp hz
      exact mem_singleton.mpr ((h.leaf_core_row hcard hn (s.core_subset hz)).mp hadj)
    exact (card_le_card hsub).trans_eq (card_singleton _)
  have hdis : Disjoint ({p.leaf} : Finset V) ((p.triangle ∪ a) ∪ q.support) := by
    apply disjoint_singleton_left.mpr
    rw [mem_union, not_or]
    exact ⟨h.leaf_outside_core, h.toConfiguration.paw_outside 0⟩
  have he : p.support ∪ q.support ∪ a =
      ({p.leaf} : Finset V) ∪ ((p.triangle ∪ a) ∪ q.support) := by
    rw [p.support_eq]
    ext z
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  rw [he, contacts_union_right G _ hdis, contacts_singleton_right,
    contacts_union_right G _ h.core_disjoint_first, s.triangle_first_contacts h hno]
  have hb := s.core_budget
  omega

lemma CCase.five_inside (s : CCase p a w u v) (h : HighCore c p q a w)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    contacts G (insert (q 3) (s.paw h).support) (p.support ∪ q.support ∪ a) ≤ 27 := by
  have hno := s.center_nonadj h hcard hn
  have hY := h.exposed_inside_of_nonadj hno
  have hX := h.leaf_inside_degree hcard hn
  have hT := s.triangle_inside h hcard hn hno
  have hsum := JointCore.contacts_insert_upper (G := G) (q 3) (s.paw h).support
    (p.support ∪ q.support ∪ a)
  rw [(s.paw h).contacts_support, s.paw_triangle] at hsum
  change contacts G (insert (q 3) (s.paw h).support) (p.support ∪ q.support ∪ a) ≤
    degreeIn G (q 3) (p.support ∪ q.support ∪ a) +
      (degreeIn G p.leaf (p.support ∪ q.support ∪ a) +
        contacts G {p.center, u, v} (p.support ∪ q.support ∪ a)) at hsum
  omega

theorem CCase.exists_eleven_outside (s : CCase p a w u v) (h : HighCore c p q a w)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) :
    ∃ j ∈ c.blocks, j ≠ q.support ∧ j ≠ a ∧
      11 ≤ contacts G (insert (q 3) (s.paw h).support) j := by
  have hsel : ({q.support, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.block (singleton_subset_iff.mpr h.core_block)
  have htwo : ({q.support, a} : Finset (Finset V)).card = 2 :=
    card_pair_eq_two_iff.mpr h.core_ne.symm
  have hge := card_le_card hsel
  have hdiff := card_sdiff_of_subset hsel
  have hblocks := c.card_vertices
  have hins : contacts G (insert (q 3) (s.paw h).support)
      (c.remainder ∪ ({q.support, a} : Finset (Finset V)).biUnion id) ≤ 27 := by
    rw [← h.paw]
    simpa only [biUnion_insert, singleton_biUnion, id_eq, union_assoc] using
      s.five_inside h hcard hn
  obtain ⟨j, hj, hnot, hheavy⟩ := c.exists_heavy_outside_selected {q.support, a} hsel
    (insert (q 3) (s.paw h).support) (2 * k) 10 hdeg (by
      rw [s.five_card h]
      omega)
  have hne : j ≠ q.support ∧ j ≠ a := by
    simpa only [mem_insert, mem_singleton, not_or] using hnot
  exact ⟨j, hj, hne.1, hne.2, by omega⟩

end Erdos577.UniversalTriple
