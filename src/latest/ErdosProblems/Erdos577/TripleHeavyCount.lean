import ErdosProblems.Erdos577.TripleHeavyGeometry
import ErdosProblems.Erdos577.JointCoreInside
import ErdosProblems.Erdos577.OutsideSelectedCount

/-! Four actual distinct rows force a nine-contact block outside both selected blocks. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w : V}

lemma HighCore.four_card (h : HighCore c p q a w) {u v : V}
    (hu : u ∈ p.triangle ∪ a) (hv : v ∈ p.triangle ∪ a) (huv : u ≠ v) :
    ({p.leaf, q 3, u, v} : Finset V).card = 4 := by
  have hXY : p.leaf ≠ q 3 := by
    intro he
    have hout : p.leaf ∉ q.support := h.toConfiguration.paw_outside 0
    exact hout (he.symm ▸ (q.mem_support _).mpr ⟨3, rfl⟩)
  exact card_eq_four.mpr ⟨p.leaf, q 3, u, v, hXY,
    (fun he ↦ h.leaf_outside_core (he.symm ▸ hu)),
    (fun he ↦ h.leaf_outside_core (he.symm ▸ hv)),
    (fun he ↦ h.exposed_outside_core (he.symm ▸ hu)),
    (fun he ↦ h.exposed_outside_core (he.symm ▸ hv)), huv, rfl⟩

lemma HighCore.four_contacts (h : HighCore c p q a w) {u v : V}
    (hu : u ∈ p.triangle ∪ a) (hv : v ∈ p.triangle ∪ a) (huv : u ≠ v) (j : Finset V) :
    contacts G {p.leaf, q 3, u, v} j = degreeIn G p.leaf j + degreeIn G (q 3) j +
      degreeIn G u j + degreeIn G v j := by
  have hfour := h.four_card hu hv huv
  obtain ⟨hXY, hXu, hXv, hYu, hYv, _⟩ := JointCore.four_distinct hfour
  simp [contacts, hXY, hXu, hXv, hYu, hYv, huv, Nat.add_assoc]

lemma HighCore.four_inside (h : HighCore c p q a w) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) {u v : V}
    (hu : u ∈ p.triangle ∪ a) (hv : v ∈ p.triangle ∪ a)
    (hur : u ≠ p.center) (hub : u ≠ p.vertices 2)
    (hvr : v ≠ p.center) (hvb : v ≠ p.vertices 2) :
    contacts G {p.leaf, q 3, u, v} (p.support ∪ q.support ∪ a) ≤ 23 := by
  have hX := h.leaf_inside_degree hcard hn
  have hY := h.exposed_inside_degree
  have hu7 := h.core_inside_degree hcard hn hu hur hub
  have hv7 := h.core_inside_degree hcard hn hv hvr hvb
  have h1 := JointCore.contacts_insert_upper (G := G) p.leaf {q 3, u, v}
    (p.support ∪ q.support ∪ a)
  have h2 := JointCore.contacts_insert_upper (G := G) (q 3) {u, v}
    (p.support ∪ q.support ∪ a)
  have h3 := JointCore.contacts_insert_upper (G := G) u {v}
    (p.support ∪ q.support ∪ a)
  simp only [contacts_singleton_left] at h3
  omega

theorem HighCore.exists_nine_outside (h : HighCore c p q a w) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) {u v : V}
    (hu : u ∈ p.triangle ∪ a) (hv : v ∈ p.triangle ∪ a) (huv : u ≠ v)
    (hur : u ≠ p.center) (hub : u ≠ p.vertices 2)
    (hvr : v ≠ p.center) (hvb : v ≠ p.vertices 2) :
    ∃ j ∈ c.blocks, j ≠ q.support ∧ j ≠ a ∧
      9 ≤ contacts G {p.leaf, q 3, u, v} j := by
  have hsel : ({q.support, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.block (singleton_subset_iff.mpr h.core_block)
  have htwo : ({q.support, a} : Finset (Finset V)).card = 2 :=
    card_pair_eq_two_iff.mpr h.core_ne.symm
  have hge := card_le_card hsel
  have hdiff := card_sdiff_of_subset hsel
  have hblocks := c.card_vertices
  have hins : contacts G {p.leaf, q 3, u, v}
      (c.remainder ∪ ({q.support, a} : Finset (Finset V)).biUnion id) ≤ 23 := by
    rw [← h.paw]
    simpa only [biUnion_insert, singleton_biUnion, id_eq, union_assoc] using
      h.four_inside hcard hn hu hv hur hub hvr hvb
  obtain ⟨j, hj, hnot, hheavy⟩ := c.exists_heavy_outside_selected {q.support, a} hsel
    {p.leaf, q 3, u, v} (2 * k) 8 hdeg (by
      rw [h.four_card hu hv huv]
      omega)
  have hne : j ≠ q.support ∧ j ≠ a := by
    simpa only [mem_insert, mem_singleton, not_or] using hnot
  exact ⟨j, hj, hne.1, hne.2, by omega⟩

end Erdos577.UniversalTriple
