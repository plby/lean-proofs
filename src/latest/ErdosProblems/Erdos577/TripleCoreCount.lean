import ErdosProblems.Erdos577.TripleCoreRows
import ErdosProblems.Erdos577.OutsideCoreCount

/-! The exact five-row inside count and an actual heavy block outside the triple core. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G}

lemma Configuration.five_card (h : Configuration c p q) :
    (insert (q 3) p.support).card = 5 := by
  rw [card_insert_of_notMem (h.quad_outside 3), p.card_support]

lemma Configuration.paw_block_contacts (h : Configuration c p q) :
    contacts G p.support q.support = 6 + if G.Adj p.center (q 3) then 1 else 0 := by
  obtain ⟨hX, hb, hc, hr⟩ := h.row_degrees
  rw [p.contacts_support, p.contacts_triangle, hX, hb, hc]
  change 3 + (degreeIn G p.center q.support + (3 + 0)) = _
  rw [hr]
  omega

lemma Configuration.inside_contacts (h : Configuration c p q) (hn : ¬QuadOn G p.support) :
    contacts G (insert (q 3) p.support) (p.support ∪ q.support) =
      17 + 2 * (if G.Adj p.center (q 3) then 1 else 0) := by
  have hY : degreeIn G (q 3) q.support = 3 := by
    rw [degreeIn_clique G h.complete.isClique ((q.mem_support _).mpr ⟨3, rfl⟩),
      q.card_support]
  rw [← singleton_union, contacts_union_left G
      (disjoint_singleton_left.mpr (h.quad_outside 3)), contacts_singleton_left,
    degreeIn_union G _ h.disjoint, contacts_union_right G _ h.disjoint,
    h.exposed_paw_degree, hY, p.internal_contacts_eq_eight hn, h.paw_block_contacts]
  omega

lemma Configuration.inside_le_nineteen (h : Configuration c p q) (hn : ¬QuadOn G p.support) :
    contacts G (insert (q 3) p.support) (p.support ∪ q.support) ≤ 19 := by
  rw [h.inside_contacts hn]
  split_ifs <;> omega

theorem Configuration.exists_heavy_block (h : Configuration c p q) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) :
    ∃ a ∈ c.blocks, a ≠ q.support ∧ 11 ≤ contacts G (insert (q 3) p.support) a := by
  apply c.exists_eleven_contact_outside_core hcard hdeg h.block
    (insert (q 3) p.support) h.five_card
  rw [← h.paw]
  exact h.inside_le_nineteen (by rw [h.paw]; exact c.no_quad_remainder hcard hn)

end Erdos577.UniversalTriple
