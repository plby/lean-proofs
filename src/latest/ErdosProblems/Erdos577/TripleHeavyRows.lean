import ErdosProblems.Erdos577.TripleCoreFactors
import ErdosProblems.Erdos577.FirstPawFinalClassification
import ErdosProblems.Erdos577.DenseOutside
import ErdosProblems.Erdos577.DenseTriangle

/-! The high-contact case has exact triangle total ten and one exposed-vertex contact. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G}

lemma Configuration.five_contacts (h : Configuration c p q) (a : Finset V) :
    contacts G (insert (q 3) p.support) a = degreeIn G (q 3) a + contacts G p.support a := by
  rw [← singleton_union, contacts_union_left G (disjoint_singleton_left.mpr (h.quad_outside 3)),
    contacts_singleton_left]

theorem Configuration.high_leaf_zero (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) {a : Finset V} (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hheavy : 11 ≤ contacts G (insert (q 3) p.support) a)
    (hpaw : 9 ≤ contacts G p.support a) : degreeIn G p.leaf a = 0 := by
  by_contra hpos
  obtain ⟨d, hd⟩ := c.property.blocks_quad a ha
  have hclass := hc.first_paw_final hcard hdeg hn p h.paw ha d hd
    (by rwa [hd]) (by rw [hd]; omega)
  have hnine : contacts G p.support a = 9 := by simpa only [hd] using hclass.2.1
  have hY : 2 ≤ degreeIn G (q 3) d.support := by
    rw [hd]
    rw [h.five_contacts] at hheavy
    omega
  have hout : q 3 ∉ p.support ∪ d.support := by
    rw [hd]
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact h.quad_outside 3 hh
    · exact disjoint_left.mp (c.property.blocks_disjoint h.block ha haq.symm)
        ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  have hf := hclass.2.2.1 (q 3) hout hY
  rw [hd] at hf
  exact h.no_exposed_core_factor hcard hn ha haq hf

theorem Configuration.high_exact_counts (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) {a : Finset V} (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hheavy : 11 ≤ contacts G (insert (q 3) p.support) a)
    (hpaw : 9 ≤ contacts G p.support a) :
    degreeIn G p.leaf a = 0 ∧ contacts G p.triangle a = 10 ∧
      degreeIn G (q 3) a = 1 ∧ 5 ≤ edgeCount G a := by
  have hzero := h.high_leaf_zero hc hcard hdeg hn ha haq hheavy hpaw
  have hpaw_eq := p.contacts_support a
  have htri : 9 ≤ contacts G p.triangle a := by omega
  obtain ⟨d, hd, hY, hT, _, _, hblocks⟩ := h.exists_exposed_chain hc
  have ha' : a ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨haq, ha⟩)
  have hYle := hd.terminal_degree_le_one_of_dense hcard hn ha' (by rw [hT]; exact htri)
  rw [hY] at hYle
  have hupper := h.triangle_bound a ha
  have hfive := h.five_contacts a
  have hten : contacts G p.triangle a = 10 := by omega
  have hedges := (hc.presentPaw_feasible p h.paw).two_triangle_universal_replacements ha
    (show 10 ≤ contacts G p.triangle a from hten.ge)
  exact ⟨hzero, hten, by omega, hedges.1⟩

end Erdos577.UniversalTriple
