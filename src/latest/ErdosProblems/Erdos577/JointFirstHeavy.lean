import ErdosProblems.Erdos577.JointFirstArms
import ErdosProblems.Erdos577.OutsideSelectedCount

/-! The four-arm degree sum forces a nine-contact block outside both selected blocks. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_nine_outside_two {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (hbs2 : bs.card = 2)
    (r : Finset V) (hr : r.card = 4) (hinside : contacts G r (c.remainder ∪ bs.biUnion id) ≤ 22) :
    ∃ j ∈ c.blocks, j ∉ bs ∧ 9 ≤ contacts G r j := by
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  obtain ⟨j, hj, hjs, hh⟩ := c.exists_heavy_outside_selected bs hbs r (2 * k) 8 hdeg (by
    rw [hr]
    omega)
  exact ⟨j, hj, hjs, Nat.succ_le_of_lt hh⟩

theorem exists_heavy_arms {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a)
    (z1 z2 : V) (h1 : z1 ∈ a) (h2 : z2 ∈ a) (hne : z1 ≠ z2)
    (h17 : contacts G {p.leaf, z1, z2} (p.support ∪ q.support ∪ a) ≤ 17) :
    ∃ j ∈ c.blocks, j ≠ s ∧ j ≠ a ∧ 9 ≤ contacts G (arms p q z1 z2) j := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hAQ : Disjoint a q.support := by rw [hq]; exact c.property.blocks_disjoint ha hs has
  have hr4 := arms_card p q hFQ z1 z2
    (fun hh ↦ disjoint_left.mp hFA hh h1) (fun hh ↦ disjoint_left.mp hFA hh h2)
    (fun hh ↦ disjoint_left.mp hAQ h1 hh) (fun hh ↦ disjoint_left.mp hAQ h2 hh) hne
  have hinside := arms_inside_bound hc hcard hn p hp hs ha has q hq hcase
    houter hweighted z1 z2 h17
  have hsel : ({s, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hs (singleton_subset_iff.mpr ha)
  have he : c.remainder ∪ ({s, a} : Finset (Finset V)).biUnion id =
      p.support ∪ q.support ∪ a := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, ← hp, ← hq, union_assoc]
  obtain ⟨j, hj, hjs, hh⟩ := exists_nine_outside_two hcard hdeg {s, a} hsel
    (card_pair_eq_two_iff.mpr has.symm) (arms p q z1 z2) hr4 (he.symm ▸ hinside)
  simp only [mem_insert, mem_singleton, not_or] at hjs
  exact ⟨j, hj, hjs.1, hjs.2, hh⟩

end Erdos577.JointFirst
