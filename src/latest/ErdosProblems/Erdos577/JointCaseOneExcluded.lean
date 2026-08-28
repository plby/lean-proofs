import ErdosProblems.Erdos577.JointFirstObstruction
import ErdosProblems.Erdos577.JointCaseOneExposed
import ErdosProblems.Erdos577.JointSetup

/-! The six-row heavy block excludes CaseI in either choice of the center row. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem case_one_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseOne p q) : False := by
  obtain ⟨_, _, ⟨d, p', hd, _, _, hpl, hpc, hp2, hp3, hpT, hps, _, _, hblocks, hkeep⟩,
      ⟨a, ha, has, hheavy⟩, _⟩ := initial_exchange_and_six_row_sum hc hcard hdeg hn p hp
    hs q hq (Or.inl hcase)
  have hweight : 13 ≤ sixWeight p q a := by rwa [sixWeight_eq_rows]
  obtain ⟨_, _, hweighted⟩ := heavy_leaves_zero hc hcard hdeg hn p hp hs ha has q hq
    (Or.inl hcase) hweight
  by_cases houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a
  · exact case_one_dense_false hc hcard hdeg hn p hp hs ha has q hq hcase houter hweighted
  have hother : 7 ≤ degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a := by
    have he := p.contacts_triangle a
    omega
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hcl : G.IsNClique 4 q.support := by
    rw [hq]
    exact FullRow.full_leaf_clique hc p hp hs (hq ▸ hcase.1)
  have hdegrees := case_one_exposed_degrees p q hFQ hcl hcase
  rw [hq] at hdegrees
  let s' := insert p.leaf (s.erase (q 3))
  have hs' : s' ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_right _ (mem_singleton_self _)
  have has' : a ≠ s' := by
    intro he
    apply disjoint_left.mp hFA (p.support_eq ▸ mem_insert_self _ _)
    rw [he]
    exact mem_insert_self _ _
  have hfull' : degreeIn G p'.leaf s' = 4 := by rw [hpl]; exact hdegrees.1
  have hcenter' : 0 < degreeIn G p'.center s' := by rw [hpc]; exact hdegrees.2.1
  have hsecond' : 2 ≤ degreeIn G (p'.vertices 2) s' := by rw [hp2]; exact hdegrees.2.2
  obtain ⟨q', hq', hcase'⟩ := case_one_labels_of_degrees hd.toFeasible hcard hn p' hps hs'
    hfull' hcenter' hsecond'
  have houter' : 7 ≤ degreeIn G p'.center a + degreeIn G (p'.vertices 3) a := by
    rw [hpc, hp3]
    exact hother
  have hweighted' : 13 ≤ degreeIn G (p'.vertices 3) a + contacts G p'.triangle a := by
    rw [hp3, hpT]
    exact hweighted
  exact case_one_dense_false hd.toFeasible hcard hdeg hn p' hps hs' (hkeep a ha has)
    has' q' hq' hcase' houter' hweighted'

end Erdos577.JointClaims
