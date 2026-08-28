import ErdosProblems.Erdos577.JointCorePositive

/-! The local core construction under exactly the two source row inequalities.
The high-contact complete-complement choice and first-block degree bounds
are separate remaining parts of the full dense-core lemma. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem core_outside_factor {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a)
    (u : V) (hu : u ∉ p.triangle ∪ a) (hdegree : 2 ≤ degreeIn G u (p.triangle ∪ a)) :
    LocalFactor G (insert u (p.triangle ∪ a)) := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad a ha
  obtain ⟨tag, q', hq', hpattern⟩ := source_classification hc p hp ha q hq houter hweighted
  have hd : Disjoint p.triangle q'.support := by
    apply disjoint_left.mpr
    intro v hv hvq
    have hvp : v ∈ p.support := p.support_eq ▸ mem_insert_of_mem hv
    rw [hp] at hvp
    rw [hq'] at hvq
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hvq)).2 hvp
  rw [← hq'] at hu hdegree ⊢
  exact hpattern.outside_factor tag p q' hd u hu hdegree

theorem local_core_pair {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a) :
    ∃ q : Quadrilateral G, q.support = a ∧
      G.Adj p.center (q 2) ∧ G.Adj p.center (q 3) ∧ G.Adj (q 2) (q 3) ∧
      QuadOn G ((p.triangle ∪ a) \ {p.center, q 2, q 3}) ∧
      5 ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, q 2, q 3}) ∧
      QuadOn G ((p.triangle ∪ a) \ {q 2, p.center, p.vertices 2}) ∧
      QuadOn G ((p.triangle ∪ a) \ {q 3, p.center, p.vertices 2}) ∧
      QuadOn G ((p.triangle ∪ a) \ {q 2, q 3, p.vertices 2}) ∧
      (∀ v ∈ a, QuadOn G (insert (p.vertices 3) (a.erase v))) := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad a ha
  obtain ⟨tag, q', hq', hpattern⟩ := source_classification hc p hp ha q hq houter hweighted
  have hPA : Disjoint p.support a := by
    rw [hp]
    apply disjoint_left.mpr
    intro v hv hva
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hva)).2 hv
  have hd : Disjoint p.triangle q'.support := by
    rw [hq']
    exact hPA.mono_left (p.support_eq ▸ subset_insert _ _)
  have hu : p.leaf ∉ p.triangle ∪ q'.support := by
    intro hv
    rcases mem_union.mp hv with hv | hv
    · exact p.leaf_not_mem_triangle hv
    · rw [hq'] at hv
      exact disjoint_left.mp hPA (p.support_eq ▸ mem_insert_self _ _) hv
  have hlocal := hpattern.complements tag p q' hd p.leaf hu
  have hthird := hpattern.third_universal tag p q' hd p.leaf hu
  rw [hq'] at hlocal hthird
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hlocal
  exact ⟨q', hq', h1, h2, h3, h4, h5, h6, h7, h8, hthird⟩

end Erdos577.JointCore
