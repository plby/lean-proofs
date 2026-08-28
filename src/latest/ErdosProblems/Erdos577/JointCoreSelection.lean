import ErdosProblems.Erdos577.JointCoreHighPair
import ErdosProblems.Erdos577.JointCoreFirstRows

/-! Choose the core pair with the stronger complete-complement clause when needed. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem selected_pair {c : TriangleChain G} (hc : c.Feasible)
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
      (∀ v ∈ a, QuadOn G (insert (p.vertices 3) (a.erase v))) ∧
      (11 ≤ contacts G p.triangle a →
        G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, q 2, q 3})) ∧
      (contacts G p.triangle a ≤ 10 → ∃ tag : Fin 8, SourcePattern tag p q) := by
  have hd : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  by_cases hhigh : 11 ≤ contacts G p.triangle a
  · obtain ⟨hcl, hrep⟩ := (hc.presentPaw_feasible p hp).all_triangle_universal_replacements ha hhigh
    obtain ⟨q, hq, hr1, hr2, hz, hprimary, hs1, hs2, ht⟩ := high_core_pair p hcl hd hhigh
    have hquad := QuadOn.of_clique hprimary.card_eq hprimary.isClique
    have he : 5 ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, q 2, q 3}) := by
      rw [edgeCount_clique hprimary.isClique, hprimary.card_eq]
      decide
    exact ⟨q, hq, hr1, hr2, hz, hquad, he, hs1, hs2, ht,
      hrep (p.vertices 3) (by change p.vertices 3 ∈ p.triangle; simp [Paw.triangle]),
      fun _ ↦ hprimary,
      fun hh ↦ False.elim (by omega)⟩
  · obtain ⟨d, hdA⟩ := c.property.blocks_quad a ha
    obtain ⟨tag, q, hq, hpattern⟩ := source_classification hc p hp ha d hdA houter hweighted
    have hTA : Disjoint p.triangle q.support := by
      rw [hq]
      exact hd.mono_left (p.support_eq ▸ subset_insert _ _)
    have hx : p.leaf ∉ p.triangle ∪ q.support := by
      intro hh
      rcases mem_union.mp hh with hh | hh
      · exact p.leaf_not_mem_triangle hh
      · rw [hq] at hh
        exact disjoint_left.mp hd (p.support_eq ▸ mem_insert_self _ _) hh
    have hlocal := hpattern.complements tag p q hTA p.leaf hx
    have hrep := hpattern.third_universal tag p q hTA p.leaf hx
    rw [hq] at hlocal hrep
    obtain ⟨hr1, hr2, hz, hprimary, he, hs1, hs2, ht⟩ := hlocal
    exact ⟨q, hq, hr1, hr2, hz, hprimary, he, hs1, hs2, ht, hrep,
      fun hh ↦ False.elim (hhigh hh), fun _ ↦ ⟨tag, hpattern⟩⟩

end Erdos577.JointCore
