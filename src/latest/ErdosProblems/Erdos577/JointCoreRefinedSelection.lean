import ErdosProblems.Erdos577.JointCoreNormalizedComplement
import ErdosProblems.Erdos577.JointCoreSelection

/-! Refined labels retain every core complement and the high-contact complete complement. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem refined_selected_pair {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a)
    (hseven : degreeIn G p.center a + degreeIn G (p.vertices 3) a = 7 →
      10 ≤ contacts G p.triangle a) :
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
      (contacts G p.triangle a ≤ 10 → ∃ tag : Fin 8, RefinedSourcePattern tag p q ∧
        (tag = 1 → degreeIn G (p.vertices 2) a = 2 →
          (∀ j : Fin 4, G.Adj (p.vertices 2) (q j) ↔ j = 0 ∨ j = 1) ∧
          G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, q 2, q 3}))) := by
  by_cases hhigh : 11 ≤ contacts G p.triangle a
  · obtain ⟨q, hq, hr1, hr2, hz, hprimary, he, hs1, hs2, ht, hrep, hcl, _⟩ :=
      selected_pair hc p hp ha houter hweighted
    exact ⟨q, hq, hr1, hr2, hz, hprimary, he, hs1, hs2, ht, hrep, hcl,
      fun hh ↦ False.elim (by omega)⟩
  · obtain ⟨d, hd⟩ := c.property.blocks_quad a ha
    obtain ⟨tag, v, hv, hpattern⟩ := source_classification hc p hp ha d hd houter hweighted
    obtain ⟨tag', q, hqv, hpat, hnormal⟩ := hpattern.refined_labels tag p v (by rwa [hv])
    have hq : q.support = a := hqv.trans hv
    have hPA : Disjoint p.support q.support := by
      rw [hp, hq]
      exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
    have hTA : Disjoint p.triangle q.support := hPA.mono_left (p.support_eq ▸ subset_insert _ _)
    have hx : p.leaf ∉ p.triangle ∪ q.support := by
      intro hh
      rcases mem_union.mp hh with hh | hh
      · exact p.leaf_not_mem_triangle hh
      · exact disjoint_left.mp hPA (p.support_eq ▸ mem_insert_self _ _) hh
    have hlocal := hpat.1.complements tag' p q hTA p.leaf hx
    have hrep := hpat.1.third_universal tag' p q hTA p.leaf hx
    rw [hq] at hlocal hrep
    obtain ⟨hr1, hr2, hz, hprimary, he, hs1, hs2, ht⟩ := hlocal
    refine ⟨q, hq, hr1, hr2, hz, hprimary, he, hs1, hs2, ht, hrep,
      fun hh ↦ False.elim (hhigh hh), fun _ ↦ ⟨tag', hpat, ?_⟩⟩
    intro htag htwo
    have hrow := hnormal htag (by rwa [hq])
    refine ⟨hrow, ?_⟩
    have hcl := (htag ▸ hpat.1).normalized_primary_clique p q hPA
      ((hrow 1).mpr (Or.inr rfl))
    rwa [hq] at hcl

end Erdos577.JointCore
