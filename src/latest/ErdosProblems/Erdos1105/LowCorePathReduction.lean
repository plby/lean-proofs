import ErdosProblems.Erdos1105.TwoAttachmentPendant
import ErdosProblems.Erdos1105.ShortCoreFullDegree

namespace Erdos1105

open SimpleGraph Finset

lemma short_two_attachment_start_pattern {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2)
    (hB : endNeighborIndices p = insert d (Ico (p.length - d) p.length)) :
    startNeighborIndices p = insert (p.length - d - 1) (range d) := by
  classical
  ext i
  by_cases hi : i < p.length
  · have hiff : i ∈ startNeighborIndices p ↔ i ∉ endNeighborIndices p := by
      simpa only [startNeighborIndices, endNeighborIndices, mem_filter, mem_range, hi, true_and]
        using short_low_core_neighbor_iff hG hu hconn p hp hlen hi
    rw [hiff, hB]
    simp only [mem_insert, mem_Ico, mem_range]
    omega
  · have hnot : i ∉ startNeighborIndices p := fun h ↦ hi (mem_range.mp (mem_filter.mp h).1)
    simp only [hnot, mem_insert, mem_range, false_iff, not_or]
    omega

/-- The long low-core path case and the two-attachment short case already
obey the even-path bound. A counterexample with non-clique core must have
a short alternating pattern with at least three attachments. -/
theorem even_high_nonclique_core_short_pattern {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d)
    (hn : 2 * d + 2 ≤ Fintype.card V) (hconn : G.Preconnected)
    (hfree : ¬pathGraph (2 * d + 2) ⊑ G)
    (hmax : ∀ J : SimpleGraph (Option V), graphCone G ≤ J → NoLongCycle J (2 * d + 3) →
      J = graphCone G)
    (hnot : ¬(graphCone G).IsClique (vertexCore (graphCone G) d : Set (Option V)))
    (hhigh : pathFormula (Fintype.card V) (2 * d + 2) < G.edgeFinset.card) :
    ∃ x y, ∃ p : (graphCone G).Walk x y,
      IsLongestSetPath (vertexCore (graphCone G) d : Set (Option V)) p ∧
      p.length = 2 * d + 2 ∧ ∃ a, 1 ≤ a ∧ a < d ∧
        endNeighborIndices p =
          (range (d + 1 - a)).image (fun j ↦ a + 2 * j) ∪ Ico (p.length - a) p.length ∧
        (∀ j < a, ¬(graphCone G).Adj y (p.getVert j)) ∧
        (∀ j, p.length - a < j → j ≤ p.length → ¬(graphCone G).Adj x (p.getVert j)) ∧
        (∀ t, a ≤ t → t ≤ p.length - a →
          ((graphCone G).Adj x (p.getVert t) ↔ Even (t - a)) ∧
          ((graphCone G).Adj y (p.getVert t) ↔ Even (t - a))) := by
  have hG : NoLongCycle (graphCone G) (2 * d + 3) :=
    no_long_cycle_cone_of_path_free G (by omega) hfree
  have hu := graphCone_universal G
  have hconn' := graphCone_delete_preconnected G hconn
  obtain ⟨x, y, p, hp, hlong⟩ := exists_longest_core_path_of_not_clique _ hG hmax hnot
  have hlen : p.length = 2 * d + 2 := by
    by_contra h
    obtain ⟨hA, hB⟩ := long_low_core_neighbor_pattern hG hu hconn' p hp (by omega)
    have := even_path_bound_of_two_attachment_core G hd hn hconn hfree p hp (by omega) hA hB
    omega
  obtain ⟨a, ha, had, hB, hbefore, hafter, hmiddle⟩ :=
    short_low_core_complete_pattern hG hu hconn' p hp hlen
  have hal : a < d := by
    by_contra h
    have had' : a = d := by omega
    subst a
    have hB' : endNeighborIndices p = insert d (Ico (p.length - d) p.length) := by
      simpa only [show d + 1 - d = 1 by omega, range_one, image_singleton, Nat.mul_zero,
        Nat.add_zero, singleton_union] using hB
    have hA := short_two_attachment_start_pattern hG hu hconn' p hp hlen hB'
    have := even_path_bound_of_two_attachment_core G hd hn hconn hfree p hp (by omega) hA hB'
    omega
  exact ⟨x, y, p, hp, hlen, a, ha, hal, hB, hbefore, hafter, hmiddle⟩

end Erdos1105

#print axioms Erdos1105.even_high_nonclique_core_short_pattern
