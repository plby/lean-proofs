import ErdosProblems.Erdos1105.PathFree
import ErdosProblems.Erdos1105.CoreBasics
import ErdosProblems.Erdos1105.LongestSetPath
import ErdosProblems.Erdos1105.CappedEdges

namespace Erdos1105

open SimpleGraph Finset

theorem path_free_vertexCore_empty {V : Type*} [Fintype V] (G : SimpleGraph V)
    {k : ℕ} (hk : 2 ≤ k) (hfree : ¬pathGraph k ⊑ G) : vertexCore G (k - 2) = ∅ := by
  classical
  by_contra hne
  obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.mpr hne
  obtain ⟨a, ha, b, hb, p, hp, hlong⟩ := exists_longest_path_between_sets G
    (vertexCore G (k - 2) : Set V) (vertexCore G (k - 2) : Set V)
    ⟨v, hv, v, hv, Walk.nil, by simp⟩
  have hwithin : ∀ w ∈ vertexCore G (k - 2), G.Adj a w → w ∈ p.support.toFinset := by
    intro w hw hadj
    by_contra hnot
    have hnot' : w ∉ p.support := by simpa using hnot
    have hpath : (Walk.cons hadj.symm p).IsPath :=
      (Walk.cons_isPath_iff _ _).mpr ⟨hp, hnot'⟩
    have h := hlong w hw b hb _ hpath
    rw [Walk.length_cons] at h
    omega
  have hdeg := (vertexCore_degree G (k - 2) ha).trans_le
    (degreeWithin_le_of_neighbors_mem G _ p.support.toFinset a hwithin)
  have hupp := degreeWithin_le_card_sub_one G (List.mem_toFinset.mpr p.start_mem_support)
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
  have hlen := path_length_lt_of_path_free hfree p hp
  omega

theorem path_free_edges_le_capped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k)
    (hfree : ¬pathGraph k ⊑ G) : G.edgeFinset.card ≤ cappedEdgeBound (Fintype.card V) (k - 2) := by
  by_cases hn : Fintype.card V ≤ k - 2
  · rw [cappedEdgeBound_eq_choose hn]
    exact G.card_edgeFinset_le_card_choose_two
  · rw [cappedEdgeBound_eq_linear (by omega)]
    exact edges_le_of_core_empty G (k - 2) (path_free_vertexCore_empty G hk hfree)

end Erdos1105

#print axioms Erdos1105.path_free_edges_le_capped
