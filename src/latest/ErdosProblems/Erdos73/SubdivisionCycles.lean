import ErdosProblems.Erdos73.SubdivisionPaths
import ErdosProblems.Erdos73.RobustConnectedSupport

/-! A simple pattern cycle expands to an actual simple cycle with exact subdivision support. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

theorem exists_cycle_with_walkSupport (S : GraphSubdivisionModel H G)
    {u : W} (c : H.Walk u u) (hc : c.IsCycle) :
    ∃ d : G.Walk (S.branchVertex u) (S.branchVertex u),
      d.IsCycle ∧ d.support.toFinset = S.walkSupport c := by
  let h := c.adj_snd hc.not_nil
  let p := c.tail
  have hp : p.IsPath := hc.isPath_tail
  have hcons : p.cons h = c := c.cons_tail_eq hc.not_nil
  have hc' : (p.cons h).IsCycle := by rw [hcons]; exact hc
  have hn : s(u, c.snd) ∉ p.edges := ((Walk.cons_isCycle_iff p h).mp hc').2
  obtain ⟨Q, hQs, hQt, hQset⟩ := S.exists_path_with_walkSupport p hp
  let E := S.pathAlongAdj h
  let A := E.walk.copy (S.pathAlongAdj_source h) (S.pathAlongAdj_target h)
  let B := Q.walk.copy hQs hQt
  have hA : A.IsPath := by simpa only [A, Walk.isPath_copy] using E.isPath
  have hB : B.IsPath := by simpa only [B, Walk.isPath_copy] using Q.isPath
  have hnotA : S.branchVertex u ∉ A.support.tail := by
    have hh := hA.support_nodup
    rw [← A.cons_tail_support] at hh
    exact (List.nodup_cons.mp hh).1
  have hnotB : S.branchVertex c.snd ∉ B.support.tail := by
    have hh := hB.support_nodup
    rw [← B.cons_tail_support] at hh
    exact (List.nodup_cons.mp hh).1
  have hdis : A.support.tail.Disjoint B.support.tail := by
    rw [List.disjoint_left]
    intro x hxA hxB
    have hxE : x ∈ E.vertexSet := by
      have hh := List.mem_of_mem_tail hxA
      simpa only [A, Walk.support_copy, GraphPath.vertexSet, List.mem_toFinset] using hh
    have hxQ : x ∈ Q.vertexSet := by
      have hh := List.mem_of_mem_tail hxB
      simpa only [B, Walk.support_copy, GraphPath.vertexSet, List.mem_toFinset] using hh
    rcases S.corridor_inter_walkSupport h p hn hxE (hQset ▸ hxQ) with he | he
    · exact hnotA (he ▸ hxA)
    · exact hnotB (he ▸ hxB)
  have hlong : 1 < B.length := by
    have hlen := S.length_le_of_walkSupport_subset p hp Q (by rw [hQset])
    have htail := c.length_tail_add_one hc.not_nil
    have hthree := hc.three_le_length
    change 1 < (Q.walk.copy hQs hQt).length
    rw [Walk.length_copy]
    change c.tail.length ≤ Q.walk.length at hlen
    omega
  refine ⟨A.append B, hA.isCycle_append hB hdis (Or.inr hlong), ?_⟩
  have hset : (A.append B).support.toFinset = E.vertexSet ∪ Q.vertexSet := by
    ext x
    simp only [List.mem_toFinset, Walk.mem_support_append_iff, A, B, Walk.support_copy,
      Finset.mem_union, GraphPath.vertexSet]
  rw [hset, hQset, ← S.walkSupport_cons h p, hcons]

theorem deletionOneConnected_walkSupport (S : GraphSubdivisionModel H G)
    {u : W} (c : H.Walk u u) (hc : c.IsCycle) : DeletionOneConnected G (S.walkSupport c) := by
  obtain ⟨d, hd, hset⟩ := S.exists_cycle_with_walkSupport c hc
  exact hset ▸ DeletionOneConnected.of_cycle d hd

end
end Erdos73.GraphSubdivisionModel
