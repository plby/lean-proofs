import ErdosProblems.Erdos577.TriangleAssembly

/-! The two feasibility bounds for exchanges of any selected block family. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Feasible.selected_edges_le {c : TriangleChain G} (hc : c.Feasible)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) {u : Finset V} (q : BlockPartition G u)
    (hu : u ⊆ c.remainder ∪ bs.biUnion id)
    (hcard : ((c.remainder ∪ bs.biUnion id) \ u).card = 4)
    (htri : TriangleIn G ((c.remainder ∪ bs.biUnion id) \ u)) :
    q.weightSum (edgeCount G) ≤
      (c.complementPartition.select bs hbs).weightSum (edgeCount G) := by
  let p := c.complementPartition.splice bs hbs q hu
  have hle := hc.partition_score_le hcard p htri
  have he := c.complementPartition.weightSum_splice_add bs hbs q hu (edgeCount G)
  change p.weightSum (edgeCount G) +
      (c.complementPartition.select bs hbs).weightSum (edgeCount G) =
      c.edgeScore + q.weightSum (edgeCount G) at he
  omega

lemma Feasible.selected_complete_le {c : TriangleChain G} (hc : c.Feasible)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) {u : Finset V} (q : BlockPartition G u)
    (hu : u ⊆ c.remainder ∪ bs.biUnion id)
    (hcard : ((c.remainder ∪ bs.biUnion id) \ u).card = 4)
    (htri : TriangleIn G ((c.remainder ∪ bs.biUnion id) \ u))
    (hedges : q.weightSum (edgeCount G) =
      (c.complementPartition.select bs hbs).weightSum (edgeCount G)) :
    q.weightSum (fun b ↦ if edgeCount G b = 6 then 1 else 0) ≤
      (c.complementPartition.select bs hbs).weightSum
        (fun b ↦ if edgeCount G b = 6 then 1 else 0) := by
  let p := c.complementPartition.splice bs hbs q hu
  have he := c.complementPartition.weightSum_splice_add bs hbs q hu (edgeCount G)
  change p.weightSum (edgeCount G) +
      (c.complementPartition.select bs hbs).weightSum (edgeCount G) =
      c.edgeScore + q.weightSum (edgeCount G) at he
  have heq : p.weightSum (edgeCount G) = c.edgeScore := by omega
  have hle := hc.partition_complete_le hcard p htri heq
  have ht := c.complementPartition.weightSum_splice_add bs hbs q hu
    (fun b ↦ if edgeCount G b = 6 then 1 else 0)
  have hbase : c.complementPartition.weightSum (fun b ↦ if edgeCount G b = 6 then 1 else 0) =
      c.completeScore := by
    rw [c.completeScore_eq_sum]
    rfl
  rw [hbase] at ht
  change p.weightSum (fun b ↦ if edgeCount G b = 6 then 1 else 0) +
      (c.complementPartition.select bs hbs).weightSum
        (fun b ↦ if edgeCount G b = 6 then 1 else 0) =
      c.completeScore + q.weightSum (fun b ↦ if edgeCount G b = 6 then 1 else 0) at ht
  omega

end Erdos577.TriangleChain
