import ErdosProblems.Erdos577.MultiScores

/-! Expose a specified terminal while exchanging any selected family of cycle blocks. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def replaceSelected (c : TriangleChain G) (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks)
    {u t : Finset V} (q : BlockPartition G u) (hu : u ⊆ c.remainder ∪ bs.biUnion id)
    (x : V) (ht : G.IsNClique 3 t) (hx : x ∉ t)
    (hr : (c.remainder ∪ bs.biUnion id) \ u = insert x t) : TriangleChain G :=
  ofPartition ht hx {
    blocks := (c.complementPartition.splice bs hbs q hu).blocks
    disjoint := (c.complementPartition.splice bs hbs q hu).disjoint
    cover := by rw [← hr]; exact (c.complementPartition.splice bs hbs q hu).cover
    quad := (c.complementPartition.splice bs hbs q hu).quad }

lemma replaceSelected_keeps (c : TriangleChain G) (bs : Finset (Finset V))
    (hbs : bs ⊆ c.blocks) {u t : Finset V} (q : BlockPartition G u)
    (hu : u ⊆ c.remainder ∪ bs.biUnion id) (x : V) (ht : G.IsNClique 3 t) (hx : x ∉ t)
    (hr : (c.remainder ∪ bs.biUnion id) \ u = insert x t)
    {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs) :
    a ∈ (c.replaceSelected bs hbs q hu x ht hx hr).blocks :=
  mem_union_left _ (mem_sdiff.mpr ⟨ha, hna⟩)

variable [DecidableRel G.Adj]

lemma Feasible.replaceSelected_feasible {c : TriangleChain G} (hc : c.Feasible)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks)
    {u t : Finset V} (q : BlockPartition G u) (hu : u ⊆ c.remainder ∪ bs.biUnion id)
    (x : V) (ht : G.IsNClique 3 t) (hx : x ∉ t)
    (hr : (c.remainder ∪ bs.biUnion id) \ u = insert x t)
    (he : q.weightSum (edgeCount G) =
      (c.complementPartition.select bs hbs).weightSum (edgeCount G))
    (hf : q.weightSum (fun a ↦ if edgeCount G a = 6 then 1 else 0) =
      (c.complementPartition.select bs hbs).weightSum
        (fun a ↦ if edgeCount G a = 6 then 1 else 0)) :
    (c.replaceSelected bs hbs q hu x ht hx hr).Feasible := by
  let d := c.replaceSelected bs hbs q hu x ht hx hr
  have hed := c.complementPartition.weightSum_splice_add bs hbs q hu (edgeCount G)
  change d.edgeScore + _ = c.edgeScore + _ at hed
  rw [he] at hed
  have heq : d.edgeScore = c.edgeScore := Nat.add_right_cancel hed
  have hfd := c.complementPartition.weightSum_splice_add bs hbs q hu
    (fun a ↦ if edgeCount G a = 6 then 1 else 0)
  have hbase : c.complementPartition.weightSum
      (fun a ↦ if edgeCount G a = 6 then 1 else 0) = c.completeScore := by
    rw [c.completeScore_eq_sum]
    rfl
  have hnew : (c.complementPartition.splice bs hbs q hu).weightSum
      (fun a ↦ if edgeCount G a = 6 then 1 else 0) = d.completeScore := by
    rw [d.completeScore_eq_sum]
    rfl
  rw [hbase, hnew, hf] at hfd
  have hfeq : d.completeScore = c.completeScore := Nat.add_right_cancel hfd
  constructor
  · intro e
    rw [heq]
    exact hc.edge_max e
  · intro e hde
    rw [hfeq]
    exact hc.complete_max e (hde.trans heq)

end Erdos577.TriangleChain
