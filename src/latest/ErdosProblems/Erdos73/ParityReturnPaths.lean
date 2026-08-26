import ErdosProblems.Erdos73.ParityColoring

/-! A breaking path and a balanced return path form a non-bipartite region. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

theorem not_bipartite_union_of_parityBreaking {V : Type*} [Fintype V]
    {G : SimpleGraph V} {T : Finset V} (c : BipartiteColoringOn G T)
    (P Q : GraphPath G) (hP : ParityBreaking c.color P)
    (hs : P.source = Q.source) (ht : P.target = Q.target) (hQ : Q.vertexSet ⊆ T) :
    ¬ (G.induce ((P.vertexSet ∪ Q.vertexSet : Finset V) : Set V)).IsBipartite := by
  intro hb
  let d := bipartiteColoringOnOfBipartite hb
  have hPe := d.even_walk P.walk (fun v hv => mem_union_left _ (List.mem_toFinset.mpr hv))
  have hQe := d.even_walk Q.walk (fun v hv => mem_union_right _ (List.mem_toFinset.mpr hv))
  have hQc := c.even_walk Q.walk (fun v hv => hQ (List.mem_toFinset.mpr hv))
  have hcs := congrArg (fun v => (c.color v).toNat) hs
  have hct := congrArg (fun v => (c.color v).toNat) ht
  have hds := congrArg (fun v => (d.color v).toNat) hs
  have hdt := congrArg (fun v => (d.color v).toNat) ht
  rw [ParityBreaking, Nat.odd_iff] at hP
  rw [Nat.even_iff] at hPe hQe hQc
  omega

end
end Erdos73
