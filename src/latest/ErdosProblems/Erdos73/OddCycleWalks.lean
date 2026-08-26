import ErdosProblems.Erdos73.Foundations
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-! An odd-cycle subgraph has a cyclic walk with exactly its original vertex support. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem IsOddCycleSubgraph.exists_cycleWalk {H : G.Subgraph} (hH : IsOddCycleSubgraph H) :
    ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ Odd c.length ∧
      (c.support.toFinset : Set V) = H.verts := by
  obtain ⟨n, hn3, hnodd, ⟨e⟩⟩ := hH
  have hcopy : cycleGraph n ⊑ H.coe := ⟨e.toCopy⟩
  obtain ⟨v, c, hc, hlen⟩ := (cycleGraph_isContained_iff (by omega : 2 < n)).mp hcopy
  have hcard : Fintype.card H.verts = n := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr e.toEquiv).symm
  have hham : c.IsHamiltonianCycle := Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    ⟨hc, hlen.trans hcard.symm⟩
  refine ⟨H.coeCopy v, c.map H.coeCopy.toHom, hc.map H.coeCopy.injective, ?_, ?_⟩
  · rw [Walk.length_map, hlen]
    exact hnodd
  · ext x
    constructor
    · intro hx
      have hx' : x ∈ c.support.map H.coeCopy.toHom := by
        have hh := List.mem_toFinset.mp hx
        rw [Walk.support_map] at hh
        exact hh
      obtain ⟨y, _, hy⟩ := List.mem_map.mp hx'
      exact hy ▸ y.property
    · intro hx
      apply List.mem_toFinset.mpr
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨⟨x, hx⟩, hham.mem_support _, rfl⟩

end
end Erdos73
