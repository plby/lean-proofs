import ErdosProblems.Erdos73.BrickFaces
import ErdosProblems.Erdos73.SubdivisionCycles

/-! Actual subdivided brick-face supports remain connected after one vertex deletion. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

theorem hexagonSubdivision_deletionOneConnected
    (S : GraphSubdivisionModel (cycleGraph 6) G) : DeletionOneConnected G S.vertexSet := by
  have hverts : ∀ v : Fin 6, v ∈ (cycleGraph.cycle 3).support := by
    intro v
    have he : (cycleGraph.cycle 3).getVert (6 - v.val) = v := by
      rw [cycleGraph.getVert_cycle (by omega : 6 - v.val ≤ 3 + 3)]
      apply Fin.ext
      change (3 + 3 - (6 - v.val)) % (3 + 3) = v.val
      omega
    exact he ▸ (cycleGraph.cycle 3).getVert_mem_support (6 - v.val)
  have hedges : ∀ u v : Fin 6, (cycleGraph 6).Adj u v →
      s(u, v) ∈ (cycleGraph.cycle 3).edges := by
    let f : Fin 7 → Fin 6 := fun i => ⟨(6 - i.val) % 6, Nat.mod_lt _ (by decide)⟩
    have hfind : ∀ u v : Fin 6, (cycleGraph 6).Adj u v →
        ∃ i : Fin 6, s(f i.castSucc, f i.succ) = s(u, v) := by decide
    intro u v huv
    obtain ⟨i, hi⟩ := hfind u v huv
    have hedge := Walk.adj_toSubgraph_iff_mem_edges.mp
      ((cycleGraph.cycle 3).toSubgraph_adj_getVert (by
        simpa only [cycleGraph.length_cycle] using i.isLt))
    have he : s((cycleGraph.cycle 3).getVert i.val,
        (cycleGraph.cycle 3).getVert (i.val + 1)) = s(u, v) := by
      rw [cycleGraph.getVert_cycle (by omega : i.val ≤ 3 + 3),
        cycleGraph.getVert_cycle (by omega : i.val + 1 ≤ 3 + 3)]
      exact hi
    exact he ▸ hedge
  have heq : S.walkSupport (cycleGraph.cycle 3) = S.vertexSet := by
    ext x
    constructor
    · intro hx
      rcases (S.mem_walkSupport _ x).mp hx with ⟨w, _, he⟩ | ⟨e, _, he⟩
      · exact (S.mem_vertexSet x).mpr (Or.inl ⟨w, he⟩)
      · exact (S.mem_vertexSet x).mpr (Or.inr ⟨e, he⟩)
    · intro hx
      rcases (S.mem_vertexSet x).mp hx with ⟨w, he⟩ | ⟨e, he⟩
      · exact (S.mem_walkSupport _ x).mpr (Or.inl ⟨w, hverts w, he⟩)
      · exact (S.mem_walkSupport _ x).mpr (Or.inr ⟨e, hedges e.lo e.hi e.adj, he⟩)
  exact heq ▸ S.deletionOneConnected_walkSupport (cycleGraph.cycle 3) cycleGraph.isCycle_cycle

def brickFaceSupport {c r : ℕ} (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a b : ℕ) (hr : a + 1 < r) (hc : b + 2 < 2 * c) (hpar : (b + a) % 2 = 1) : Finset V :=
  (S.restrictCopy (elementaryBrickFaceCopy a b hr hc hpar)).vertexSet

theorem brickFaceSupport_deletionOneConnected {c r : ℕ}
    (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a b : ℕ) (hr : a + 1 < r) (hc : b + 2 < 2 * c) (hpar : (b + a) % 2 = 1) :
    DeletionOneConnected G (brickFaceSupport S a b hr hc hpar) :=
  hexagonSubdivision_deletionOneConnected (S.restrictCopy (elementaryBrickFaceCopy a b hr hc hpar))

end
end Erdos73
