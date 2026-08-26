import ErdosProblems.Erdos73.ParityColoring

/-! Preserve terminal-clean parity-breaking paths when changing only ambient edges. -/

namespace Erdos73
noncomputable section

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G J : SimpleGraph V} {T R : Finset V}

def BipartiteColoringOn.mono_graph (c : BipartiteColoringOn G T) (hJG : J ≤ G) :
    BipartiteColoringOn J T := ⟨c.color, fun x hx y hy hxy => c.valid x hx y hy (hJG hxy)⟩

def BipartiteColoringOn.mono_support (c : BipartiteColoringOn G T) (hRT : R ⊆ T) :
    BipartiteColoringOn G R := ⟨c.color, fun x hx y hy hxy => c.valid x (hRT hx) y (hRT hy) hxy⟩

theorem IsParityBreakingPath.mapLe {c : V → Bool} {P : GraphPath G}
    (hP : IsParityBreakingPath c T P) (hGJ : G ≤ J) :
    IsParityBreakingPath c T (P.mapLe hGJ) := by
  refine ⟨hP.source_mem, hP.target_mem, ?_, ?_⟩
  · simpa only [ParityBreaking, GraphPath.mapLe, Walk.length_mapLe] using hP.breaking
  · intro x hx hxT
    rw [GraphPath.mapLe_vertexSet] at hx
    exact hP.internal_disjoint x hx hxT

theorem IsParityBreakingPath.transfer {c : V → Bool} {P : GraphPath G}
    (hP : IsParityBreakingPath c T P) (J : SimpleGraph V)
    (hJ : ∀ e, e ∈ P.walk.edges → e ∈ J.edgeSet) :
    IsParityBreakingPath c T (P.transfer J hJ) := by
  refine ⟨hP.source_mem, hP.target_mem, ?_, ?_⟩
  · simpa only [ParityBreaking, GraphPath.transfer, Walk.length_transfer] using hP.breaking
  · intro x hx hxT
    rw [GraphPath.transfer_vertexSet] at hx
    exact hP.internal_disjoint x hx hxT

theorem IsParityBreakingPath.reverse {c : V → Bool} {P : GraphPath G}
    (hP : IsParityBreakingPath c T P) : IsParityBreakingPath c T P.reverse := by
  refine ⟨hP.target_mem, hP.source_mem, ?_, ?_⟩
  · have hh := hP.breaking
    rw [ParityBreaking, Nat.odd_iff] at hh ⊢
    simp only [GraphPath.reverse, Walk.length_reverse]
    omega
  · intro x hx hxT
    rw [GraphPath.reverse_vertexSet] at hx
    exact (hP.internal_disjoint x hx hxT).symm

end
end Erdos73
