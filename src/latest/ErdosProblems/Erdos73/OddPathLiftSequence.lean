import ErdosProblems.Erdos73.OddPathAuxiliary
import ErdosProblems.Erdos73.OddTerminalPathsDefs

/-! The explicit two-layer sequence lifting an odd terminal path. -/

namespace Erdos73

open SimpleGraph Finset OddPathVertex
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : Finset V}

omit [Fintype V] in
theorem exists_oddPathLiftSequence {Q : GraphPath G} (hQ : IsOddTerminalPath A Q)
    {t : ℕ} (hlen : Q.walk.length = 2 * t + 1) :
    ∃ f : Fin (4 * t + 2) → OddPathVertex A, Function.Injective f ∧
      (∀ r, projection (f r) = Q.walk.getVert ((r.val + 1) / 2)) ∧
      (∀ r, layer (f r) = decide ((r.val / 2) % 2 = 1)) ∧
      (∀ i (hi : i + 1 < 4 * t + 2),
        (oddPathAuxiliary G A).Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩)) := by
  have hbound (r : Fin (4 * t + 2)) : (r.val + 1) / 2 ≤ Q.walk.length := by
    have hr := r.isLt
    omega
  have hex (r : Fin (4 * t + 2)) : ∃ x : OddPathVertex A,
      projection x = Q.walk.getVert ((r.val + 1) / 2) ∧
        layer x = decide ((r.val / 2) % 2 = 1) := by
    apply exists_projection_layer
    intro hbit hterminal
    have hpar : (r.val / 2) % 2 = 1 := of_decide_eq_true hbit
    have hmem : Q.walk.getVert ((r.val + 1) / 2) ∈ Q.vertexSet :=
      List.mem_toFinset.mpr (Q.walk.getVert_mem_support _)
    rcases hQ.internal_disjoint _ hmem hterminal with hs | ht
    · have he := Q.isPath.getVert_injOn (hbound r) (show 0 ≤ Q.walk.length by omega)
        (by simpa only [Walk.getVert_zero] using hs)
      omega
    · have he := Q.isPath.getVert_injOn (hbound r) (show Q.walk.length ≤ Q.walk.length from le_rfl)
        (by simpa only [Walk.getVert_length] using ht)
      have hr := r.isLt
      omega
  choose f hfproj hflayer using hex
  have hinj : Function.Injective f := by
    intro r s he
    have hp := congrArg projection he
    rw [hfproj r, hfproj s] at hp
    have hidx := Q.isPath.getVert_injOn (hbound r) (hbound s) hp
    have hl := congrArg layer he
    rw [hflayer r, hflayer s] at hl
    have hequiv := decide_eq_decide.mp hl
    apply Fin.ext
    omega
  refine ⟨f, hinj, hfproj, hflayer, ?_⟩
  intro i hi
  by_cases hp : i % 2 = 1
  · apply Or.inr
    constructor
    · rw [hfproj, hfproj]
      congr 1
      change (i + 1) / 2 = (i + 1 + 1) / 2
      omega
    · rw [hflayer, hflayer]
      intro he
      have hh := decide_eq_decide.mp he
      change (i / 2 % 2 = 1 ↔ (i + 1) / 2 % 2 = 1) at hh
      omega
  · apply Or.inl
    constructor
    · rw [hflayer, hflayer]
      apply decide_eq_decide.mpr
      change (i / 2 % 2 = 1 ↔ (i + 1) / 2 % 2 = 1)
      omega
    · rw [hfproj, hfproj]
      have hiQ : (i + 1) / 2 < Q.walk.length := by omega
      have hedge := Q.walk.toSubgraph.adj_sub (Q.walk.toSubgraph_adj_getVert hiQ)
      have he : (i + 1 + 1) / 2 = (i + 1) / 2 + 1 := by omega
      simpa only [he] using hedge

end Erdos73
