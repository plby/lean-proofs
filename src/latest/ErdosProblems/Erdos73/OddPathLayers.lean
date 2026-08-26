import ErdosProblems.Erdos73.OddPathAugmenting
import ErdosProblems.Erdos73.MatchingPathParity

/-! The layer changes on a doubled-graph augmenting path give its length modulo four. -/

namespace Erdos73

open SimpleGraph Finset Erdos556 OddPathVertex
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : Finset V}
variable {P : GraphPath (oddPathAuxiliary G A)}

theorem oddPathAugmenting_layer_getVert
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P)
    (i : ℕ) (hi : i ≤ P.walk.length) :
    layer (P.walk.getVert i) = decide ((i / 2) % 2 = 1) := by
  induction i with
  | zero =>
    rw [Walk.getVert_zero,
      eq_original_of_terminal (oddPathAugmenting_source_terminal hP)]
    rfl
  | succ i ih =>
    have hil : i < P.walk.length := by omega
    have hi' := ih (by omega : i ≤ P.walk.length)
    have he := hP.edge_mem_iff_odd_index (oddPathBaseMatching_isMatching G A) i hil
    have hadj := P.walk.toSubgraph.adj_sub (P.walk.toSubgraph_adj_getVert hil)
    by_cases hp : i % 2 = 1
    · have hm := (mem_oddPathBaseMatching_iff _ _).mp (he.mpr hp)
      change layer (P.walk.getVert (i + 1)) = decide (((i + 1) / 2) % 2 = 1)
      rw [hm.1, layer_mate _ hm.2, hi', ← decide_not]
      apply decide_eq_decide.mpr
      omega
    · have hn : s(P.walk.getVert i, P.walk.getVert (i + 1)) ∉ oddPathBaseMatching A :=
        fun hm => hp (he.mp hm)
      have hl := (oddPathAuxiliary_adj_of_not_matching hadj hn).1
      change layer (P.walk.getVert (i + 1)) = decide (((i + 1) / 2) % 2 = 1)
      rw [← hl, hi']
      apply decide_eq_decide.mpr
      omega

theorem oddPathAugmenting_length_mod_four
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P) :
    ∃ t : ℕ, P.walk.length = 4 * t + 1 := by
  have ho := hP.odd_length (oddPathBaseMatching_isMatching G A)
  have hl := oddPathAugmenting_layer_getVert hP P.walk.length le_rfl
  rw [Walk.getVert_length] at hl
  have htarget : layer P.target = false :=
    congrArg layer (eq_original_of_terminal (oddPathAugmenting_target_terminal hP))
  rw [htarget] at hl
  have hp : (P.walk.length / 2) % 2 ≠ 1 := by
    intro hh
    rw [hh] at hl
    exact Bool.false_ne_true hl
  rw [Nat.odd_iff] at ho
  refine ⟨P.walk.length / 4, ?_⟩
  omega

end Erdos73
