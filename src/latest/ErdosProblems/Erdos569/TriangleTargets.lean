/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos569.Triangle

/-! # Cycle targets in the triangle bound -/

open scoped SimpleGraph

namespace Erdos569

open Erdos79 Erdos570

theorem cycleCode_degree {k : ℕ} (hk : 3 ≤ k) (v : Fin k) :
    (SimpleGraph.cycleGraph k).degree v = 2 := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 3 := ⟨k - 3, by omega⟩
  exact SimpleGraph.cycleGraph_degree_three_le

theorem cycleCode_noIsolated {k : ℕ} (hk : 3 ≤ k) :
    NoIsolated (cycleCode k) := by
  classical
  change ∀ v : Fin k, ¬(SimpleGraph.cycleGraph k).IsIsolated v
  intro v
  apply ((SimpleGraph.cycleGraph k).degree_pos v).mp
  rw [cycleCode_degree hk]
  decide

theorem cycleCode_edgeCount {k : ℕ} (hk : 3 ≤ k) :
    (cycleCode k).edgeCount = k := by
  change Nat.card (SimpleGraph.cycleGraph k).edgeSet = k
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  have hs := (SimpleGraph.cycleGraph k).sum_degrees_eq_twice_card_edges
  simp only [cycleCode_degree hk, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hs
  omega

theorem ramseyAt_cycle_three_vertices {k : ℕ} (hk : 3 ≤ k)
    (H : GraphCode) (hn : H.vertexCount ≤ 3) :
    RamseyAt (cycleCode k) H (2 * k + 1) := by
  have hcontain : H.graph ⊑ (cycleCode 3).graph := by
    simpa [cycleCode, completeCode, SimpleGraph.cycleGraph_three_eq_top] using
      isContained_completeCode_of_vertexCount_le (H := H) hn
  apply RamseyAt.mono_right hcontain
  apply ramseyAt_of_graphRamseyNumber_le
  rw [graphRamseyNumber_comm]
  have ht := graphRamseyNumber_le_of_ramseyAt
    (ramseyAt_triangle (cycleCode k) (cycleCode_noIsolated hk))
  rwa [cycleCode_edgeCount hk] at ht

end Erdos569
