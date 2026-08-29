/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputEdgeCoverage
import ErdosProblems.Erdos599.HalfwayFiniteRunWalkPositionCoverage

/-!
# Restricting a concrete finite compressor input to a coordinate interval

The restriction retains the literal vertex stream, colours, and directed
raw edges.  Recompressing it therefore constructs the actual alternating
subtrace between two consecutive contact coordinates.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

universe u

variable {V : Type u} {D : Digraph V}

noncomputable def coordinateInterval (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) : FiniteInput D where
  lastEdge := b - a
  lastEdge_pos := Nat.sub_pos_of_lt hab
  vertex n := S.vertex (a + n)
  vertex_injective_on := by
    intro i j hi hj hij
    apply Nat.add_left_cancel
    exact S.vertex_injective_on (by omega) (by omega) hij
  colour k := S.colour ⟨a + k.1, by omega⟩
  forward_adj := by
    intro n hn
    simpa only [Nat.add_assoc] using
      S.forward_adj ⟨a + n.1, by omega⟩ hn
  backward_adj := by
    intro n hn
    simpa only [Nat.add_assoc] using
      S.backward_adj ⟨a + n.1, by omega⟩ hn

@[simp] theorem coordinateInterval_vertex (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) (n : Nat) :
    (S.coordinateInterval a b hab hb).vertex n = S.vertex (a + n) := rfl

@[simp] theorem coordinateInterval_lastEdge (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) :
    (S.coordinateInterval a b hab hb).lastEdge = b - a := rfl

theorem coordinateInterval_rawEdge (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (k : Fin (S.coordinateInterval a b hab hb).lastEdge) :
    (S.coordinateInterval a b hab hb).rawEdge k =
      S.rawEdge ⟨a + k.1, by
        have hkbase : k.1 < b - a := by
          simpa only [coordinateInterval_lastEdge] using k.2
        omega⟩ := by
  let j : Fin S.lastEdge := ⟨a + k.1, by
    have hkbase : k.1 < b - a := by
      simpa only [coordinateInterval_lastEdge] using k.2
    omega⟩
  change (S.coordinateInterval a b hab hb).rawEdge k = S.rawEdge j
  cases hcolour : S.colour j <;>
    simp [rawEdge, coordinateInterval, j, hcolour, Nat.add_assoc]

@[simp] theorem coordinateInterval_trace_initial (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) :
    (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace.initial =
      S.vertex a := by
  rw [(S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace_initial]
  rfl

@[simp] theorem coordinateInterval_trace_terminal (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) :
    (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace.terminal =
      S.vertex b := by
  rw [(S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace_terminal]
  rw [(S.coordinateInterval a b hab hb).toFiniteRunWalk_final_last]
  change S.vertex (a + (b - a)) = S.vertex b
  rw [Nat.add_sub_of_le hab.le]

theorem coordinateInterval_trace_edgeSet_subset (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) :
    (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace.edgeSet ⊆
      S.toFiniteRunWalk.toFiniteTrace.edgeSet := by
  intro e he
  rw [(S.coordinateInterval a b hab hb).mem_toFiniteTrace_edgeSet_iff] at he
  obtain ⟨k, rfl⟩ := he
  rw [S.coordinateInterval_rawEdge a b hab hb k]
  exact S.rawEdge_mem_toFiniteTrace _

/-- Exact carrier of the compressed trace of any concrete finite input. -/
theorem toFiniteTrace_vertexSet (S : FiniteInput D) :
    S.toFiniteRunWalk.toFiniteTrace.vertexSet =
      S.vertex '' Set.Icc 0 S.lastEdge := by
  apply Set.Subset.antisymm
  · rintro x hx
    simp only [FiniteTrace.vertexSet, Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    change x ∈ (S.toFiniteRunWalk.run i).link.path.support at hxi
    rw [S.toFiniteRunWalk_run_support i] at hxi
    obtain ⟨n, hn, rfl⟩ := hxi
    have hil : i.1 < S.runs.length := by
      have hil' : i.1 < S.toFiniteRunWalk.lastIndex + 1 := by
        simpa only [FiniteRunWalk.toFiniteTrace] using i.2
      change i.1 < S.runs.length - 1 + 1 at hil'
      rw [S.runCount_eq] at hil'
      exact hil'
    have hi := S.runUpper_le_lastEdge (⟨i.1, hil⟩ : Fin S.runs.length)
    rw [← runLower_succ S.runs hil] at hi
    exact ⟨n, ⟨Nat.zero_le _, hn.2.trans hi⟩, rfl⟩
  · rintro x ⟨n, hn, rfl⟩
    have hfinal : n ≤ S.toFiniteRunWalk.finalPosition := by
      simpa only [FiniteRunWalk.finalPosition,
        S.toFiniteRunWalk_final_last] using hn.2
    exact S.toFiniteRunWalk.vertex_mem_toFiniteTrace n hfinal

theorem coordinateInterval_trace_vertexSet (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) :
    (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace.vertexSet =
      S.vertex '' Set.Icc a b := by
  rw [(S.coordinateInterval a b hab hb).toFiniteTrace_vertexSet]
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    rcases hn with ⟨hn0, hnb⟩
    have hnb' : n ≤ b - a := by
      simpa only [coordinateInterval_lastEdge] using hnb
    exact ⟨a + n, ⟨Nat.le_add_right _ _, by omega⟩, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n - a, ⟨Nat.zero_le _, ?_⟩, ?_⟩
    · exact Nat.sub_le_sub_right hn.2 a
    · simp only [coordinateInterval_vertex]
      rw [Nat.add_sub_of_le hn.1]

theorem coordinateInterval_trace_vertexSet_subset (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) :
    (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace.vertexSet ⊆
      S.toFiniteRunWalk.toFiniteTrace.vertexSet := by
  rw [S.coordinateInterval_trace_vertexSet a b hab hb,
    S.toFiniteTrace_vertexSet]
  rintro x ⟨n, hn, rfl⟩
  exact ⟨n, ⟨Nat.zero_le _, hn.2.trans hb⟩, rfl⟩

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.coordinateInterval_trace_edgeSet_subset
#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.coordinateInterval_trace_vertexSet
