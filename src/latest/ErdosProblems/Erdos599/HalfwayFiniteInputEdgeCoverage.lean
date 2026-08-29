/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputForwardSegment

/-!
# Every raw compressor edge occurs in its compressed finite trace

The colour blocks partition the raw edge coordinates.  Selecting the first
block whose upper boundary is past `k` gives the unique compressed run
containing that edge and hence its literal occurrence in the output trace.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

universe u

variable {V : Type u} {D : Digraph V}

private theorem exists_run_offset (runs : List (List Direction)) {n : Nat}
    (hn : n < runs.flatten.length) :
    ∃ (i : Fin runs.length) (k : Nat), k < (runs.get i).length ∧
      n = runLower runs i + k := by
  induction runs generalizing n with
  | nil => simp at hn
  | cons r runs ih =>
      by_cases hnr : n < r.length
      · exact ⟨⟨0, by simp⟩, n, by simpa using hnr, by simp [runLower]⟩
      · have hnTail : n - r.length < runs.flatten.length := by
          have hlen : n < r.length + runs.flatten.length := by
            simpa only [List.flatten_cons, List.length_append] using hn
          omega
        obtain ⟨i, k, hk, hnk⟩ := ih hnTail
        refine ⟨⟨i.1 + 1, by simp⟩, k, by simpa using hk, ?_⟩
        simp only [runLower, List.take_succ_cons, List.map_cons,
          List.sum_cons, List.get_cons_succ]
        change n = r.length + runLower runs i + k
        have hnGe : r.length ≤ n := Nat.le_of_not_gt hnr
        omega

/-- The literal raw directed edge at coordinate `k`. -/
def rawEdge (S : FiniteInput D) (k : Fin S.lastEdge) : V × V :=
  match S.colour k with
  | .forward => (S.vertex k.1, S.vertex (k.1 + 1))
  | .backward => (S.vertex (k.1 + 1), S.vertex k.1)

theorem rawEdge_mem_toFiniteTrace (S : FiniteInput D)
    (k : Fin S.lastEdge) :
    S.rawEdge k ∈ S.toFiniteRunWalk.toFiniteTrace.edgeSet := by
  have hk : k.1 < S.runs.flatten.length := by
    rw [S.runs_flatten, S.colours_length]
    exact k.2
  obtain ⟨i, n, hn, hkn⟩ := exists_run_offset S.runs hk
  rw [S.toFiniteTrace_edgeSet]
  simp only [orientedEdgeSet, Set.mem_iUnion]
  refine ⟨i, ?_⟩
  by_cases hd : S.runDirection i = .forward
  · rw [if_pos hd]
    refine ⟨n, hn, ?_⟩
    have hc : S.colour k = .forward := by
      have hc' := (S.colour_run_offset i hn).trans hd
      have hkfin :
          (⟨runLower S.runs i.1 + n, by
            exact lt_of_lt_of_le (Nat.add_lt_add_left hn _)
              (S.runUpper_le_lastEdge i)⟩ : Fin S.lastEdge) = k := by
        apply Fin.ext
        exact hkn.symm
      rw [← hkfin]
      exact hc'
    simp [rawEdge, hc, hkn]
  · rw [if_neg hd]
    refine ⟨n, hn, ?_⟩
    have hb : S.runDirection i = .backward := by
      cases h : S.runDirection i
      · exact (hd h).elim
      · rfl
    have hc : S.colour k = .backward := by
      have hc' := (S.colour_run_offset i hn).trans hb
      have hkfin :
          (⟨runLower S.runs i.1 + n, by
            exact lt_of_lt_of_le (Nat.add_lt_add_left hn _)
              (S.runUpper_le_lastEdge i)⟩ : Fin S.lastEdge) = k := by
        apply Fin.ext
        exact hkn.symm
      rw [← hkfin]
      exact hc'
    simp [rawEdge, hc, hkn]

theorem mem_toFiniteTrace_edgeSet_iff (S : FiniteInput D) {e : V × V} :
    e ∈ S.toFiniteRunWalk.toFiniteTrace.edgeSet ↔
      ∃ k : Fin S.lastEdge, e = S.rawEdge k := by
  constructor
  · rw [S.toFiniteTrace_edgeSet]
    simp only [orientedEdgeSet, Set.mem_iUnion]
    rintro ⟨i, he⟩
    by_cases hdir : S.runDirection i = .forward
    · rw [if_pos hdir] at he
      rcases he with ⟨k, hk, rfl⟩
      let n : Fin S.lastEdge :=
        ⟨runLower S.runs i.1 + k, by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge i)⟩
      refine ⟨n, ?_⟩
      have hcolour := (S.colour_run_offset i hk).trans hdir
      simp [rawEdge, n, hcolour]
    · have hback : S.runDirection i = .backward := by
        cases h : S.runDirection i
        · exact (hdir h).elim
        · rfl
      rw [if_neg hdir] at he
      rcases he with ⟨k, hk, rfl⟩
      let n : Fin S.lastEdge :=
        ⟨runLower S.runs i.1 + k, by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge i)⟩
      refine ⟨n, ?_⟩
      have hcolour := (S.colour_run_offset i hk).trans hback
      simp [rawEdge, n, hcolour]
  · rintro ⟨k, rfl⟩
    exact S.rawEdge_mem_toFiniteTrace k

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.rawEdge_mem_toFiniteTrace
#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.mem_toFiniteTrace_edgeSet_iff
