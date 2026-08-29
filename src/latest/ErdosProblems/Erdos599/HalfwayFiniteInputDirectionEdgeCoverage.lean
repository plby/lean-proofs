/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputCoordinateInterval

/-!
# Direction-preserving edge coverage of finite compression

Every edge of a compressed link is the raw edge at a coordinate with that
link's colour, and every raw edge occurs in the corresponding directed link.
Consequently coordinate restriction preserves forward and backward edge
classes separately, not only their unoriented union.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

universe u

variable {V : Type u} {D : Digraph V}

private theorem exists_run_offset_direction (runs : List (List Direction))
    {n : Nat} (hn : n < runs.flatten.length) :
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
          List.sum_cons]
        change n = r.length + runLower runs i + k
        have hnGe : r.length ≤ n := Nat.le_of_not_gt hnr
        omega

theorem mem_directionEdges_exists_rawEdge (S : FiniteInput D)
    (d : Direction) {e : V × V}
    (he : e ∈ (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).directionEdges d) :
    ∃ k : Fin S.lastEdge, S.colour k = d ∧ e = S.rawEdge k := by
  simp only [AltPath.directionEdges, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at he
  obtain ⟨l, ⟨i, rfl⟩, hdir, he⟩ := he
  have hrun : S.runDirection (S.runIndex i) = d :=
    (S.toFiniteRunWalk_run_direction i).symm.trans hdir
  change e ∈ (S.projectedRun (S.runIndex i)).link.path.edgeSet at he
  cases d with
  | forward =>
      rw [S.projectedRun_edgeSet_eq_forward (S.runIndex i) hrun] at he
      obtain ⟨k, hk, rfl⟩ := he
      let n : Fin S.lastEdge :=
        ⟨runLower S.runs (S.runIndex i) + k, by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge (S.runIndex i))⟩
      have hc : S.colour n = .forward :=
        (S.colour_run_offset (S.runIndex i) hk).trans hrun
      exact ⟨n, hc, by simp [rawEdge, hc, n]⟩
  | backward =>
      rw [S.projectedRun_edgeSet_eq_backward (S.runIndex i) hrun] at he
      obtain ⟨k, hk, rfl⟩ := he
      let n : Fin S.lastEdge :=
        ⟨runLower S.runs (S.runIndex i) + k, by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge (S.runIndex i))⟩
      have hc : S.colour n = .backward :=
        (S.colour_run_offset (S.runIndex i) hk).trans hrun
      exact ⟨n, hc, by simp [rawEdge, hc, n]⟩

theorem rawEdge_mem_directionEdges (S : FiniteInput D)
    (k : Fin S.lastEdge) :
    S.rawEdge k ∈
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).directionEdges
        (S.colour k) := by
  have hk : k.1 < S.runs.flatten.length := by
    rw [S.runs_flatten, S.colours_length]
    exact k.2
  obtain ⟨i, n, hn, hkn⟩ := exists_run_offset_direction S.runs hk
  let j : Fin (S.runs.length - 1 + 1) := Fin.cast S.runCount_eq.symm i
  have hji : S.runIndex j = i := Fin.ext rfl
  have hc : S.colour k = S.runDirection i := by
    have hc' := S.colour_run_offset i hn
    have hkfin :
        (⟨runLower S.runs i.1 + n, by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hn _)
            (S.runUpper_le_lastEdge i)⟩ : Fin S.lastEdge) = k := by
      apply Fin.ext
      exact hkn.symm
    rw [← hkfin]
    exact hc'
  simp only [AltPath.directionEdges, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range]
  refine ⟨(S.projectedRun i).link, ⟨j, ?_⟩, ?_, ?_⟩
  · change (S.projectedRun (S.runIndex j)).link = (S.projectedRun i).link
    rw [hji]
  · rw [S.projectedRun_direction, ← hc]
  · cases hkcolour : S.colour k with
    | forward =>
        have hrun : S.runDirection i = .forward := hc.symm.trans hkcolour
        rw [S.projectedRun_edgeSet_eq_forward i hrun]
        refine ⟨n, hn, ?_⟩
        simp [rawEdge, hkcolour, hkn]
    | backward =>
        have hrun : S.runDirection i = .backward := hc.symm.trans hkcolour
        rw [S.projectedRun_edgeSet_eq_backward i hrun]
        refine ⟨n, hn, ?_⟩
        simp [rawEdge, hkcolour, hkn]

theorem coordinateInterval_directionEdges_subset (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) (d : Direction) :
    (AltPath.finite
      (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace
      ).directionEdges d ⊆
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).directionEdges d := by
  intro e he
  obtain ⟨k, hkcolour, rfl⟩ :=
    (S.coordinateInterval a b hab hb).mem_directionEdges_exists_rawEdge d he
  rw [S.coordinateInterval_rawEdge a b hab hb k]
  let j : Fin S.lastEdge := ⟨a + k.1, by
    have hkbase : k.1 < b - a := by
      simpa only [coordinateInterval_lastEdge] using k.2
    omega⟩
  have hjcolour : S.colour j = d := by
    simpa [coordinateInterval, j] using hkcolour
  simpa only [hjcolour] using S.rawEdge_mem_directionEdges j

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.mem_directionEdges_exists_rawEdge
#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.coordinateInterval_directionEdges_subset
