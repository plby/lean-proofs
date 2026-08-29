/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteBreakCoverage
import ErdosProblems.Erdos599.HalfwayFiniteInputBreakIntervalDirection

/-!
# Exact decomposition by finite consecutive contact intervals
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

universe u

variable {V : Type u} {D : Digraph V}

theorem rawEdge_mem_breakIntervalPath
    (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X))
    (k : Fin S.lastEdge)
    (hleft : S.finiteWalk.breakPosition X i.castSucc ≤ k.1)
    (hright : k.1 < S.finiteWalk.breakPosition X i.succ) :
    S.rawEdge k ∈ (S.breakIntervalPath X i).edgeSet := by
  let a := S.finiteWalk.breakPosition X i.castSucc
  let b := S.finiteWalk.breakPosition X i.succ
  have hab : a < b := S.breakPosition_lt_succ X i
  have hb : b ≤ S.lastEdge := by
    rw [← S.finiteWalk_finalPosition]
    exact S.finiteWalk.breakPosition_le_final X i.succ
  have hoff : k.1 - a < b - a := by omega
  let j : Fin (S.coordinateInterval a b hab hb).lastEdge :=
    ⟨k.1 - a, by simpa only [coordinateInterval_lastEdge] using hoff⟩
  have hj := (S.coordinateInterval a b hab hb).rawEdge_mem_toFiniteTrace j
  change (S.coordinateInterval a b hab hb).rawEdge j ∈
    (S.breakIntervalPath X i).edgeSet at hj
  rw [S.coordinateInterval_rawEdge a b hab hb j] at hj
  have hindex : a + j.1 = k.1 := Nat.add_sub_of_le hleft
  have hfin : (⟨a + j.1, by omega⟩ : Fin S.lastEdge) = k := Fin.ext hindex
  simpa only [hfin] using hj

theorem breakIntervals_vertexSet_exact (S : FiniteInput D) (X : Set V) :
    (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).vertexSet =
      Set.range (S.finiteWalk.breakPoint X) ∪
        ⋃ i : Fin (S.finiteWalk.breakCount X),
          (S.breakIntervalPath X i).vertexSet := by
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ S.toFiniteRunWalk.toFiniteTrace.vertexSet at hx
    rw [S.toFiniteTrace_vertexSet] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    rcases hn with ⟨hn0, hnle⟩
    by_cases hnfinal : n = S.lastEdge
    · left
      let j : Fin (S.finiteWalk.breakCount X + 1) :=
        ⟨S.finiteWalk.breakCount X, Nat.lt_succ_self _⟩
      refine ⟨j, ?_⟩
      rw [FiniteRunWalk.breakPoint, S.finiteWalk.breakPosition_last X,
        S.finiteWalk_finalPosition, hnfinal]
      rfl
    · right
      have hnlt : n < S.finiteWalk.finalPosition := by
        rw [S.finiteWalk_finalPosition]
        exact lt_of_le_of_ne hnle hnfinal
      obtain ⟨i, hleft, hright⟩ :=
        S.finiteWalk.exists_consecutiveBreak_interval X hnlt
      simp only [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      rw [S.breakIntervalPath_vertexSet X i]
      exact ⟨n, ⟨hleft, hright.le⟩, rfl⟩
  · rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact S.toFiniteRunWalk.vertex_mem_toFiniteTrace
        (S.finiteWalk.breakPosition X i)
        (S.finiteWalk.breakPosition_le_final X i)
    · simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hx⟩ := hx
      exact S.breakIntervalPath_vertexSet_subset X i hx

theorem breakIntervals_edgeSet_exact (S : FiniteInput D) (X : Set V) :
    (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).edgeSet =
      ⋃ i : Fin (S.finiteWalk.breakCount X),
        (S.breakIntervalPath X i).edgeSet := by
  apply Set.Subset.antisymm
  · intro e he
    change e ∈ S.toFiniteRunWalk.toFiniteTrace.edgeSet at he
    rw [S.mem_toFiniteTrace_edgeSet_iff] at he
    obtain ⟨k, rfl⟩ := he
    have hklt : k.1 < S.finiteWalk.finalPosition := by
      rw [S.finiteWalk_finalPosition]
      exact k.2
    obtain ⟨i, hleft, hright⟩ :=
      S.finiteWalk.exists_consecutiveBreak_interval X hklt
    exact Set.mem_iUnion.2
      ⟨i, S.rawEdge_mem_breakIntervalPath X i k hleft hright⟩
  · intro e he
    simp only [Set.mem_iUnion] at he
    obtain ⟨i, he⟩ := he
    exact S.breakIntervalPath_edgeSet_subset X i he

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.breakIntervals_vertexSet_exact
#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.breakIntervals_edgeSet_exact
