/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputCoordinateInterval
import ErdosProblems.Erdos599.HalfwayFiniteRunWalkContactEnumeration

/-!
# Concrete intervals between consecutive compressor contacts

The actual compressor input can be restricted between two consecutive
contact coordinates and recompressed.  The resulting alternating path has
the exact coordinate carrier and no cut vertex in its hammock interior.
If it is wholly contained in the cut, the two coordinates are adjacent;
this is the literal inside-edge case and must not be sent to Claim 2.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

universe u

variable {V : Type u} {D : Digraph V}

abbrev finiteWalk (S : FiniteInput D) : FiniteRunWalk D :=
  S.toFiniteRunWalk

theorem finiteWalk_finalPosition (S : FiniteInput D) :
    S.finiteWalk.finalPosition = S.lastEdge := by
  rw [FiniteRunWalk.finalPosition]
  exact S.toFiniteRunWalk_final_last

theorem breakPosition_lt_succ (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) :
    S.finiteWalk.breakPosition X i.castSucc <
      S.finiteWalk.breakPosition X i.succ :=
  S.finiteWalk.breakPosition_strictMono X Fin.castSucc_lt_succ

noncomputable def breakCoordinateInput (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) : FiniteInput D :=
  S.coordinateInterval
    (S.finiteWalk.breakPosition X i.castSucc)
    (S.finiteWalk.breakPosition X i.succ)
    (S.breakPosition_lt_succ X i)
    (by
      rw [← S.finiteWalk_finalPosition]
      exact S.finiteWalk.breakPosition_le_final X i.succ)

noncomputable def breakIntervalPath (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) : AltPath D :=
  .finite (S.breakCoordinateInput X i).toFiniteRunWalk.toFiniteTrace

@[simp] theorem breakIntervalPath_initial (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) :
    (S.breakIntervalPath X i).initial =
      S.finiteWalk.breakPoint X i.castSucc := by
  unfold breakIntervalPath breakCoordinateInput finiteWalk
  simp only [AltPath.initial, FiniteRunWalk.breakPoint]
  rw [S.coordinateInterval_trace_initial]
  rfl

@[simp] theorem breakIntervalPath_terminal (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) :
    (S.breakIntervalPath X i).terminal? =
      some (S.finiteWalk.breakPoint X i.succ) := by
  unfold breakIntervalPath breakCoordinateInput finiteWalk
  simp only [AltPath.terminal?, FiniteRunWalk.breakPoint]
  rw [S.coordinateInterval_trace_terminal]
  rfl

theorem breakIntervalPath_vertexSet (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) :
    (S.breakIntervalPath X i).vertexSet =
      S.vertex '' Set.Icc
        (S.finiteWalk.breakPosition X i.castSucc)
        (S.finiteWalk.breakPosition X i.succ) := by
  simp only [breakIntervalPath, AltPath.vertexSet]
  exact S.coordinateInterval_trace_vertexSet _ _ _ _

theorem breakIntervalPath_vertexSet_subset (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) :
    (S.breakIntervalPath X i).vertexSet ⊆
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).vertexSet := by
  simp only [breakIntervalPath, AltPath.vertexSet]
  exact S.coordinateInterval_trace_vertexSet_subset _ _ _ _

theorem breakIntervalPath_edgeSet_subset (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) :
    (S.breakIntervalPath X i).edgeSet ⊆
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).edgeSet := by
  simp only [breakIntervalPath, AltPath.edgeSet]
  exact S.coordinateInterval_trace_edgeSet_subset _ _ _ _

theorem breakIntervalPath_hammockInterior_disjoint
    (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) :
    Disjoint
      (Blueprint.hammockInterior
        (S.finiteWalk.breakPoint X i.castSucc)
        (.vertex (S.finiteWalk.breakPoint X i.succ))
        (S.breakIntervalPath X i)) X := by
  rw [Set.disjoint_left]
  intro x hx hxX
  have hxPath := hx.1
  rw [S.breakIntervalPath_vertexSet X i] at hxPath
  obtain ⟨n, hn, hxn⟩ := hxPath
  have hna : n ≠ S.finiteWalk.breakPosition X i.castSucc := by
    intro heq
    apply hx.2
    left
    rw [← hxn, heq]
    rfl
  have hnb : n ≠ S.finiteWalk.breakPosition X i.succ := by
    intro heq
    apply hx.2
    right
    change x = S.finiteWalk.breakPoint X i.succ
    rw [← hxn, heq]
    rfl
  have hleft : S.finiteWalk.breakPosition X i.castSucc < n :=
    lt_of_le_of_ne hn.1 (Ne.symm hna)
  have hright : n < S.finiteWalk.breakPosition X i.succ :=
    lt_of_le_of_ne hn.2 hnb
  apply S.finiteWalk.no_mem_between_consecutive X i (n := n) hleft hright
  change S.vertex n ∈ X
  rw [hxn]
  exact hxX

/-- A consecutive contact interval which is wholly inside the cut consists
of one raw edge.  It is the closed/inside branch, not a Claim-2 segment. -/
theorem breakPosition_succ_eq_of_interval_subset
    (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X))
    (hinside : (S.breakIntervalPath X i).vertexSet ⊆ X) :
    S.finiteWalk.breakPosition X i.succ =
      S.finiteWalk.breakPosition X i.castSucc + 1 := by
  let a := S.finiteWalk.breakPosition X i.castSucc
  let b := S.finiteWalk.breakPosition X i.succ
  have hab : a < b := S.breakPosition_lt_succ X i
  by_contra hne
  have ha1b : a + 1 < b := by omega
  have hvertex : S.vertex (a + 1) ∈
      (S.breakIntervalPath X i).vertexSet := by
    rw [S.breakIntervalPath_vertexSet X i]
    exact ⟨a + 1, ⟨by omega, by omega⟩, rfl⟩
  have hx : S.finiteWalk.vertex (a + 1) ∈ X := by
    exact hinside hvertex
  exact (S.finiteWalk.no_mem_between_consecutive X i (n := a + 1)
    (Nat.lt_succ_self a) ha1b) (by simpa [finiteWalk] using hx)

theorem breakIntervalPath_inside_or_outside
    (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) :
    (S.breakIntervalPath X i).vertexSet ⊆ X ∨
      ¬ (S.breakIntervalPath X i).vertexSet ⊆ X :=
  Classical.em _

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.breakIntervalPath_hammockInterior_disjoint
#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.breakPosition_succ_eq_of_interval_subset
