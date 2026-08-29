/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.MarkedRayFiniteEdgeStability
import ErdosProblems.Erdos599.SafeSwitchingAssembly
import ErdosProblems.Erdos599.AlternatingDichotomy

/-!
# Finite forward skeletons to a terminal or a marked edge

Starting at any carrier vertex of a warp, follow its owner until either the
owner terminates or the next marked edge begins.  On a finite owner this is
a first-hit truncation.  On a ray, infinitely many marked edges guarantee a
least marked index after the starting occurrence.

The resulting path does not traverse the selected marked edge: its finish
is the edge's tail.  Consequently every traversed edge is unmarked.
-/

noncomputable section

namespace Erdos599.DWeb

open Set _root_.Erdos599.DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

private theorem finite_Iio_nat (k : ℕ) : (Set.Iio k : Set ℕ).Finite := by
  induction k with
  | zero => simp
  | succ k ih =>
      have heq : (Set.Iio (k + 1) : Set ℕ) = insert k (Set.Iio k) := by
        ext n
        simp only [Set.mem_Iio, Set.mem_insert_iff]
        omega
      rw [heq]
      exact ih.insert k

/-- Every carrier vertex has a finite forward skeleton which either reaches
the warp frontier or stops at the tail of a marked warp edge. -/
theorem IsWarp.exists_unmarkedForwardPath_to_terminal_or_markedTail
    {W : Set Gamma.DPath} (_hW : Gamma.IsWarp W)
    {marked : V → V → Prop}
    (hmarked : Gamma.InfinitelyManyMarkedEdges W marked)
    {s : V} (hs : s ∈ Gamma.vertexSet W) :
    ∃ p : FinitePath Gamma.graph,
      p.start = s ∧ p.edgeSet ⊆ familyEdges W ∧
      (∀ e ∈ p.edgeSet, ¬marked e.1 e.2) ∧
      (p.finish ∈ Gamma.terminalFrontier W ∨
        ∃ y, (p.finish, y) ∈ familyEdges W ∧ marked p.finish y) := by
  classical
  obtain ⟨owner, hownerW, hsOwner⟩ := hs
  rcases owner with q | r
  · let M : Set V :=
      {x | ∃ y, (x, y) ∈ q.edgeSet ∧ marked x y} ∪ {q.finish}
    have hmeet : (q.suffixFrom s hsOwner).walk.Meets M := by
      refine ⟨q.finish, ?_, Or.inr (Set.mem_singleton q.finish)⟩
      change q.finish ∈ (q.suffixFrom s hsOwner).support
      exact (q.suffixFrom s hsOwner).finish_mem_support
    let p := q.firstHitAfter s hsOwner M hmeet
    have hpEdgesOwner : p.edgeSet ⊆ q.edgeSet :=
      q.firstHitAfter_edgeSet_subset s hsOwner M hmeet
    have hpEdges : p.edgeSet ⊆ familyEdges W := by
      intro e he
      exact Set.mem_iUnion.mpr ⟨Sum.inl q,
        Set.mem_iUnion.mpr ⟨hownerW, hpEdgesOwner he⟩⟩
    have hpUnmarked : ∀ e ∈ p.edgeSet, ¬marked e.1 e.2 := by
      intro e he hmark
      have htailOutside := q.firstHitAfter_no_mem_before s hsOwner M hmeet
        (Walk.edge_fst_mem_support_dropLast p.walk he)
      apply htailOutside
      exact Or.inl ⟨e.2, hpEdgesOwner he, hmark⟩
    have hpFinish := q.firstHitAfter_finish_mem s hsOwner M hmeet
    refine ⟨p, q.firstHitAfter_start s hsOwner M hmeet, hpEdges,
      hpUnmarked, ?_⟩
    rcases hpFinish with hpMarked | hpTerminal
    · obtain ⟨y, hqy, hmy⟩ := hpMarked
      exact Or.inr ⟨y, Set.mem_iUnion.mpr ⟨Sum.inl q,
        Set.mem_iUnion.mpr ⟨hownerW, hqy⟩⟩, hmy⟩
    · have hpq : p.finish = q.finish := Set.mem_singleton_iff.mp hpTerminal
      exact Or.inl ⟨Sum.inl q, hownerW, by
        change some q.finish = some p.finish
        rw [hpq]⟩
  · obtain ⟨i, hi⟩ := hsOwner
    have hex : ∃ m : ℕ, marked (r (i + m)) (r (i + m + 1)) := by
      by_contra hnone
      push Not at hnone
      have hsubset : {n : ℕ | marked (r n) (r (n + 1))} ⊆ Set.Iio i := by
        intro n hn
        by_contra hni
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hni)
        exact hnone m (by simpa [Nat.add_assoc] using hn)
      exact (hmarked r hownerW) ((finite_Iio_nat i).subset hsubset)
    let m := Nat.find hex
    have hm : marked (r (i + m)) (r (i + m + 1)) := Nat.find_spec hex
    let p := SwitchingCore.raySegmentPath r i m
    have hpEdges : p.edgeSet ⊆ familyEdges W := by
      intro e he
      rw [SwitchingCore.raySegmentPath_edgeSet] at he
      obtain ⟨k, hk, rfl⟩ := he
      exact Set.mem_iUnion.mpr ⟨Sum.inr r,
        Set.mem_iUnion.mpr ⟨hownerW, ⟨i + k, by simp [Nat.add_assoc]⟩⟩⟩
    have hpUnmarked : ∀ e ∈ p.edgeSet, ¬marked e.1 e.2 := by
      intro e he
      rw [SwitchingCore.raySegmentPath_edgeSet] at he
      obtain ⟨k, hk, rfl⟩ := he
      apply Nat.find_min hex
      simpa only [m] using hk
    refine ⟨p, ?_, hpEdges, hpUnmarked, Or.inr ?_⟩
    · change r i = s
      exact hi
    · refine ⟨r (i + m + 1), ?_, ?_⟩
      · rw [SwitchingCore.raySegmentPath_finish]
        exact Set.mem_iUnion.mpr ⟨Sum.inr r,
          Set.mem_iUnion.mpr ⟨hownerW, ⟨i + m, by simp [Nat.add_assoc]⟩⟩⟩
      · change marked (r (i + m)) (r (i + m + 1))
        exact hm

#print axioms IsWarp.exists_unmarkedForwardPath_to_terminal_or_markedTail

end Erdos599.DWeb
