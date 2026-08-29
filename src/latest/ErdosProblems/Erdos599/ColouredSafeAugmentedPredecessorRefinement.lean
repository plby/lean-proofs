/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeAugmentedRealReach
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Original-source predecessor refinement in an arbitrary augmented web

The original and augmented webs are explicit parameters. A strong splice
can replace an incoming edge at the old head by a finite
real path starting at a newly touched original source. This is different
from subdividing the old edge, so that third alternative is explicit.
The invariant composes under monotone carriers and real edges. The concrete
one- and two-port criteria use actual inserted finite families.
-/

namespace Erdos599.ColouredSafeAugmentedRealReach

open Set Cardinal DirectedPath Alternating ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma D : DWeb V}

def SourcePredecessorRefines (Gamma D : DWeb V) (W U : Set D.DPath) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ D.vertexSet W →
    (y, x) ∈ familyEdges U →
      (y, x) ∈ familyEdges W ∨
      (∃ z, (z, x) ∈ familyEdges W ∧ RealReach Gamma D U z x) ∨
      (∃ a ∈ Gamma.source, RealReach Gamma D U a x)

theorem SourcePredecessorRefines.refl (W : Set D.DPath) :
    SourcePredecessorRefines Gamma D W W := fun _ _ _ he ↦ Or.inl he

/-- An ordinary edge-preserving extension retaining old initials cannot
add a new predecessor at an old vertex. -/
theorem familyEdges_into_oldVertex_of_edge_initial_extension
    {W U : Set D.DPath}
    (hW : D.IsWarp W)
    (hU : D.IsWarp U)
    (hE : familyEdges W ⊆ familyEdges U)
    (hI : D.initialSet W ⊆
      D.initialSet U)
    {x y : V} (hx : x ∈ D.vertexSet W)
    (hyx : (y, x) ∈ familyEdges U) : (y, x) ∈ familyEdges W := by
  classical
  by_cases hin : HasIncoming (familyEdges W) x
  · obtain ⟨z, hzx⟩ := hin
    have hyz : y = z := (IsWarp.familyEdges_biUnique hU).1 hyx (hE hzx)
    exact hyz.symm ▸ hzx
  · have hxI : x ∈ D.initialSet W := by
      rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hW]
      exact ⟨hx, hin⟩
    have hxU := hI hxI
    rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hU] at hxU
    exact False.elim (hxU.2 ⟨y, hyx⟩)

/-- The incoming-edge invariant follows from the actual ordinary-extension
data; it is not an additional hypothesis on the moving successor. -/
theorem sourcePredecessorRefines_of_edge_initial_extension
    {W U : Set D.DPath}
    (hW : D.IsWarp W)
    (hU : D.IsWarp U)
    (hE : familyEdges W ⊆ familyEdges U)
    (hI : D.initialSet W ⊆
      D.initialSet U) : SourcePredecessorRefines Gamma D W U :=
  fun _ _ hx he ↦ Or.inl
    (familyEdges_into_oldVertex_of_edge_initial_extension hW hU hE hI hx he)

theorem SourcePredecessorRefines.trans
    {W U R : Set D.DPath}
    (hWU : SourcePredecessorRefines Gamma D W U) (hUR : SourcePredecessorRefines Gamma D U R)
    (hWUvertices : D.vertexSet W ⊆
      D.vertexSet U)
    (hURvertices : D.vertexSet U ⊆
      D.vertexSet R)
    (hURreal : RealEdges (Gamma := D) Gamma.graph.Adj U ⊆
      RealEdges (Gamma := D) Gamma.graph.Adj R) :
    SourcePredecessorRefines Gamma D W R := by
  intro x y hx hyx
  rcases hUR (hWUvertices hx) hyx with hold | ⟨z, hzx, hzR⟩ | hsource
  · rcases hWU hx hold with hold | ⟨z, hzx, hzU⟩ | ⟨a, ha, haU⟩
    · exact Or.inl hold
    · exact Or.inr (Or.inl ⟨z, hzx, hzU.mono hURvertices hURreal⟩)
    · exact Or.inr (Or.inr ⟨a, ha, haU.mono hURvertices hURreal⟩)
  · rcases hWU hx hzx with hold | ⟨w, hwx, hwU⟩ | ⟨a, ha, haU⟩
    · exact Or.inr (Or.inl ⟨z, hold, hzR⟩)
    · exact Or.inr (Or.inl ⟨w, hwx, hwU.mono hURvertices hURreal⟩)
    · exact Or.inr (Or.inr ⟨a, ha, haU.mono hURvertices hURreal⟩)
  · exact Or.inr (Or.inr hsource)

/-- A finite inserted owner gives a literal real prefix to each of its
vertices, all in the same output warp. -/
theorem realReach_of_inserted_finitePath
    {U : Set D.DPath} (p : FinitePath Gamma.graph)
    (hpV : p.support ⊆ D.vertexSet U)
    (hpE : p.edgeSet ⊆ familyEdges U) {x : V} (hx : x ∈ p.support) :
    RealReach Gamma D U p.start x := by
  refine ⟨hpV p.start_mem_support, ?_⟩
  exact Relation.ReflTransGen.mono
    (fun _ _ he ↦ ⟨hpE he, p.edgeSet_subset_adj he⟩) _ _
    (GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      p Set.Subset.rfl hx)

/-- Concrete two-port criterion. Every genuinely new incoming edge at an
old vertex belongs to a finite inserted owner rooted at the cut tail or an
original source. Its head must be the old cut head. -/
theorem sourcePredecessorRefines_of_twoPortInsertion
    {W U : Set D.DPath} {P : Set Gamma.DPath} {s t : V}
    (hP : Gamma.IsWarp P) (hPfinite : Gamma.HasFiniteCharacter P)
    (hsP : s ∈ Gamma.initialSet P)
    (hroots : Gamma.initialSet P ⊆ Gamma.source ∪ {s})
    (hcut : (s, t) ∈ familyEdges W)
    (hcap : Gamma.vertexSet P ∩ D.vertexSet W ⊆ {s, t})
    (hUE : familyEdges U ⊆ familyEdges W ∪ familyEdges P)
    (hPE : familyEdges P ⊆ familyEdges U)
    (hPV : Gamma.vertexSet P ⊆ D.vertexSet U) :
    SourcePredecessorRefines Gamma D W U := by
  intro x y hx hyx
  rcases hUE hyx with hold | hnew
  · exact Or.inl hold
  have hxP : x ∈ Gamma.vertexSet P := (familyEdges_subset_vertexSet_prod P hnew).2
  rcases Set.mem_insert_iff.mp (hcap ⟨hxP, hx⟩) with hxs | hxt
  · have hno : ¬HasIncoming (familyEdges P) s := by
      rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hP] at hsP
      exact hsP.2
    exact False.elim (hno ⟨y, hxs ▸ hnew⟩)
  · have hxt' : x = t := Set.mem_singleton_iff.mp hxt
    subst x
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hnew
    obtain ⟨hqP, hyq⟩ := Set.mem_iUnion.mp hq
    obtain ⟨p, rfl⟩ := hPfinite hqP
    have hpE : p.edgeSet ⊆ familyEdges U := by
      intro e he
      exact hPE (Set.mem_iUnion.mpr ⟨Sum.inl p, Set.mem_iUnion.mpr ⟨hqP, he⟩⟩)
    have hpV : p.support ⊆ D.vertexSet U :=
      fun _ hv ↦ hPV ⟨Sum.inl p, hqP, hv⟩
    have hreach := realReach_of_inserted_finitePath p hpV hpE
      (p.edgeSet_subset_support_prod hyq).2
    rcases hroots ⟨Sum.inl p, hqP, rfl⟩ with hsource | hs
    · exact Or.inr (Or.inr ⟨p.start, hsource, hreach⟩)
    · have hps : p.start = s := Set.mem_singleton_iff.mp hs
      exact Or.inr (Or.inl ⟨s, hcut, hps ▸ hreach⟩)

/-- A one-port insertion cannot add an incoming edge at any old vertex. -/
theorem sourcePredecessorRefines_of_onePortInsertion
    {W U : Set D.DPath} {P : Set Gamma.DPath} {s : V}
    (hP : Gamma.IsWarp P) (hsP : s ∈ Gamma.initialSet P)
    (hcap : Gamma.vertexSet P ∩ D.vertexSet W ⊆ {s})
    (hUE : familyEdges U ⊆ familyEdges W ∪ familyEdges P) :
    SourcePredecessorRefines Gamma D W U := by
  intro x y hx hyx
  rcases hUE hyx with hold | hnew
  · exact Or.inl hold
  have hxs : x = s := Set.mem_singleton_iff.mp
    (hcap ⟨(familyEdges_subset_vertexSet_prod P hnew).2, hx⟩)
  rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hP] at hsP
  exact False.elim (hsP.2 ⟨y, hxs ▸ hnew⟩)

/-- The exact edge and carrier equations of the native two-port splice
discharge all relation-inclusion premises of predecessor refinement. -/
theorem sourcePredecessorRefines_of_twoPortSplice
    {W U : Set D.DPath} {P : Set Gamma.DPath} {s t : V}
    (hP : Gamma.IsWarp P) (hPfinite : Gamma.HasFiniteCharacter P)
    (hsP : s ∈ Gamma.initialSet P)
    (hroots : Gamma.initialSet P ⊆ Gamma.source ∪ {s})
    (hcut : (s, t) ∈ familyEdges W)
    (hcap : Gamma.vertexSet P ∩ D.vertexSet W ⊆ {s, t})
    (hUE : familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges P)
    (hUV : D.vertexSet U =
      D.vertexSet W ∪ Gamma.vertexSet P) :
    SourcePredecessorRefines Gamma D W U := by
  apply sourcePredecessorRefines_of_twoPortInsertion hP hPfinite hsP hroots hcut hcap
  · rw [hUE]
    exact Set.union_subset_union_left _ Set.sdiff_subset
  · rw [hUE]
    exact Set.subset_union_right
  · rw [hUV]
    exact Set.subset_union_right

#print axioms SourcePredecessorRefines.trans
#print axioms familyEdges_into_oldVertex_of_edge_initial_extension
#print axioms sourcePredecessorRefines_of_edge_initial_extension
#print axioms sourcePredecessorRefines_of_twoPortInsertion
#print axioms sourcePredecessorRefines_of_onePortInsertion
#print axioms sourcePredecessorRefines_of_twoPortSplice

end Erdos599.ColouredSafeAugmentedRealReach
