/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularExtension
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# Merging newly completed components with an old clean row

In the singular successor step an unrestricted continuation records the
new target witnesses, while a second, restricted continuation supplies the
clean geometric state for the following quotient.  The displayed row can be
made compatible with the clean state by retaining exactly the newly completed
components of the unrestricted continuation and using the clean component at
every other source.  This file proves the elementary, but dependent, warp and
forward-extension bookkeeping for that merge.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularCompletedPendingMerge

open SliceSpliceSource SingularExtension

universe u

variable {V : Type u}

/-- Keep the completed components of `T`; at every source not represented by
one of them, keep the old component of `C`. -/
def completedPendingMerge (G : DWeb V) (C T : Set G.DPath) : Set G.DPath :=
  completedPart G T ∪
    initialRestriction G C (G.source \ G.initialSet (completedPart G T))

/-- Two members of a warp with the same initial vertex are equal. -/
private theorem eq_of_mem_warp_of_initial_eq
    {G : DWeb V} {W : Set G.DPath} (hW : G.IsWarp W)
    {p q : G.DPath} (hp : p ∈ W) (hq : q ∈ W)
    (hinitial : p.initial = q.initial) : p = q := by
  by_contra hpq
  exact Set.disjoint_left.1 (hW hp hq hpq)
    p.initial_mem_support
    (hinitial ▸ q.initial_mem_support)

/-- The merge is a warp.  The only nontrivial case is a completed component
of `T` against an old component of `C`.  Extend the latter into `T`; the two
resulting `T` components have different initial vertices and hence are
disjoint. -/
theorem completedPendingMerge_isWarp
    {G : DWeb V} {C T : Set G.DPath}
    (hC : G.IsWarp C) (hT : G.IsWarp T)
    (hforward : G.ForwardExtension C T) :
    G.IsWarp (completedPendingMerge G C T) := by
  intro p hp q hq hpq
  rcases hp with hpT | hpC
  · rcases hq with hqT | hqC
    · exact hT hpT.1 hqT.1 hpq
    · obtain ⟨q', hq'T, hqq'⟩ := hforward.1 q hqC.1
      have hpq' : p ≠ q' := by
        intro heq
        subst q'
        have hqInitial : q.initial ∈ G.initialSet (completedPart G T) :=
          ⟨p, hpT, (G.extends_initial hqq').symm⟩
        exact hqC.2.2 hqInitial
      exact (hT hpT.1 hq'T hpq').mono_right
        (G.support_mono_of_extends hqq')
  · rcases hq with hqT | hqC
    · obtain ⟨p', hp'T, hpp'⟩ := hforward.1 p hpC.1
      have hp'q : p' ≠ q := by
        intro heq
        subst p'
        have hpInitial : p.initial ∈ G.initialSet (completedPart G T) :=
          ⟨q, hqT, (G.extends_initial hpp').symm⟩
        exact hpC.2.2 hpInitial
      exact (hT hp'T hqT.1 hp'q).mono_left
        (G.support_mono_of_extends hpp')
    · exact hC hpC.1 hqC.1 hpq

/-- The merge has finite character whenever both input rows do. -/
theorem completedPendingMerge_finiteCharacter
    {G : DWeb V} {C T : Set G.DPath}
    (hC : G.HasFiniteCharacter C) (hT : G.HasFiniteCharacter T) :
    G.HasFiniteCharacter (completedPendingMerge G C T) := by
  apply SingularContinuation.finiteCharacter_union G
  · intro p hp
    exact hT hp.1
  · intro p hp
    exact hC hp.1

/-- The merge is a forward extension of the old clean row. -/
theorem forwardExtension_completedPendingMerge
    {G : DWeb V} {C T : Set G.DPath}
    (hT : G.IsWarp T) (hforward : G.ForwardExtension C T)
    (hCsource : G.initialSet C = G.source) :
    G.ForwardExtension C (completedPendingMerge G C T) := by
  constructor
  · intro p hpC
    obtain ⟨q, hqT, hpq⟩ := hforward.1 p hpC
    by_cases hqCompleted : q ∈ completedPart G T
    · exact ⟨q, Or.inl hqCompleted, hpq⟩
    · have hpSource : p.initial ∈ G.source := by
        rw [← hCsource]
        exact ⟨p, hpC, rfl⟩
      have hpNotCompleted : p.initial ∉ G.initialSet (completedPart G T) := by
        rintro ⟨r, hrCompleted, hrInitial⟩
        have hqr : q = r := eq_of_mem_warp_of_initial_eq hT hqT hrCompleted.1
          ((G.extends_initial hpq).symm.trans hrInitial.symm)
        exact hqCompleted (hqr ▸ hrCompleted)
      exact ⟨p, Or.inr ⟨hpC, hpSource, hpNotCompleted⟩,
        G.extends_refl p⟩
  · intro q hqMerge
    rcases hqMerge with hqT | hqC
    · obtain ⟨p, hpC, hpq⟩ := hforward.2 q hqT.1
      exact ⟨p, hpC, hpq⟩
    · exact ⟨q, hqC.1, G.extends_refl q⟩

/-- Consequently a full-source clean row produces a full-source merge. -/
theorem initialSet_completedPendingMerge
    {G : DWeb V} {C T : Set G.DPath}
    (hT : G.IsWarp T) (hforward : G.ForwardExtension C T)
    (hCsource : G.initialSet C = G.source) :
    G.initialSet (completedPendingMerge G C T) = G.source := by
  rw [← hCsource]
  exact (G.initialSet_eq_of_forwardExtension
    (forwardExtension_completedPendingMerge hT hforward hCsource)).symm

/-- In a normalized web all target witnesses in `T` lie in its completed
part, which is included unchanged in the merge. -/
theorem linksToTarget_completedPendingMerge
    {G : DWeb V} (hNorm : G.IsNormalized)
    {C T : Set G.DPath} {B : Set V}
    (hlinks : LinksToTarget G T B) :
    LinksToTarget G (completedPendingMerge G C T) B := by
  intro b hb
  obtain ⟨p, hp, hrest⟩ := linksToTarget_completedPart hNorm hlinks b hb
  exact ⟨p, Or.inl hp, hrest⟩

/-- Every still-pending member of the merge comes from the old clean row. -/
theorem pendingPart_completedPendingMerge_subset
    (G : DWeb V) (C T : Set G.DPath) :
    pendingPart G (completedPendingMerge G C T) ⊆ C := by
  intro p hp
  rcases hp.1 with hpCompleted | hpC
  · exact (hp.2 ⟨Or.inl hpCompleted, hpCompleted.2⟩).elim
  · exact hpC.1

/-- Terminal cleanliness of the old row is inherited by the pending part of
the merge. -/
theorem pendingPart_completedPendingMerge_terminalClean
    {G : DWeb V} {C T : Set G.DPath} {D : Set V}
    (hclean : SingularContinuation.TerminalCleanAt G C D) :
    SingularContinuation.TerminalCleanAt G
      (pendingPart G (completedPendingMerge G C T)) D := by
  intro p hp
  exact hclean p (pendingPart_completedPendingMerge_subset G C T hp)

/-- Bundled form used by the target-row state machine. -/
theorem completedPendingMerge_structural
    {G : DWeb V} (hNorm : G.IsNormalized)
    {C T : Set G.DPath} {B : Set V}
    (hCwarp : G.IsWarp C) (hTwarp : G.IsWarp T)
    (hCfinite : G.HasFiniteCharacter C)
    (hTfinite : G.HasFiniteCharacter T)
    (hCsource : G.initialSet C = G.source)
    (hforward : G.ForwardExtension C T)
    (hlinks : LinksToTarget G T B) :
    G.IsWarp (completedPendingMerge G C T) ∧
      G.HasFiniteCharacter (completedPendingMerge G C T) ∧
      G.ForwardExtension C (completedPendingMerge G C T) ∧
      G.initialSet (completedPendingMerge G C T) = G.source ∧
      LinksToTarget G (completedPendingMerge G C T) B := by
  exact ⟨completedPendingMerge_isWarp hCwarp hTwarp hforward,
    completedPendingMerge_finiteCharacter hCfinite hTfinite,
    forwardExtension_completedPendingMerge hTwarp hforward hCsource,
    initialSet_completedPendingMerge hTwarp hforward hCsource,
    linksToTarget_completedPendingMerge hNorm hlinks⟩

end SingularCompletedPendingMerge
end CardinalInduction
end Erdos599
