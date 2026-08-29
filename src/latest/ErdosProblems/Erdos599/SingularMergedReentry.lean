/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularCompletedPendingReentry
import ErdosProblems.Erdos599.SingularRestrictedFullComparison

/-!
# The merged singular quotient re-entry step

This is the assumption-free composition used by the singular target-row
machine.  A lower-cardinal half-way row in the quotient produces a
future-safe clean continuation and an unrestricted target continuation.
The former is a forward prefix of the latter, so their completed/pending
merge is simultaneously a target row and an iterable split row.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMergedReentry

open SingularContinuation SingularQuotientReentry
  SingularTargetLinkTransfer SingularCompletedPendingMerge
  SingularCompletedPendingReentry SingularRestrictedFullComparison
  SingularTargetRowMachine

universe u

variable {V : Type u}

/-- A finite full-source row routes every requested ambient source to the
terminal frontier of its own component. -/
theorem routesTerminals_requestedFrontier
    {G : DWeb V} {W : Set G.DPath} {B : Set V}
    (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hB : B ⊆ G.source) :
    RoutesTerminals G W B (SingularBoundarySplit.requestedFrontier G W B) := by
  intro b hb
  have hbInitial : b ∈ G.initialSet W := hinitial.symm ▸ hB hb
  obtain ⟨p, hpW, hpInitial⟩ := hbInitial
  obtain ⟨f, rfl⟩ := hfinite hpW
  refine ⟨f, hpW, hpInitial, ?_⟩
  exact ⟨.inl f, ⟨hpW, hpInitial ▸ hb⟩, rfl⟩

/-- A quotient half-way witness gives one fully packaged singular successor.
There is no abstract successor hypothesis in this statement: both component
rows and their comparison are the concrete constructions from the imported
modules. -/
theorem exists_mergedReentry_of_halfway
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    {A B : Set V} (hA : A ⊆ (G.quotient D).source)
    (hB : B ⊆ G.source)
    (hroute : RoutesTerminals G W B A)
    {kappa : Cardinal.{u}}
    {U : Set (G.quotient D).DPath}
    (hU : IsHalfwayLinkageOfAltitude (G.quotient D) A kappa U) :
    ∃ (E : Set V) (M : Set G.DPath),
      IsSeparatingHalfwayStopover (G.quotient D) U E ∧
      HeightAtMost (G.quotient D) E kappa ∧
      G.IsWarp M ∧
      G.HasFiniteCharacter M ∧
      G.ForwardExtension W M ∧
      G.initialSet M = G.source ∧
      LinksToTarget G M B ∧
      Nonempty (SplitStopover G M) := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  obtain ⟨C₀, hC₀, hheightC₀⟩ := hU.exists_stopover
  obtain ⟨E, hE, hheightE, _hEsub, _hquotient⟩ :=
    exists_quotientSeparatingStopover hNoEnter hC₀ hheightC₀
  let C : Set G.DPath := frozenRestrictedContinuation G hD hclean hE
  let T : Set G.DPath :=
    continuation G hD.linkage hD.separator hD.stopover.minimal
      hclean U hE.linkage.initialSet_eq
  let M : Set G.DPath := completedPendingMerge G C T
  have hCstruct := frozenRestrictedContinuation_structural
    hNorm hD hclean hE
  have hTwarp : G.IsWarp T :=
    continuation_isWarp G hD.linkage hD.separator hD.stopover.minimal
      hclean hE.linkage.isWarp hE.linkage.initialSet_eq
  have hTfinite : G.HasFiniteCharacter T :=
    continuation_finiteCharacter G hD.linkage hD.separator
      hD.stopover.minimal hclean hE.linkage.finiteCharacter
        hE.linkage.initialSet_eq
  have hTlinks : LinksToTarget G T B :=
    linksToTarget_continuation hNorm hD hclean
      hE.linkage.isWarp hE.linkage.finiteCharacter
      hE.linkage.initialSet_eq hA hB hroute hU.2.1
  have hCT : G.ForwardExtension C T :=
    forwardExtension_frozenRestrictedContinuation_continuation
      hD hclean hE
  have hTterminal : G.terminalFrontier T ⊆ E :=
    terminalFrontier_continuation_subset_newStopover hD hclean hE
  have hM := completedPendingMerge_successor hNorm
    hCstruct.2.2.1 hCstruct.1 hCstruct.2.1 hTwarp hTfinite
      hCT hTterminal hTlinks
  exact ⟨E, M, hE, hheightE, hM.1, hM.2.1, hM.2.2.1,
    hM.2.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2⟩

/-- Requested-frontier specialization used by one column of the singular
target-row machine.  The quotient-source and routing hypotheses are derived
from the current separating row. -/
theorem exists_mergedReentry_to_requestedFrontier
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D B : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    (hB : B ⊆ G.source)
    {kappa : Cardinal.{u}}
    {U : Set (G.quotient D).DPath}
    (hU : IsHalfwayLinkageOfAltitude (G.quotient D)
      (SingularBoundarySplit.requestedFrontier G W B) kappa U) :
    ∃ (E : Set V) (M : Set G.DPath),
      IsSeparatingHalfwayStopover (G.quotient D) U E ∧
      HeightAtMost (G.quotient D) E kappa ∧
      G.IsWarp M ∧
      G.HasFiniteCharacter M ∧
      G.ForwardExtension W M ∧
      G.initialSet M = G.source ∧
      LinksToTarget G M B ∧
      Nonempty (SplitStopover G M) := by
  apply exists_mergedReentry_of_halfway
    (A := SingularBoundarySplit.requestedFrontier G W B) (B := B)
    hNorm hD hclean
  · exact SingularTargetRowMachine.requestedFrontier_subset_quotientSource
      (A := B) hD
  · exact hB
  · exact routesTerminals_requestedFrontier
      hD.linkage.finiteCharacter hD.linkage.initialSet_eq hB
  · exact hU

end SingularMergedReentry
end CardinalInduction
end Erdos599
