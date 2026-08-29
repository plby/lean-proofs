/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularCompletedPendingMerge
import ErdosProblems.Erdos599.SingularTargetRowMachine
import ErdosProblems.Erdos599.SingularPendingReentry

/-!
# Packaging a clean/target pair as the next singular row

The quotient re-entry construction naturally produces two rows.  The clean
row carries the next separating stop-over, while the target row carries the
new target witnesses.  Once the target row is a forward extension of the
clean row, `completedPendingMerge` combines exactly the information needed
by the private singular row machine: newly completed target components are
kept, and every still-pending component remains in the clean row.

This module contains only that final, elementary glue.  In particular it
does not postulate a successor construction and does not hide the difficult
boundary-starting case behind an abstract existence assertion.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularCompletedPendingReentry

open SingularContinuation SingularExtension
  SingularCompletedPendingMerge SingularPendingDecomposition
  SingularTargetRowMachine SliceSpliceSource

universe u

variable {V : Type u}

/-- The terminal frontier of the completed/pending merge is controlled by
the frontiers of its two input rows. -/
theorem terminalFrontier_completedPendingMerge_subset
    {G : DWeb V} {C T : Set G.DPath} {E : Set V}
    (hCterminal : G.terminalFrontier C ⊆ E)
    (hTterminal : G.terminalFrontier T ⊆ E) :
    G.terminalFrontier (completedPendingMerge G C T) ⊆ E := by
  rintro x ⟨p, hp, hpx⟩
  rcases hp with hpT | hpC
  · exact hTterminal ⟨p, hpT.1, hpx⟩
  · exact hCterminal ⟨p, hpC.1, hpx⟩

/-- A clean separating stop-over for `C` induces the split stop-over needed
for the merged displayed row.  No cleanliness is asserted for the completed
target components; the pending part is clean because it is contained in
`C`. -/
noncomputable def splitStopover_completedPendingMerge
    {G : DWeb V} {C T : Set G.DPath} {E : Set V}
    (hC : IsSeparatingHalfwayStopover G C E)
    (hCclean : TerminalCleanAt G C E)
    (hTterminal : G.terminalFrontier T ⊆ E) :
    SplitStopover G (completedPendingMerge G C T) where
  boundary := E
  separator := hC.separator
  minimal := hC.stopover.minimal
  quotient_unhindered := hC.quotient_unhindered
  terminal_subset :=
    terminalFrontier_completedPendingMerge_subset
      hC.linkage.terminalFrontier_subset hTterminal
  clean_pending_roof := by
    have hCroofs : G.vertexSet C ⊆ G.roof E :=
      linkage_vertexSet_subset_roof G hC.linkage hC.separator hCclean
    rintro x ⟨p, hp, hxp⟩
    apply hCroofs
    exact ⟨p, pendingPart_completedPendingMerge_subset G C T hp.1, hxp⟩
  clean_pending_terminalClean := by
    intro p hp
    apply hCclean p
    exact pendingPart_completedPendingMerge_subset G C T hp.1
  boundary_pending_trivial := by
    intro p hp
    exact
      SingularPendingReentry.boundaryPendingPart_completedPendingMerge_eq_trivialPath
        hC.linkage.finiteCharacter hCclean hp

/-- Full successor package used after a clean quotient re-entry and an
unrestricted target continuation have been compared.  The old row is
forward-extended through the clean row and then through the merge. -/
theorem completedPendingMerge_successor
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W C T : Set G.DPath} {E B : Set V}
    (hWC : G.ForwardExtension W C)
    (hC : IsSeparatingHalfwayStopover G C E)
    (hCclean : TerminalCleanAt G C E)
    (hTwarp : G.IsWarp T)
    (hTfinite : G.HasFiniteCharacter T)
    (hCT : G.ForwardExtension C T)
    (hTterminal : G.terminalFrontier T ⊆ E)
    (hTlinks : LinksToTarget G T B) :
    let M := completedPendingMerge G C T
    G.IsWarp M ∧
      G.HasFiniteCharacter M ∧
      G.ForwardExtension W M ∧
      G.initialSet M = G.source ∧
      LinksToTarget G M B ∧
      Nonempty (SplitStopover G M) := by
  dsimp only
  have hstruct := completedPendingMerge_structural hNorm
    hC.linkage.isWarp hTwarp hC.linkage.finiteCharacter hTfinite
    hC.linkage.initialSet_eq hCT hTlinks
  refine ⟨hstruct.1, hstruct.2.1, ?_, hstruct.2.2.2.1,
    hstruct.2.2.2.2, ?_⟩
  · exact G.forwardExtension_trans hWC hstruct.2.2.1
  · exact ⟨splitStopover_completedPendingMerge hC hCclean hTterminal⟩

end SingularCompletedPendingReentry
end CardinalInduction
end Erdos599
