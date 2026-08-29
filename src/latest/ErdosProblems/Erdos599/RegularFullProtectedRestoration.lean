/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularJointSafeReplacement

/-!
# Restoring a full protected batch

`SingularProtectedRestoration.restoreProtectedCurrent` restores only the
components whose quotient coordinates are designated as current.  For the
regular construction it is also useful to retain the reserve components:
they are the pending row carried to the next boundary.

The theorem below performs exactly this one ambient restoration.  It does
not identify the protected quotient at the new boundary with a quotient
obtained by deleting the newly completed ambient paths.  That stronger
identity is false in general and is deliberately absent from the result.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularFullProtectedRestoration

open SingularContinuation SingularExtension SingularPendingReentry
  SingularProtectedBatchTransport SingularProtectedRestoration
  SingularQuotientReentry SingularSafeBatch

universe u

variable {V : Type u}

/-- Restore both the current and reserve parts of one protected batch.

The equality `current ∪ reserve = terminalFrontier W` says that the batch
covers every pending component.  The selected original coordinates route to
`current`, so their target links transport back through the frontier star.
The frozen family is protected by `Q`, which supplies the only cross-family
disjointness used in the proof. -/
theorem exists_fullProtectedRestoration
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W : Set G.DPath} {C Q current reserve selected : Set V}
    (hFwarp : G.IsWarp F) (hWwarp : G.IsWarp W)
    (hFfinite : G.HasFiniteCharacter F)
    (hWfinite : G.HasFiniteCharacter W)
    (hFW : Disjoint (G.vertexSet F) (G.vertexSet W))
    (hWroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hFQ : G.vertexSet F ⊆ Q)
    {mu : Cardinal.{u}}
    (hcurrent : current ⊆ ((G.delete Q).quotient C).source)
    (hreserve : reserve ⊆ ((G.delete Q).quotient C).source)
    (hcover : current ∪ reserve = G.terminalFrontier W)
    (hselected : selected ⊆ G.source)
    (hroute : RoutesTerminals G W selected current)
    (B : ProtectedBatch ((G.delete Q).quotient C)
      current reserve mu) :
    ∃ T : Set G.DPath,
      G.IsWarp T ∧
        G.HasFiniteCharacter T ∧
        G.ForwardExtension (F ∪ W) T ∧
        G.initialSet T = G.initialSet (F ∪ W) ∧
        LinksToTarget G T selected ∧
        G.terminalFrontier T ⊆
          G.terminalFrontier F ∪ B.boundary := by
  let U := forgetProtectedBatchFamily B
  let R := deletedQuotientFamily G C Q U
  obtain ⟨hRwarp, hRfinite, hRinitialCover, hRlinks,
      _hRQ, _hnextSource, _hnextCard⟩ :=
    deletedProtectedBatch_quotientPayload B hcurrent hreserve
  have hRinitial : (G.quotient C).initialSet R =
      G.terminalFrontier W := by
    exact hRinitialCover.trans hcover
  have hUstart : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source := by
    rw [(protectedBatch_isLinkageBetween B).initialSet_eq]
    exact Set.union_subset hcurrent hreserve
  have hcross : Disjoint (G.vertexSet F)
      (G.vertexSet (frontierContinuation G hWwarp hWroof htrim
        R hRinitial.le)) := by
    exact disjoint_frozen_frontierContinuation_deletedQuotientFamily
      G hFW hFQ hWwarp hWroof htrim hUstart hRinitial.le
  let T := frozenFrontierContinuation G F hWwarp hWroof htrim
    R hRinitial.le
  have hstruct := frozenFrontierContinuation_structural G
    hFwarp hWwarp hFfinite hWfinite hWroof htrim hRwarp hRfinite
      hRinitial hcross
  have hcurrentTerminal : current ⊆ G.terminalFrontier W := by
    intro x hx
    rw [← hcover]
    exact Or.inl hx
  have hcontinuedLinks : LinksToTarget G
      (frontierContinuation G hWwarp hWroof htrim R hRinitial.le)
      selected := by
    exact linksToTarget_frontierContinuation hNorm hWwarp hWfinite
      hWroof htrim hRwarp hRfinite hRinitial hcurrentTerminal
        hselected hroute hRlinks
  have hTlinks : LinksToTarget G T selected := by
    intro a ha
    obtain ⟨p, hp, q, hpq, hpure, hsuffix⟩ := hcontinuedLinks a ha
    exact ⟨p, Or.inr hp, q, hpq, hpure, hsuffix⟩
  have hRterminal : (G.quotient C).terminalFrontier R ⊆
      B.boundary := by
    rw [deletedQuotientFamily_terminalFrontier]
    exact (protectedBatch_isLinkageBetween B).terminalFrontier_subset
  have hTterminal : G.terminalFrontier T ⊆
      G.terminalFrontier F ∪ B.boundary := by
    exact (terminalFrontier_frozenFrontierContinuation_subset G
      hWwarp hWfinite hWroof htrim hRinitial.le hRinitial.ge).trans
        (Set.union_subset Set.subset_union_left
          (hRterminal.trans Set.subset_union_right))
  exact ⟨T, hstruct.1, hstruct.2.1, hstruct.2.2.1,
    hstruct.2.2.2, hTlinks, hTterminal⟩

end RegularFullProtectedRestoration
end CardinalInduction
end Erdos599
