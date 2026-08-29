/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSelectedFreeze

/-!
# Exact selected-source packaging of the singular three-piece continuation

The geometric continuation theorem links the initials of the selected
pending components.  This file combines it with the selected-row bookkeeping:
selected components which were already complete retain their target links
under forward extension.  Thus the resulting row links every selected source,
not merely the sources which were pending at the old row.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularThreePieceReentry

open SingularExtension SingularPendingDecomposition
open SingularPendingReentry SingularSelectedFreeze
open SingularTargetRowMachine

universe u

variable {V : Type u}

/-- Continue exactly the pending components selected by `B`, freeze every
other old component, and recover target links for all of `B`.  The safety set
only has to cover the completed old components; unselected pending components
are protected by the roof and terminal-clean fields of the split stop-over. -/
theorem exists_threePieceSelectedRowContinuation_of_safety
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {B : Set V} (S : SplitStopover G W)
    (hWwarp : G.IsWarp W)
    (hWfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hB : B ⊆ G.source)
    {Q : Set V}
    (hcompletedQ :
      G.vertexSet (completedPart G W) ⊆ Q)
    (hsafe : DeletedPendingSafety G (selectedRow G W B)
      S.boundary Q mu) :
    ∃ (U : Set (deletedPendingAuxiliaryWeb
        G (selectedRow G W B) S.boundary Q).DPath) (T : Set G.DPath),
      IsHalfwayLinkageOfAltitude
          (deletedPendingAuxiliaryWeb G (selectedRow G W B)
            S.boundary Q)
          (pendingRequests G (selectedRow G W B) S.boundary)
          (altitude (deletedPendingAuxiliaryWeb G (selectedRow G W B)
            S.boundary Q) U) U ∧
      G.IsWarp T ∧
      G.HasFiniteCharacter T ∧
      G.ForwardExtension W T ∧
      G.initialSet T = G.source ∧
      LinksToTarget G T B ∧
      G.terminalFrontier T ⊆
        G.terminalFrontier
            (completedPart G W ∪
              (pendingPart G W \ selectedPending G W B)) ∪
          (G.quotient S.boundary).terminalFrontier
            (deletedQuotientFamily G S.boundary Q
              (forgetDeletedPendingAuxiliaryFamily
                G (selectedRow G W B) S.boundary Q U)) := by
  obtain ⟨U, T, hU, hTwarp, hTfinite, hforward, hTinitial,
      hPending, hfrontier⟩ :=
    exists_threePieceSelectedPendingContinuation_of_safety
      hlower hmu hNorm S (selectedRow_subset G W B) hWwarp hWfinite
        (by simpa only [hinitial] using Set.Subset.rfl)
        hcompletedQ hsafe
  have hlinks : LinksToTarget G T B :=
    linksToTarget_of_selectedPending hNorm hWfinite hTfinite
      hinitial hB hforward (by
        simpa only [selectedPending] using hPending)
  refine ⟨U, T, hU, hTwarp, hTfinite, hforward,
    hTinitial.trans hinitial, hlinks, ?_⟩
  simpa only [selectedPending] using hfrontier

end SingularThreePieceReentry
end CardinalInduction
end Erdos599
