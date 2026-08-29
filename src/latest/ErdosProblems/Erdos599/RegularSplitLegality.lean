/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderSplitProvenance

/-!
# Sound canonical legality for regular assembly

The successor-normalized canonical ladder satisfies `IsSplitLegal`, while
the older `IsLegal` package additionally asks for false strict provenance
of fresh same-stage records.  Regular stage geometry uses only the common
construction fields.  This module supplies the one sound compatibility
direction: a legacy-legal ladder may be used wherever split legality is
requested.  It does not manufacture legacy legality for a canonical split
ladder.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

instance IsLegal.instCoeIsSplitLegal {L : G.KappaLadder kappa} :
    CoeOut L.IsLegal L.IsSplitLegal where
  coe := IsLegal.isSplitLegal

/-- Exact successor arrows extend every old path.  This is the split-legal
counterpart of the legacy compatibility projection and uses no provenance
field. -/
theorem IsSplitLegal.successorExtensions {L : G.KappaLadder kappa}
    (hL : L.IsSplitLegal) (a : Ladder.Stage kappa)
    (p : G.DPath) (hp : p ∈ L.warpAt a) :
    ∃ q ∈ L.successorWarp a, G.Extends p q := by
  obtain ⟨q, hq, _⟩ := (hL.exactSuccessorArrows a).1.1 p hp
  exact ⟨q, hq.1.1, hq.2.extends⟩

/-- Strict roofs of split-legal ladder frontiers are monotone. -/
theorem IsSplitLegal.strictRoof_frontier_mono
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal)
    {a b : Ladder.Stage kappa} (hab : a ≤ b) :
    G.strictRoof (L.frontier a) ⊆ G.strictRoof (L.frontier b) := by
  rcases hab.lt_or_eq with hab | rfl
  · intro x hx
    constructor
    · exact G.roof_cut (hL.frontierChronology hab) hx.1
    · intro hxEssential
      have hxFrontier : x ∈ L.frontier b := by
        rw [← hL.frontiersEssential b]
        exact hxEssential
      exact Set.disjoint_left.1 (hL.strictFrontierChronology hab)
        hx hxFrontier
  · exact fun _ hx ↦ hx

/-- Split-legal form of the eventual-frontier characterization at the
limit roof boundary. -/
theorem IsSplitLegal.mem_limitRoof_diff_limitStrictRoof_iff_eventually_frontier
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal) (v : V) :
    v ∈ L.limitRoof \ L.limitStrictRoof ↔
      ∃ a : Ladder.Stage kappa, ∀ b : Ladder.Stage kappa,
        a ≤ b → v ∈ L.frontier b :=
  L.mem_limitRoof_diff_limitStrictRoof_iff_eventually_frontier
    hL.frontiersEssential hL.frontierChronology
      hL.strictFrontierChronology v

/-- Split-legal form of the corrected club hit-stage closure theorem. -/
theorem hitStages_isClosed_of_splitLegal
    (L : G.KappaLadder kappa) (hL : L.IsSplitLegal)
    (Sigma : Set (Ladder.Stage kappa)) (p : G.DPath)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hprefix : ∀ a ∈ L.hitStages Sigma p,
      ∃ q ∈ G.essentialWarpPart (L.warpAt a),
        (p.support ∩ q.support).Nonempty)
    (hmiss : L.LimitMissIsInessential Sigma p)
    (havoid : Disjoint Sigma L.phi) :
    DirSupClosed (L.hitStages Sigma p) :=
  L.hitStages_isClosed Sigma p hSigma hL.warpStages
    hL.recordedPathsPersist hprefix hmiss
    (fun a hp ↦ hL.currentInessentialPersists a hp) havoid

end KappaLadder
end DWeb
end Erdos599
